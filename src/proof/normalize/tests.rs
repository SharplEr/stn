use super::*;
use crate::{
    ProofStore,
    model::{self, Primitive},
    syntax,
};

/// Builds and independently checks witnesses before comparing their normal forms.
/// Unlike search, the fixture can retain nonminimum witnesses to exercise the laws.
struct Evidence {
    /// Owning store for both original endpoints and explicit test intermediates.
    types: TypeStore,
    /// Expanded declarations used by the witness checker.
    primitives: Vec<Primitive>,
    /// All test witnesses, including structurally different equivalent trees.
    proofs: ProofStore,
    /// Equivalence keys for those witnesses.
    forms: NormalForms,
}

impl Evidence {
    fn new(definitions: &str) -> Self {
        let document = syntax::SourceText::new(format!("DEFINITIONS:\n{definitions}\nFEATURES:\n"))
            .parse()
            .unwrap();
        let specification = model::elaborate(document).unwrap();
        Self {
            types: specification.types,
            primitives: specification.primitives,
            proofs: ProofStore::default(),
            forms: NormalForms::default(),
        }
    }

    fn ty(&self, name: &str) -> TypeId {
        self.types.find(&Type::Named(name.into(), vec![])).unwrap()
    }

    fn union(&mut self, names: &[&str]) -> TypeId {
        let items = names.iter().map(|name| self.ty(name)).collect();
        self.types.union(items)
    }

    fn primitive(&mut self, name: &str) -> ProofId {
        let (id, primitive) = self
            .primitives
            .iter()
            .enumerate()
            .find(|(_, primitive)| primitive.name == name)
            .unwrap();
        self.insert(Proof::primitive(id, primitive))
    }

    fn insert(&mut self, proof: Proof) -> ProofId {
        let normal = self.forms.candidate(&proof, &self.types);
        assert_eq!(
            self.forms[normal].input,
            Boundary::from_type(proof.input, &self.types)
        );
        assert_eq!(
            self.forms[normal].output,
            Boundary::from_type(proof.output, &self.types)
        );
        let id = self.proofs.insert(proof);
        self.proofs
            .check_against(id, &self.primitives, &self.types)
            .unwrap();
        self.forms.remember(id, normal);
        id
    }

    fn infer(
        &mut self,
        rule: Rule,
        input: TypeId,
        output: TypeId,
        children: Vec<ProofId>,
    ) -> ProofId {
        self.insert(self.proofs.inference(input, output, rule, children))
    }

    fn compose(&mut self, first: ProofId, second: ProofId) -> ProofId {
        self.infer(
            Rule::Compose,
            self.proofs[first].input,
            self.proofs[second].output,
            vec![first, second],
        )
    }

    fn extend(&mut self, input: TypeId, child: ProofId) -> ProofId {
        let carried = self.types.source_variants(input);
        let handled = self.types.handled_variants(self.proofs[child].input);
        let output = self.types.union(
            std::iter::once(self.proofs[child].output)
                .chain(carried.difference(&handled).copied())
                .collect(),
        );
        self.infer(Rule::ExtendSum, input, output, vec![child])
    }

    fn fanout(&mut self, left: ProofId, right: ProofId) -> ProofId {
        let output = self.types.intern(Type::Product(vec![
            self.proofs[left].output,
            self.proofs[right].output,
        ]));
        self.infer(Rule::Fanout, self.proofs[left].input, output, vec![
            left, right,
        ])
    }

    fn key(&self, proof: ProofId) -> NormalId {
        self.forms.witnesses[&proof]
    }
}

#[test]
fn association_normalizes_inside_collection_lifts_without_rewriting_the_witness() {
    let mut e = Evidence::new("A\nB\nC\nD\nf: A -> B\ng: B -> C\nh: C -> D");
    let f = e.primitive("f");
    let g = e.primitive("g");
    let h = e.primitive("h");
    let fg = e.compose(f, g);
    let gh = e.compose(g, h);
    let left = e.compose(fg, h);
    let right = e.compose(f, gh);
    assert_ne!(left, right);
    assert_eq!(e.key(left), e.key(right));
    let input = e.types.intern(Type::List(e.ty("A")));
    let output = e.types.intern(Type::List(e.ty("D")));
    let left_map = e.infer(Rule::MapList, input, output, vec![left]);
    let right_map = e.infer(Rule::MapList, input, output, vec![right]);
    assert_ne!(left_map, right_map);
    assert_eq!(e.key(left_map), e.key(right_map));
    assert_eq!(e.proofs[left_map].cost, e.proofs[right_map].cost);
}

#[test]
fn disjoint_extensions_distribute_with_a_nominal_source_but_keep_original_costs() {
    let mut e = Evidence::new(
        "A\nB\nC\nError\nSource = A | Error\nf: A -> B\ng: B -> C\nuseSource: Source -> A",
    );
    let f = e.primitive("f");
    let g = e.primitive("g");
    let fg = e.compose(f, g);
    let source = e.ty("Source");
    // Normalization uses a virtual B | Error boundary without interning it.
    let before = e.types.find(&Type::Sum(vec![e.ty("B"), e.ty("Error")]));
    let protected = e.extend(source, fg);
    assert_eq!(before, None);
    assert_eq!(
        e.types.find(&Type::Sum(vec![e.ty("B"), e.ty("Error")])),
        None
    );
    let extended_f = e.extend(source, f);
    let extended_g = e.extend(e.proofs[extended_f].output, g);
    let distributed = e.compose(extended_f, extended_g);
    assert_eq!(e.key(protected), e.key(distributed));
    assert_eq!(e.proofs[protected].cost.rules, 2);
    assert_eq!(e.proofs[distributed].cost.rules, 3);
    assert_eq!(e.proofs[protected].input, source);
}

#[test]
fn overlapping_errors_can_distribute_when_the_next_step_already_passes_them() {
    let mut e = Evidence::new("A\nB\nC\nError\nf: A -> B | Error\ng: B -> C");
    let f = e.primitive("f");
    let g = e.primitive("g");
    let extended_g = e.extend(e.proofs[f].output, g);
    let fg = e.compose(f, extended_g);
    let source = e.union(&["A", "Error"]);
    let protected = e.extend(source, fg);
    let extended_f = e.extend(source, f);
    let distributed = e.compose(extended_f, extended_g);
    assert_eq!(e.key(protected), e.key(distributed));
    assert_eq!(e.proofs[protected].cost, e.proofs[distributed].cost);
}

#[test]
fn an_error_handler_must_not_run_on_preexisting_carried_errors() {
    let mut e = Evidence::new("A\nB\nC\nError\nf: A -> B | Error\ng: B | Error -> C | Error");
    let f = e.primitive("f");
    let g = e.primitive("g");
    let source = e.union(&["A", "Error"]);
    let fg = e.compose(f, g);
    let protected = e.extend(source, fg);
    let extended_f = e.extend(source, f);
    let consuming = e.compose(extended_f, g);
    assert_eq!(e.proofs[protected].input, e.proofs[consuming].input);
    assert_eq!(e.proofs[protected].output, e.proofs[consuming].output);
    assert_eq!(e.proofs[protected].cost, e.proofs[consuming].cost);
    assert_ne!(e.key(protected), e.key(consuming));
}

#[test]
fn distribution_checks_every_later_step_in_the_pipeline() {
    let mut e =
        Evidence::new("A\nB\nC\nD\nError\nf: A -> B\ng: B -> C | Error\nh: C | Error -> D | Error");
    let f = e.primitive("f");
    let g = e.primitive("g");
    let h = e.primitive("h");
    let source = e.union(&["A", "Error"]);
    let fg = e.compose(f, g);
    let fgh = e.compose(fg, h);
    let protected = e.extend(source, fgh);
    let extended_fg = e.extend(source, fg);
    let consuming = e.compose(extended_fg, h);
    assert_eq!(e.proofs[protected].output, e.proofs[consuming].output);
    assert_ne!(e.key(protected), e.key(consuming));
}

#[test]
fn a_nominal_sum_wrapper_is_not_an_anonymous_pass_through_branch() {
    let mut e = Evidence::new("A\nB\nC\nN = B | C\nf: A -> N\ng: B -> N");
    let f = e.primitive("f");
    let g = e.primitive("g");
    let inspect_n = e.extend(e.ty("N"), g);
    let fg = e.compose(f, inspect_n);
    let source = e.union(&["A", "N"]);
    let protected = e.extend(source, fg);
    let extended_f = e.extend(source, f);
    let inspecting = e.compose(extended_f, inspect_n);
    assert_eq!(e.proofs[protected].output, e.proofs[inspecting].output);
    assert_eq!(e.proofs[protected].cost, e.proofs[inspecting].cost);
    assert_ne!(e.key(protected), e.key(inspecting));
}

#[test]
fn function_order_repetitions_fanout_order_and_projections_remain_distinct() {
    let mut e = Evidence::new("A\nf: A -> A\ng: A -> A");
    let f = e.primitive("f");
    let g = e.primitive("g");
    let fg = e.compose(f, g);
    let gf = e.compose(g, f);
    let ff = e.compose(f, f);
    assert_ne!(e.key(fg), e.key(gf));
    assert_ne!(e.key(ff), e.key(f));
    let pair_fg = e.fanout(f, g);
    let pair_gf = e.fanout(g, f);
    assert_ne!(e.key(pair_fg), e.key(pair_gf));
    let tuple = e.proofs[pair_fg].output;
    let first = e.infer(Rule::Project(0), tuple, e.ty("A"), vec![]);
    let second = e.infer(Rule::Project(1), tuple, e.ty("A"), vec![]);
    assert_ne!(e.key(first), e.key(second));
}
