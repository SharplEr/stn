//! Proof tests and independent witness translation, compiled only under `cfg(test)`.
use super::{Proof, ProofId};
use crate::{
    Cost, FeatureStatus, ProofNode, ProofStore, Rule, Type, TypeId, TypeStore, ValidationError,
    ValidationOptions, model, syntax, validate_source,
};
use std::collections::{HashMap, HashSet};

#[test]
fn shared_proof_cost_overflow_is_reported_without_unfolding_the_dag() {
    let mut report = validate_source(
        "input",
        "DEFINITIONS:\nFEATURES:\nsame: () -> ()\n".to_owned(),
        &ValidationOptions::default(),
    )
    .unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected identity proof");
    };
    let mut root = proofs[0];
    // Every level doubles the logical tree while adding only one stored proof.
    // All nodes before the final level have representable, correct costs.
    for _ in 0..usize::BITS {
        let previous = &report.proofs[root];
        let output = report.types.intern(Type::Product(vec![previous.output; 2]));
        let proof = Proof {
            input: previous.input,
            output,
            cost: Cost {
                functions: 0,
                rules: previous.cost.rules.saturating_mul(2).saturating_add(1),
            },
            node: ProofNode::Inference {
                rule: Rule::Fanout,
                children: vec![root; 2],
            },
        };
        root = report.proofs.insert(proof);
    }
    assert_eq!(
        report
            .proofs
            .check_against(root, &[], &report.types)
            .unwrap_err(),
        "proof cost overflow",
    );
}

impl ProofStore {
    /// Number of proof records owned by the store.
    fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Test-only verification of an external or edited witness against a specification.
    /// `root` belongs to this store, and `types` owns its type identifiers. Parse
    /// and elaborate the source independently, then translate the witness into
    /// separate stores before checking its rules, source metadata, and costs.
    /// This establishes validity, not minimum cost or compliance with search bounds.
    fn check(
        &self,
        root: ProofId,
        source: String,
        types: &TypeStore,
    ) -> Result<(), ValidationError> {
        let document = syntax::SourceText::new(source).parse()?;
        let mut specification = model::elaborate(&document)?;
        let mut imported = Self::default();
        let root = imported
            .import(root, self, types, &mut specification.types)
            .map_err(ValidationError::Invalid)?;
        imported
            .check_against(root, &specification.primitives, &specification.types)
            .map_err(ValidationError::Invalid)
    }

    /// Import a witness from another store, translating all proof and type identifiers.
    /// `root` belongs to `source`; the returned identifier belongs to this store.
    /// Memoization preserves shared premises and visiting marks reject malformed cycles.
    fn import(
        &mut self,
        root: ProofId,
        source: &Self,
        source_types: &TypeStore,
        target_types: &mut TypeStore,
    ) -> Result<ProofId, String> {
        ProofImporter {
            source_types,
            source_proofs: source,
            target_types,
            target_proofs: self,
            types: HashMap::new(),
            proofs: HashMap::new(),
            visiting: HashSet::new(),
        }
        .visit(root)
    }
}

/// Translation state for one external witness and all its reachable premises.
struct ProofImporter<'a> {
    /// Source type graph owning every endpoint and substitution identifier.
    source_types: &'a TypeStore,
    /// Source proof graph owning the input witness and its children.
    source_proofs: &'a ProofStore,
    /// Independently elaborated target graph used by the verifier.
    target_types: &'a mut TypeStore,
    /// Translated proof records, inserted after their children.
    target_proofs: &'a mut ProofStore,
    /// Translation of source type identifiers, computed at most once per node.
    types: HashMap<TypeId, TypeId>,
    /// Translation of source proof identifiers, preserving DAG sharing.
    proofs: HashMap<ProofId, ProofId>,
    /// Nodes currently being translated, used to detect cycles.
    visiting: HashSet<ProofId>,
}
impl ProofImporter<'_> {
    /// Translate children before inserting their parent, memoizing both type
    /// and proof identifiers. Reject missing source nodes and back edges.
    fn visit(&mut self, id: ProofId) -> Result<ProofId, String> {
        if let Some(&local) = self.proofs.get(&id) {
            return Ok(local);
        }
        if !self.visiting.insert(id) {
            return Err("proof contains a cycle".into());
        }
        let p = self
            .source_proofs
            .get(id)
            .ok_or("proof contains an invalid proof identifier")?;
        let input = self
            .target_types
            .import(self.source_types, p.input, &mut self.types)?;
        let output = self
            .target_types
            .import(self.source_types, p.output, &mut self.types)?;
        let node = match &p.node {
            ProofNode::Primitive {
                id,
                name,
                line,
                description,
                substitutions,
            } => ProofNode::Primitive {
                id: *id,
                name: name.clone(),
                line: *line,
                description: description.clone(),
                substitutions: substitutions
                    .iter()
                    .map(|(n, t)| {
                        Ok((
                            n.clone(),
                            self.target_types
                                .import(self.source_types, *t, &mut self.types)?,
                        ))
                    })
                    .collect::<Result<_, String>>()?,
            },
            ProofNode::Inference { rule, children } => ProofNode::Inference {
                rule: *rule,
                children: children
                    .iter()
                    .map(|c| self.visit(*c))
                    .collect::<Result<_, _>>()?,
            },
        };
        let local = self.target_proofs.insert(Proof {
            input,
            output,
            cost: p.cost,
            node,
        });
        self.visiting.remove(&id);
        self.proofs.insert(id, local);
        Ok(local)
    }
}

#[test]
fn shared_premises_count_each_occurrence_without_copying_nodes() {
    let source = "DEFINITIONS:\nA\nFEATURES:\nrepeat: A -> (A, A)\n";
    let report =
        validate_source("input", source.to_owned(), &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof");
    };
    let root = proofs[0];
    let proof = &report.proofs[root];
    let ProofNode::Inference {
        rule: Rule::Fanout,
        children,
    } = &proof.node
    else {
        panic!("expected fanout");
    };
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], children[1]);
    assert_eq!(report.proofs.len(), 2);
    assert_eq!(proof.cost, Cost {
        functions: 0,
        rules: 3
    });
    assert_eq!(report.proofs.find(proof), Some(root));
    report
        .proofs
        .check(root, source.to_owned(), &report.types)
        .unwrap();
}

#[test]
fn compaction_retains_multiple_roots_and_reuses_identical_feature_proofs() {
    let source = "DEFINITIONS:\nA\nB\nUnused\nUnusedPair = (A, Unused)\n\
        FEATURES:\nfirst: A -> A\nsecond: B -> B\nagain: A -> A\n";
    let report =
        validate_source("input", source.to_owned(), &ValidationOptions::default()).unwrap();
    let roots = report
        .features
        .iter()
        .map(|f| match &f.status {
            FeatureStatus::Proved { proofs } => proofs[0],
            _ => panic!("expected proof"),
        })
        .collect::<Vec<_>>();
    assert_eq!(report.proofs.len(), 2);
    assert_eq!(roots[0], roots[2]);
    assert_ne!(roots[0], roots[1]);
    for root in roots {
        report
            .proofs
            .check(root, source.to_owned(), &report.types)
            .unwrap();
    }
}

#[test]
fn external_checker_rejects_cyclic_and_missing_premises() {
    let source = "DEFINITIONS:\nA\nFEATURES:\nrepeat: A -> (A, A)\n";
    let report =
        validate_source("input", source.to_owned(), &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof");
    };
    // Deliberately misuse foreign indices to construct malformed external records.
    // The original fanout's first child is at zero; in an empty store it becomes
    // the inserted parent itself, so importing it must detect the cycle.
    let mut cyclic = ProofStore::default();
    let cycle = cyclic.insert(report.proofs[proofs[0]].clone());
    let error = cyclic
        .check(cycle, source.to_owned(), &report.types)
        .unwrap_err();
    assert!(error.to_string().contains("cycle"));

    let mut wrong_child = report.proofs[proofs[0]].clone();
    wrong_child.node = ProofNode::Inference {
        rule: Rule::Compose,
        children: vec![proofs[0]],
    };
    let mut missing = ProofStore::default();
    let root = missing.insert(wrong_child);
    let error = missing
        .check(root, source.to_owned(), &report.types)
        .unwrap_err();
    assert!(error.to_string().contains("invalid proof identifier"));
}

#[test]
fn external_proof_identifiers_are_translated_between_stores() {
    let source = "DEFINITIONS:\nA\nB\nP = (A, B)\nFEATURES:\npart: P -> A\n";
    let report =
        validate_source("input", source.to_owned(), &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof")
    };
    // Introducing an unused body changes allocation order but not the goal's types.
    let reordered = "DEFINITIONS:\nA\nB\nUnused = List<B>\nP = (A, B)\nFEATURES:\npart: P -> A\n";
    let other =
        validate_source("other", reordered.to_owned(), &ValidationOptions::default()).unwrap();
    assert_ne!(report.features[0].input, other.features[0].input);
    report
        .proofs
        .check(proofs[0], reordered.to_owned(), &report.types)
        .unwrap();
    // The verifier must use the new declaration's shape, not the imported store's cache.
    let changed = reordered.replace("P = (A, B)", "P = List<B>");
    assert!(
        report
            .proofs
            .check(proofs[0], changed, &report.types)
            .is_err()
    );
}

#[test]
fn external_existential_proof_translates_bound_variables_and_witnesses() {
    let source = "DEFINITIONS:\nA\nB\nKinds = A | B\nColumn<T from Kinds> = List<T>\n\
        FEATURES:\nsame: (exists X from Kinds: Column<X>) -> (exists Y from Kinds: Column<Y>)\n";
    let report =
        validate_source("input", source.to_owned(), &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof")
    };
    report
        .proofs
        .check(proofs[0], source.to_owned(), &report.types)
        .unwrap();
}

#[test]
fn external_proof_import_preserves_nominal_lifts_and_synthesized_sums() {
    let source = "DEFINITIONS:\nA\nB\nDocId\nScore\nE\nF\n\
        MatchedDocs = Set<DocId>\nScores = Set<Score>\n\
        start: A -> MatchedDocs | E\nscore: DocId -> Score\nfinish: Scores -> B | F\n\
        FEATURES:\ngoal: A -> B | E | F\n";
    let report =
        validate_source("input", source.to_owned(), &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof");
    };
    for proof in proofs {
        report
            .proofs
            .check(*proof, source.to_owned(), &report.types)
            .unwrap();
    }
}

#[test]
fn external_checker_rejects_an_incorrect_cost_and_rule() {
    use crate::{ProofNode, Rule};
    let source = "DEFINITIONS:\nA\nB\nf: A -> B\nFEATURES:\ng: A -> B\n";
    let report =
        validate_source("input", source.to_owned(), &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        unreachable!()
    };
    report
        .proofs
        .check(proofs[0], source.to_owned(), &report.types)
        .unwrap();
    let mut wrong_cost = report.proofs[proofs[0]].clone();
    wrong_cost.cost.functions = 0;
    let mut edited = report.proofs.clone();
    let wrong_cost = edited.insert(wrong_cost);
    assert!(
        edited
            .check(wrong_cost, source.to_owned(), &report.types)
            .is_err()
    );
    let mut wrong_rule = report.proofs[proofs[0]].clone();
    wrong_rule.node = ProofNode::Inference {
        rule: Rule::Identity,
        children: Vec::new(),
    };
    wrong_rule.cost = Cost {
        functions: 0,
        rules: 1,
    };
    let wrong_rule = edited.insert(wrong_rule);
    assert!(
        edited
            .check(wrong_rule, source.to_owned(), &report.types)
            .is_err()
    );
}
