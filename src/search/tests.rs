use super::*;
use crate::{Cost, model, syntax::SourceText};
use std::num::NonZeroUsize;

fn specification(source: &str) -> Specification {
    model::elaborate(SourceText::new(source.to_owned()).parse().unwrap()).unwrap()
}

fn named(types: &TypeStore, name: &str) -> TypeId {
    types.find(&Type::Named(name.to_owned(), vec![])).unwrap()
}

fn saturate(relation: &mut ProofRelation<'_>) {
    while relation.propagate().unwrap() {}
}

#[test]
fn a_late_sum_reopens_a_goal_and_propagates_the_cheaper_path_to_its_consumer() {
    let mut spec = specification(
        "DEFINITIONS:\nA\nB\nC\nD\nE\nF\nX\nY\nZ\nDone\n\
        f: A -> B | E\ng: B -> C | F\nh: C -> D\n\
        slow1: A -> X\nslow2: X -> Y\nslow3: Y -> Z\nslow4: Z -> D | E | F\n\
        finish: D | E | F -> Done\nFEATURES:\nresult: A -> D | E | F\nconsumer: A -> Done\n",
    );
    let options = ValidationOptions::default();
    let mut usage = SearchUsage::default();
    let mut budget = Budget {
        options: &options,
        usage: &mut usage,
    };
    let universe = IncrementalUniverse::new(
        &spec.primitives,
        &spec.features,
        &mut spec.types,
        spec.tuple_arity,
        &mut budget,
    )
    .unwrap();
    let late = spec.types.union(
        ["C", "E", "F"]
            .map(|name| named(&spec.types, name))
            .to_vec(),
    );
    assert!(!universe.members.contains(&late));
    let goals = spec
        .features
        .iter()
        .map(|f| (f.input, f.output))
        .collect::<Vec<_>>();
    let mut proofs = ProofStore::default();
    let mut relation = ProofRelation::new(&mut spec.types, &mut proofs, budget);
    relation
        .activate(&universe.members.iter().copied().collect::<Vec<_>>())
        .unwrap();
    relation.seed_primitives(&spec.primitives).unwrap();
    saturate(&mut relation);
    assert_eq!(
        relation.cost(goals[0]),
        Some(Cost {
            functions: 3,
            rules: 7
        })
    );
    assert_eq!(
        relation.cost(goals[1]),
        Some(Cost {
            functions: 4,
            rules: 8
        })
    );
    relation.activate(&[late]).unwrap();
    saturate(&mut relation);
    assert_eq!(
        relation.cost(goals[0]),
        Some(Cost {
            functions: 3,
            rules: 4
        })
    );
    assert_eq!(
        relation.cost(goals[1]),
        Some(Cost {
            functions: 4,
            rules: 5
        })
    );
    relation
        .check_features(&spec.primitives, &spec.features)
        .unwrap();
}

#[test]
fn late_products_and_collection_rules_use_premises_that_already_propagated() {
    let mut spec =
        specification("DEFINITIONS:\nA\nB\nC\nf: A -> B\ng: A -> C\nFEATURES:\ngoal: A -> C\n");
    let (a, b, c) = (
        named(&spec.types, "A"),
        named(&spec.types, "B"),
        named(&spec.types, "C"),
    );
    let options = ValidationOptions::default();
    let mut usage = SearchUsage::default();
    let mut proofs = ProofStore::default();
    let budget = Budget {
        options: &options,
        usage: &mut usage,
    };
    let mut relation = ProofRelation::new(&mut spec.types, &mut proofs, budget);
    relation.activate(&[a, b, c]).unwrap();
    relation.seed_primitives(&spec.primitives).unwrap();
    saturate(&mut relation);
    let pair = relation.types.intern(Type::Product(vec![b, c]));
    let from = relation.types.intern(Type::Set(a));
    let to = relation.types.intern(Type::Set(b));
    relation.activate(&[pair, from, to]).unwrap();
    saturate(&mut relation);
    assert_eq!(
        relation.cost((a, pair)),
        Some(Cost {
            functions: 2,
            rules: 1
        })
    );
    assert_eq!(
        relation.cost((from, to)),
        Some(Cost {
            functions: 1,
            rules: 1
        })
    );
}

#[test]
fn reopening_compares_both_cost_components() {
    for (late, expected) in [
        ("h: N -> C", Cost {
            functions: 2,
            rules: 1,
        }),
        ("h: A -> C", Cost {
            functions: 1,
            rules: 0,
        }),
    ] {
        let mut spec = specification(&format!(
            "DEFINITIONS:\nA\nB\nC\nN = B\nf: A -> N\ng: B -> C\n{late}\nFEATURES:\ngoal: A -> C\n",
        ));
        let options = ValidationOptions {
            max_proofs: NonZeroUsize::new(1).unwrap(),
            ..ValidationOptions::default()
        };
        let mut usage = SearchUsage::default();
        let mut budget = Budget {
            options: &options,
            usage: &mut usage,
        };
        let universe = IncrementalUniverse::new(
            &spec.primitives,
            &spec.features,
            &mut spec.types,
            spec.tuple_arity,
            &mut budget,
        )
        .unwrap();
        let goal = (spec.features[0].input, spec.features[0].output);
        let mut proofs = ProofStore::default();
        let mut relation = ProofRelation::new(&mut spec.types, &mut proofs, budget);
        relation
            .activate(&universe.members.iter().copied().collect::<Vec<_>>())
            .unwrap();
        relation.seed_primitives(&spec.primitives[..2]).unwrap();
        saturate(&mut relation);
        assert_eq!(
            relation.cost(goal),
            Some(Cost {
                functions: 2,
                rules: 3
            })
        );
        relation.seed_primitives(&spec.primitives).unwrap();
        saturate(&mut relation);
        assert_eq!(relation.cost(goal), Some(expected));
        relation
            .check_features(&spec.primitives, &spec.features)
            .unwrap();
    }
}
#[test]
fn hmax_accounts_for_a_shared_product_producer_and_falls_back_for_unsupported_rules() {
    for (extra, expected) in [
        ("", Cost {
            functions: 2,
            rules: 1,
        }),
        ("escape: List<A> -> F", Cost {
            functions: 0,
            rules: 1,
        }),
    ] {
        let mut spec = specification(&format!(
            "DEFINITIONS:\nA\nB\nC\nF\nmake: A -> (B, C)\nfinish: (B, C) -> F\n{extra}\nFEATURES:\ngoal: A -> F\n"
        ));
        let options = ValidationOptions::default();
        let mut usage = SearchUsage::default();
        let mut budget = Budget {
            options: &options,
            usage: &mut usage,
        };
        let universe = IncrementalUniverse::new(
            &spec.primitives,
            &spec.features,
            &mut spec.types,
            spec.tuple_arity,
            &mut budget,
        )
        .unwrap();
        let goal = (spec.features[0].input, spec.features[0].output);
        let bounds = bounds::lower_bounds(
            &[goal],
            &universe.members,
            &spec.primitives,
            &spec.types,
            &mut budget,
        )
        .unwrap();
        assert_eq!(bounds[&goal], expected);
    }
}

#[test]
fn an_identity_certificate_can_finish_before_exhaustive_generation_exceeds_capacity() {
    let report = crate::validate_source(
        "input",
        "DEFINITIONS:\nA\nB\nC\nFEATURES:\ngoal: A -> A\n".to_owned(),
        ValidationOptions {
            exhaustive: true,
            max_depth: 2,
            max_types: NonZeroUsize::new(3).unwrap(),
            max_proofs: NonZeroUsize::new(1).unwrap(),
            ..ValidationOptions::default()
        },
    )
    .unwrap();
    assert!(!report.has_unresolved_features(), "{report}");
    assert_eq!(report.usage.types, 3); // Even the exhaustive unit seed was unnecessary.
}

#[test]
fn the_architecture_example_finishes_under_the_default_budget_with_the_same_minima() {
    let report = crate::validate_source(
        "design",
        include_str!("../../examples/proof-search-incremental.stypes").to_owned(),
        ValidationOptions::default(),
    )
    .unwrap();
    assert!(!report.has_unresolved_features(), "{report}");
    for (feature, (functions, rules)) in report.features.iter().zip([(3, 4), (2, 2), (5, 7)]) {
        let FeatureStatus::Proved { proofs } = &feature.status else {
            unreachable!()
        };
        assert!(
            proofs
                .iter()
                .all(|p| report.proofs[*p].cost == Cost { functions, rules })
        );
    }
}
