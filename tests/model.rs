use stn_validator::{FeatureStatus, Type, ValidationOptions, check_proof, validate_source};

#[test]
fn equal_types_share_identifiers_and_nested_nodes() {
    let source = "DEFINITIONS:\nA\nB\nK\nFEATURES:\n\
        canonical: Map<K, List<A | B>> -> Map<K, List<B | (A | B)>>\n\
        nested: List<A | B> -> List<B | A>\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
    let map = &report.features[0];
    let list = &report.features[1];
    assert_eq!(map.input, map.output);
    assert_eq!(list.input, list.output);
    let Type::Map(_, value) = report.types[map.input] else {
        panic!("expected a map node");
    };
    assert_eq!(value, list.input);
    assert_eq!(
        report.types.find(&Type::List(match report.types[value] {
            Type::List(element) => element,
            _ => panic!("expected a list node"),
        })),
        Some(value)
    );
    assert_eq!(
        report.types.display(map.input).to_string(),
        "Map<K, List<A | B>>"
    );
    assert!(
        report
            .features
            .iter()
            .all(|f| matches!(f.status, FeatureStatus::Proved { .. }))
    );
}

#[test]
fn nominal_families_keep_ordered_arguments_and_distinct_identity() {
    let source = "DEFINITIONS:\nA\nB\nKinds = A | B\n\
        Pair<K from Kinds, V from Kinds> = (K, V)\n\
        Other<K from Kinds, V from Kinds> = (K, V)\n\
        FEATURES:\nfirst: Pair<A, B> -> (A, B)\n\
        other: Other<A, B> -> (A, B)\nreverse: Pair<B, A> -> (B, A)\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
    let first = &report.features[0];
    let other = &report.features[1];
    let reverse = &report.features[2];
    assert_ne!(first.input, other.input);
    assert_ne!(first.input, reverse.input);
    assert_eq!(first.output, other.output);
    let Type::Named(_, args) = &report.types[first.input] else {
        panic!("expected nominal node")
    };
    let Type::Product(items) = &report.types[first.output] else {
        panic!("expected product node")
    };
    assert_eq!(args, items);
    assert_eq!(
        report.types.display(reverse.input).to_string(),
        "Pair<B, A>"
    );
}

#[test]
fn external_proof_identifiers_are_translated_between_stores() {
    let source = "DEFINITIONS:\nA\nB\nP = (A, B)\nFEATURES:\npart: P -> A\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof")
    };
    // Introducing an unused body changes allocation order but not the goal's types.
    let reordered = "DEFINITIONS:\nA\nB\nUnused = List<B>\nP = (A, B)\nFEATURES:\npart: P -> A\n";
    let other = validate_source("other", reordered, &ValidationOptions::default()).unwrap();
    assert_ne!(report.features[0].input, other.features[0].input);
    check_proof(reordered, &report.types, &report.proofs, proofs[0]).unwrap();
    // The verifier must use the new declaration's shape, not the imported store's cache.
    let changed = reordered.replace("P = (A, B)", "P = List<B>");
    assert!(check_proof(&changed, &report.types, &report.proofs, proofs[0]).is_err());
}

#[test]
fn external_existential_proof_translates_bound_variables_and_witnesses() {
    let source = "DEFINITIONS:\nA\nB\nKinds = A | B\nColumn<T from Kinds> = List<T>\n\
        FEATURES:\nsame: (exists X from Kinds: Column<X>) -> (exists Y from Kinds: Column<Y>)\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof")
    };
    check_proof(source, &report.types, &report.proofs, proofs[0]).unwrap();
}

#[test]
fn external_proof_import_preserves_nominal_lifts_and_synthesized_sums() {
    let source = "DEFINITIONS:\nA\nB\nDocId\nScore\nE\nF\n\
        MatchedDocs = Set<DocId>\nScores = Set<Score>\n\
        start: A -> MatchedDocs | E\nscore: DocId -> Score\nfinish: Scores -> B | F\n\
        FEATURES:\ngoal: A -> B | E | F\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof");
    };
    for proof in proofs {
        check_proof(source, &report.types, &report.proofs, *proof).unwrap();
    }
}
