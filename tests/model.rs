use stn_validator::{FeatureStatus, Type, ValidationOptions, validate_source};

#[test]
fn equal_types_share_identifiers_and_nested_nodes() {
    let source = "DEFINITIONS:\nA\nB\nK\nFEATURES:\n\
        canonical: Map<K, List<A | B>> -> Map<K, List<B | (A | B)>>\n\
        nested: List<A | B> -> List<B | A>\n";
    let report = validate_source("input", source.to_owned(), ValidationOptions::default()).unwrap();
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
    let report = validate_source("input", source.to_owned(), ValidationOptions::default()).unwrap();
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
