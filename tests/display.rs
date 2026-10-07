use stn_validator::{
    FeatureStatus, ProofNode, ValidationOptions, ValidationReport, validate_source,
};

fn validate(definitions: &str, features: &str) -> ValidationReport {
    let report = validate_source(
        "display.stypes",
        format!("DEFINITIONS:\n{definitions}\nFEATURES:\n{features}\n"),
        ValidationOptions::default(),
    )
    .unwrap();
    assert!(!report.has_unresolved_features(), "{report}");
    report
}

fn expressions(report: &ValidationReport, feature: usize) -> Vec<String> {
    let FeatureStatus::Proved { proofs } = &report.features[feature].status else {
        panic!("expected a proved feature");
    };
    proofs
        .iter()
        .map(|&id| report.proofs.expression(id))
        .collect()
}

#[test]
fn composition_associations_retain_one_checked_witness() {
    let report = validate(
        "A\nB\nC\nD\nf: A -> B\ng: B -> C\nh: C -> D",
        "goal: A -> D",
    );
    assert_eq!(expressions(&report, 0), ["f >>> g >>> h"]);
    let text = report.to_string();
    assert!(text.contains("PROVED (1 minimum-cost witness(es)"));
    assert!(text.contains("cost: functions=3, rules=2"));
    assert_eq!(text.matches("goal = f >>> g >>> h").count(), 1);
    assert!(!text.contains("alternative"));
}

#[test]
fn different_compositions_remain_separate_alternatives() {
    let report = validate(
        "A\nB\nC\nD\nf: A -> B\ng: B -> D\nh: A -> C\ni: C -> D",
        "goal: A -> D",
    );
    let text = report.to_string();
    assert!(text.contains("goal = f >>> g"));
    assert!(text.contains("goal = h >>> i"));
    assert!(text.contains("alternative 1 (1 witness(es))"));
    assert!(text.contains("alternative 2 (1 witness(es))"));
}

#[test]
fn mixed_operators_and_nested_fanouts_preserve_grouping() {
    for (definitions, feature, expected) in [
        (
            "A\nB\nC\nD\nf: A -> B\ng: B -> C\nh: B -> D",
            "goal: A -> (C, D)",
            "f >>> (g &&& h)",
        ),
        (
            "A\nB\nC\nD\nf: A -> B\ng: B -> C\nh: A -> D",
            "goal: A -> (C, D)",
            "(f >>> g) &&& h",
        ),
        (
            "A\nB\nC\nD\nf: A -> B\ng: B -> C\nh: A -> D",
            "goal: A -> (D, C)",
            "h &&& (f >>> g)",
        ),
        (
            "A\nB\nC\nD\nf: A -> B\ng: A -> C\nh: A -> D",
            "goal: A -> ((B, C), D)",
            "(f &&& g) &&& h",
        ),
        (
            "A\nB\nC\nD\nf: A -> B\ng: A -> C\nh: A -> D",
            "goal: A -> (B, (C, D))",
            "f &&& (g &&& h)",
        ),
    ] {
        let report = validate(definitions, feature);
        assert_eq!(expressions(&report, 0), [expected]);
    }
}

#[test]
fn safe_extensions_share_one_witness_and_collection_lifts_keep_their_scope() {
    let report = validate(
        "A\nB\nC\nError\nf: A -> B | Error\ng: B -> C",
        "extended: A | Error -> C | Error",
    );
    let extended = expressions(&report, 0);
    assert_eq!(extended, ["extend(f) >>> extend(g)"]);
    let report = validate(
        "A\nB\nC\nf: A -> B\ng: B -> C",
        "lifted: List<A> -> List<C>",
    );
    assert_eq!(expressions(&report, 0), ["mapList(f >>> g)"]);
}

#[test]
fn structural_steps_remain_visible_without_type_annotations() {
    let report = validate(
        "A\nB\nPair = (A, B)",
        "identity: A -> A\nview: Pair -> (A, B)\nproject: (A, B) -> B\n\
         list: List<A | B> -> List<A>\nset: Set<A | B> -> Set<A>\n\
         keys: Map<A | B, A> -> Map<A, A>",
    );
    for (index, expected) in [
        "id",
        "view",
        "project[2]",
        "narrowList",
        "narrowSet",
        "narrowKeys",
    ]
    .into_iter()
    .enumerate()
    {
        assert_eq!(expressions(&report, index), [expected]);
    }
    assert!(!report.to_string().contains(" -> "));
}

#[test]
fn generic_metadata_is_omitted_from_expressions_but_retained_in_evidence() {
    let report = validate(
        "A\nB\nKinds = A | B\nWrapped<T from Kinds>\n\
         /// Preserve the original value.\nwrap<T from Kinds>: T -> Wrapped<T>",
        "goal<T from Kinds>: T -> Wrapped<T>",
    );
    for feature in &report.features {
        let FeatureStatus::Proved { proofs } = &feature.status else {
            unreachable!();
        };
        assert_eq!(report.proofs.expression(proofs[0]), "wrap");
        let ProofNode::Primitive {
            line,
            description,
            substitutions,
            ..
        } = &report.proofs[proofs[0]].node
        else {
            panic!("expected the specialized primitive");
        };
        assert_eq!(*line, 7);
        assert_eq!(description, "Preserve the original value.");
        assert_eq!(substitutions.len(), 1);
        assert_eq!(substitutions["T"], feature.input);
    }
    let text = report.to_string();
    assert!(text.contains("goal<T=A> = wrap"));
    assert!(text.contains("goal<T=B> = wrap"));
}

#[test]
fn long_pipeline_definitions_break_between_outer_steps() {
    let report = validate(
        "A\nB\nC\nD\n\
         firstLongOperationNameForFormatting: A -> B\n\
         secondLongOperationNameForFormatting: B -> C\n\
         thirdLongOperationNameForFormatting: C -> D",
        "goal: A -> D",
    );
    assert!(report.to_string().contains(concat!(
        "  goal =\n",
        "      firstLongOperationNameForFormatting\n",
        "      >>> secondLongOperationNameForFormatting\n",
        "      >>> thirdLongOperationNameForFormatting\n",
    )));
}

#[test]
fn unresolved_goals_keep_their_types_in_diagnostics() {
    let report = validate_source(
        "display.stypes",
        "DEFINITIONS:\nA\nB\nFEATURES:\ngoal: A -> B\n".to_owned(),
        ValidationOptions::default(),
    )
    .unwrap();
    let text = report.to_string();
    assert!(text.contains("goal: A -> B"));
    assert!(text.contains("UNRESOLVABLE_IN_RELEVANT_UNIVERSE"));
    assert!(!text.contains("goal ="));
}
