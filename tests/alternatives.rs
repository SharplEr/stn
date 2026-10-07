use std::num::NonZeroUsize;
use stn_validator::{Cost, FeatureStatus, ValidationOptions, ValidationReport, validate_source};

fn validate(source: &str, limit: usize) -> ValidationReport {
    let report = validate_source("input", source.to_owned(), ValidationOptions {
        max_proofs: NonZeroUsize::new(limit).unwrap(),
        ..ValidationOptions::default()
    })
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
fn validator_features_keep_one_representative_with_the_original_minimum_cost() {
    let report = validate(include_str!("../examples/validator-complete.stypes"), 5);
    for (feature, cost) in report.features.iter().zip([
        Cost {
            functions: 4,
            rules: 6,
        },
        Cost {
            functions: 3,
            rules: 3,
        },
    ]) {
        let FeatureStatus::Proved { proofs } = &feature.status else {
            unreachable!();
        };
        assert_eq!(proofs.len(), 1);
        assert_eq!(report.proofs[proofs[0]].cost, cost);
    }
    assert_eq!(expressions(&report, 0), [
        "Args.parse >>> extend(Args.loadInput) >>> extend(validateSource) >>> extend(ValidationReport.format)"
    ]);
}

#[test]
fn repeated_associations_do_not_crowd_another_pipeline_out_of_the_limit() {
    let report = validate(
        "DEFINITIONS:\nA\nB\nC\nD\nE\nF\nG\nH\n\
         a: A -> B\nb: B -> C\nc: C -> D\nd: D -> E\n\
         e: A -> F\nf: F -> G\ng: G -> H\nh: H -> E\n\
         FEATURES:\ngoal: A -> E\n",
        2,
    );
    let alternatives = expressions(&report, 0);
    assert_eq!(alternatives.len(), 2);
    assert!(alternatives.contains(&"a >>> b >>> c >>> d".to_owned()));
    assert!(alternatives.contains(&"e >>> f >>> g >>> h".to_owned()));
}

#[test]
fn an_error_handler_keeps_different_scopes_as_separate_alternatives() {
    let report = validate(
        "DEFINITIONS:\nA\nB\nC\nError\n\
         f: A -> B | Error\ng: B | Error -> C | Error\n\
         FEATURES:\ngoal: A | Error -> C | Error\n",
        2,
    );
    let alternatives = expressions(&report, 0);
    assert_eq!(alternatives.len(), 2);
    assert!(alternatives.contains(&"extend(f >>> g)".to_owned()));
    assert!(alternatives.contains(&"extend(f) >>> g".to_owned()));
}

#[test]
fn projections_with_the_same_function_set_still_have_different_meanings() {
    let report = validate("DEFINITIONS:\nA\nFEATURES:\ngoal: (A, A) -> A\n", 2);
    assert_eq!(expressions(&report, 0), ["project[1]", "project[2]"]);
}

#[test]
fn virtual_normalization_steps_do_not_increase_a_witness_cost() {
    let report = validate(
        "DEFINITIONS:\nA\nB\nC\nError\nf: A -> B\ng: B -> C\n\
         FEATURES:\ngoal: A | Error -> C | Error\n",
        5,
    );
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        unreachable!();
    };
    assert_eq!(proofs.len(), 1);
    assert_eq!(report.proofs[proofs[0]].cost, Cost {
        functions: 2,
        rules: 2
    });
    assert_eq!(expressions(&report, 0), ["extend(f >>> g)"]);
}
