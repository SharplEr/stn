use std::num::NonZeroUsize;
use stn_validator::{SearchUsage, ValidationOptions, validate_source};

const SOURCE: &str = "DEFINITIONS:\nA\nFEATURES:\ngoal: A -> A\n";

#[test]
fn usage_covers_the_shared_search_and_is_printed_against_configured_limits() {
    let report = validate_source("input", SOURCE.to_owned(), ValidationOptions {
        max_types: NonZeroUsize::new(4).unwrap(),
        max_steps: NonZeroUsize::new(100).unwrap(),
        ..ValidationOptions::default()
    })
    .unwrap();
    assert!(!report.has_unresolved_features());
    assert_eq!(report.usage.types, 1);
    assert!(report.usage.steps > 0);
    let expected_usage = format!(
        "budget-used: types=1 (25.00%), steps={} ({:.2}%)",
        report.usage.steps, report.usage.steps as f64
    );
    assert!(report.to_string().contains(&expected_usage));

    // Repeating the same goal reuses the shared search rather than charging it twice.
    let repeated = SOURCE.to_owned() + "another: A -> A\n";
    let repeated = validate_source("input", repeated, report.options).unwrap();
    assert_eq!(repeated.usage, report.usage);
}

#[test]
fn an_exact_step_budget_completes_and_one_less_preserves_exhausted_usage() {
    let baseline =
        validate_source("input", SOURCE.to_owned(), ValidationOptions::default()).unwrap();
    let required = baseline.usage.steps;
    assert!(required > 1);
    for (limit, incomplete) in [(required, false), (required - 1, true)] {
        let report = validate_source("input", SOURCE.to_owned(), ValidationOptions {
            max_steps: NonZeroUsize::new(limit).unwrap(),
            ..ValidationOptions::default()
        })
        .unwrap();
        assert_eq!(report.has_incomplete_search(), incomplete);
        assert_eq!(report.usage, SearchUsage {
            types: 1,
            steps: limit
        });
        let expected_usage = format!("steps={limit} (100.00%)");
        assert!(report.to_string().contains(&expected_usage));
    }
}

#[test]
fn universe_construction_keeps_usage_when_it_exhausts_either_resource() {
    let source = "DEFINITIONS:\nA\nB\nf: A -> B\nFEATURES:\ngoal: A -> B\n";
    for (options, expected_types, expected_steps) in [
        (
            ValidationOptions {
                max_types: NonZeroUsize::new(1).unwrap(),
                ..ValidationOptions::default()
            },
            1,
            Some(0),
        ),
        (
            ValidationOptions {
                max_steps: NonZeroUsize::new(1).unwrap(),
                ..ValidationOptions::default()
            },
            2,
            Some(1),
        ),
        (
            ValidationOptions {
                exhaustive: true,
                max_depth: 0,
                max_types: NonZeroUsize::new(3).unwrap(),
                ..ValidationOptions::default()
            },
            3,
            None,
        ),
    ] {
        let report = validate_source("input", source.to_owned(), options).unwrap();
        assert!(report.has_incomplete_search());
        assert_eq!(report.usage.types, expected_types);
        if let Some(steps) = expected_steps {
            assert_eq!(report.usage.steps, steps);
        } else {
            // Lazy exhaustive generation can hit its type cap after other stages ran.
            assert!(report.usage.steps > 0);
            assert!(report.usage.steps < report.options.max_steps.get());
        }
    }
}

#[test]
fn declarations_without_features_do_not_consume_search_resources() {
    let report = validate_source(
        "input",
        "DEFINITIONS:\nA\nFEATURES:\n".to_owned(),
        ValidationOptions::default(),
    )
    .unwrap();
    assert_eq!(report.usage, SearchUsage::default());
    assert!(
        report
            .to_string()
            .contains("budget-used: types=0 (0.00%), steps=0 (0.00%)")
    );
}
