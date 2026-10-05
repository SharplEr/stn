use stn_validator::{Cost, FeatureStatus, ValidationOptions, ValidationReport, validate_source};

fn validate(defs: &str, goals: &str) -> ValidationReport {
    validate_source(
        "input",
        &format!("DEFINITIONS:\n{defs}\nFEATURES:\n{goals}\n"),
        &ValidationOptions::default(),
    )
    .unwrap()
}
fn costs(report: &ValidationReport) -> Vec<Cost> {
    report
        .features
        .iter()
        .map(|f| match &f.status {
            FeatureStatus::Proved { proofs } => {
                assert!(!proofs.is_empty());
                assert!(
                    proofs
                        .iter()
                        .all(|p| report.proofs[*p].cost == report.proofs[proofs[0]].cost)
                );
                report.proofs[proofs[0]].cost
            }
            status => panic!("{}: {status:?}", f.name),
        })
        .collect()
}
fn unresolved(report: &ValidationReport) {
    assert!(
        report
            .features
            .iter()
            .all(|f| matches!(f.status, FeatureStatus::UnresolvableWithinUniverse { .. })),
        "{report}"
    );
}

#[test]
fn composition_returns_only_equal_minima() {
    let report = validate(
        "A\nB\nC\nD\nab: A -> B\nbd: B -> D\nac: A -> C\ncd: C -> D\nlong: B -> C",
        "goal: A -> D",
    );
    assert_eq!(costs(&report), vec![Cost {
        functions: 2,
        rules: 1
    }]);
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        unreachable!()
    };
    assert_eq!(proofs.len(), 2);
    assert_ne!(
        report.proofs.expression(proofs[0], &report.types),
        report.proofs.expression(proofs[1], &report.types)
    );
}

#[test]
fn identity_and_nested_projections() {
    let report = validate("A\nB\nC\nP = (A, (B, C))", "same: A -> A\npart: P -> C");
    assert_eq!(costs(&report), vec![
        Cost {
            functions: 0,
            rules: 1
        },
        Cost {
            functions: 0,
            rules: 3
        }
    ]);
}

#[test]
fn fanout_respects_order_and_allows_repeated_outputs() {
    let report = validate(
        "A\nB\nC\nf: A -> B\ng: A -> C",
        "reverse: A -> (C, B)\nrepeat: A -> (B, B)",
    );
    assert_eq!(costs(&report), vec![
        Cost {
            functions: 2,
            rules: 1
        },
        // f followed by id &&& id calls the user function once. Functions
        // take priority over the number of rules in the simplicity metric.
        Cost {
            functions: 1,
            rules: 4
        },
    ]);
}

#[test]
fn fanout_does_not_flatten_a_tuple_or_construct_a_named_product() {
    let report = validate(
        "A\nB\nC\nf: A -> B\ng: A -> C\nP = (B, C)",
        "flat: A -> (B, C, A)\nnamed: A -> P",
    );
    unresolved(&report);
}

#[test]
fn nominal_views_are_directed_and_identity_cannot_rebrand() {
    let report = validate(
        "A\nN = Set<A>\nM = Set<A>",
        "view: N -> Set<A>\nreverse: Set<A> -> N\nrename: M -> N",
    );
    assert!(matches!(
        report.features[0].status,
        FeatureStatus::Proved { .. }
    ));
    assert!(matches!(
        report.features[1].status,
        FeatureStatus::UnresolvableWithinUniverse { .. }
    ));
    assert!(matches!(
        report.features[2].status,
        FeatureStatus::UnresolvableWithinUniverse { .. }
    ));
}

#[test]
fn nominal_map_changes_the_structure_but_anonymous_input_cannot_gain_a_name() {
    let report = validate(
        "DocId\nScore\nMatchedDocs = Set<DocId>\nScores = Set<Score>\nscore: DocId -> Score",
        "named: MatchedDocs -> Scores\nanonymous: Set<DocId> -> Scores",
    );
    assert_eq!(
        costs(&ValidationReport {
            features: vec![report.features[0].clone()],
            ..report.clone()
        }),
        vec![Cost {
            functions: 1,
            rules: 1
        }]
    );
    assert!(matches!(
        report.features[1].status,
        FeatureStatus::UnresolvableWithinUniverse { .. }
    ));
}

#[test]
fn lifts_collections_and_flatmaps_lists() {
    let report = validate(
        "A\nB\nK\nf: A -> B\ng: A -> List<B>",
        "list: List<A> -> List<B>\nset: Set<A> -> Set<B>\nmap: Map<K, A> -> Map<K, B>\nflat: List<A> -> List<B>",
    );
    assert_eq!(costs(&report), vec![
        Cost {
            functions: 1,
            rules: 1
        };
        4
    ]);
    let FeatureStatus::Proved { proofs } = &report.features[3].status else {
        unreachable!()
    };
    assert!(proofs.iter().any(|p| {
        report
            .proofs
            .expression(*p, &report.types)
            .starts_with("flatMap")
    }));
}

#[test]
fn collection_narrowing_filters_but_scalar_errors_remain() {
    let report = validate(
        "A\nB\nE\nK\nValues = List<A | B>\nOnlyA = List<A>",
        "list: List<A | B> -> List<A>\nset: Set<A | B> -> Set<A>\nkeys: Map<A | B, K> -> Map<A, K>\nnominal: Values -> OnlyA\nscalar: A | E -> A",
    );
    let proved = ValidationReport {
        features: report.features[..4].to_vec(),
        ..report.clone()
    };
    assert_eq!(costs(&proved), vec![
        Cost {
            functions: 0,
            rules: 1
        };
        4
    ]);
    assert!(matches!(
        report.features[4].status,
        FeatureStatus::UnresolvableWithinUniverse { .. }
    ));
}

#[test]
fn sum_extension_propagates_multiple_errors_at_intermediate_steps() {
    let report = validate(
        "A\nB\nC\nD\nE\nF\ntryB: A -> B | E\nuseB: B -> C | F\nuseC: C -> D",
        "goal: A -> D | E | F\ndrop: A -> D",
    );
    assert_eq!(
        costs(&ValidationReport {
            features: vec![report.features[0].clone()],
            ..report.clone()
        }),
        vec![Cost {
            functions: 3,
            rules: 4
        }]
    );
    assert!(matches!(
        report.features[1].status,
        FeatureStatus::UnresolvableWithinUniverse { .. }
    ));
}

#[test]
fn extends_nominal_sum_and_multivariant_function_domains() {
    let report = validate(
        "A\nB\nC\nD\nE\nS = A | B | E\nf: A | B -> C | D",
        "goal: S -> C | D | E",
    );
    assert_eq!(costs(&report), vec![Cost {
        functions: 1,
        rules: 1
    }]);
}

#[test]
fn input_restriction_matches_tuple_components() {
    let report = validate("A\nB\nC\nK\nf: (A | B, K) -> C", "goal: (A, K) -> C");
    assert_eq!(costs(&report), vec![Cost {
        functions: 1,
        rules: 1
    }]);
}

#[test]
fn overloads_with_intersections_are_rejected_even_for_equal_outputs() {
    for defs in [
        "A\nB\nf: A -> B\nf: A | B -> B",
        "A\nB\nK\nf: (A | B, K) -> A\nf: (A, K) -> A",
    ] {
        let error = validate_source(
            "input",
            &format!("DEFINITIONS:\n{defs}\nFEATURES:\n"),
            &ValidationOptions::default(),
        )
        .unwrap_err();
        assert!(error.to_string().contains("ambiguous overload"));
    }
}

#[test]
fn traits_desugar_receiver_and_expand_closed_parameters() {
    let report = validate(
        "A\nB\nKinds = A | B\nReader<T from Kinds>:\n    value: T\n    update: T -> ()\nReader.create<T from Kinds>: T -> Reader<T>",
        "get<T from Kinds>: Reader<T> -> T\nmake: A -> Reader<A>",
    );
    assert_eq!(costs(&report), vec![
        Cost {
            functions: 1,
            rules: 0
        };
        3
    ]);
    assert_ne!(report.features[0].name, report.features[1].name);
}

#[test]
fn generic_specialization_overlap_is_detected() {
    let error = validate_source(
        "input",
        "DEFINITIONS:\nA\nB\nKinds = A | B\nf<T from Kinds>: A -> T\nFEATURES:\n",
        &ValidationOptions::default(),
    )
    .unwrap_err();
    assert!(error.to_string().contains("ambiguous overload"));
}

#[test]
fn existentials_are_alpha_equivalent_but_have_no_implicit_pack_or_unpack() {
    let report = validate(
        "A\nB\nKinds = A | B\nColumn<T from Kinds>\nAny = exists T from Kinds: Column<T>",
        "same: (exists X from Kinds: Column<X>) -> (exists Y from Kinds: Column<Y>)\npack: Column<A> -> Any\nunpack: Any -> Column<A>",
    );
    assert!(matches!(
        report.features[0].status,
        FeatureStatus::Proved { .. }
    ));
    assert!(matches!(
        report.features[1].status,
        FeatureStatus::UnresolvableWithinUniverse { .. }
    ));
    assert!(matches!(
        report.features[2].status,
        FeatureStatus::UnresolvableWithinUniverse { .. }
    ));
}

#[test]
fn declared_deep_shapes_are_admitted_even_at_zero_synthesis_depth() {
    let source = "DEFINITIONS:\nA\nB\nf: List<List<A>> -> B\nFEATURES:\ng: List<List<A>> -> B\n";
    let report = validate_source("input", source, &ValidationOptions {
        max_depth: 0,
        ..ValidationOptions::default()
    })
    .unwrap();
    assert_eq!(costs(&report), vec![Cost {
        functions: 1,
        rules: 0
    }]);
}

#[test]
fn features_are_never_available_as_morphisms() {
    unresolved(&validate("A\nB", "f: A -> B\ng: A -> B"));
}

#[test]
fn empty_sections_are_valid_and_cycles_are_rejected_before_expansion() {
    assert!(validate("", "").features.is_empty());
    for defs in ["A = B\nB = A", "A<T from B>\nB = A<B>"] {
        let error = validate_source(
            "input",
            &format!("DEFINITIONS:\n{defs}\nFEATURES:\n"),
            &ValidationOptions::default(),
        )
        .unwrap_err();
        assert!(error.to_string().contains("cyclic"));
    }
}

#[test]
fn resource_exhaustion_never_reports_underivability_or_minimum_cost() {
    let source = "DEFINITIONS:\nA\nB\nf: A -> B\nFEATURES:\ng: A -> B\n";
    for options in [
        ValidationOptions {
            max_types: 1,
            ..ValidationOptions::default()
        },
        ValidationOptions {
            max_steps: 1,
            ..ValidationOptions::default()
        },
    ] {
        let report = validate_source("input", source, &options).unwrap();
        assert!(matches!(
            report.features[0].status,
            FeatureStatus::SearchIncomplete { .. }
        ));
    }
}

#[test]
fn complete_depth_zero_universe_can_certify_failure() {
    let source = "DEFINITIONS:\nA\nB\nFEATURES:\ng: A -> B\n";
    let report = validate_source("input", source, &ValidationOptions {
        exhaustive: true,
        max_depth: 0,
        ..ValidationOptions::default()
    })
    .unwrap();
    unresolved(&report);
    assert!(report.to_string().contains("UNRESOLVABLE_WITHIN_BOUNDS"));
}

#[test]
fn proof_alternative_limit_is_respected_and_results_are_deterministic() {
    let source = "DEFINITIONS:\nA\nB\nf: A -> B\ng: A -> B\nFEATURES:\nh: A -> B\n";
    let options = ValidationOptions {
        max_proofs: 1,
        ..ValidationOptions::default()
    };
    let report = validate_source("input", source, &options).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        unreachable!()
    };
    assert_eq!(proofs.len(), 1);
    assert_eq!(
        report.to_string(),
        validate_source("input", source, &options)
            .unwrap()
            .to_string()
    );
}

#[test]
fn external_checker_rejects_an_incorrect_cost_and_rule() {
    use stn_validator::{ProofNode, Rule, check_proof};
    let source = "DEFINITIONS:\nA\nB\nf: A -> B\nFEATURES:\ng: A -> B\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        unreachable!()
    };
    check_proof(source, &report.types, &report.proofs, proofs[0]).unwrap();
    let mut wrong_cost = report.proofs[proofs[0]].clone();
    wrong_cost.cost.functions = 0;
    let mut edited = report.proofs.clone();
    let wrong_cost = edited.insert(wrong_cost);
    assert!(check_proof(source, &report.types, &edited, wrong_cost).is_err());
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
    assert!(check_proof(source, &report.types, &edited, wrong_rule).is_err());
}

#[test]
fn nominal_mapping_can_be_an_intermediate_branch_transformation() {
    let report = validate(
        "A\nB\nC\nE\nF\nAs = List<A>\nBs = List<B>\nstart: C -> As | E\nmapElement: A -> B\nfinish: Bs -> C | F",
        "goal: C -> C | E | F",
    );
    assert!(
        matches!(report.features[0].status, FeatureStatus::Proved { .. }),
        "{report}"
    );
}

#[test]
fn nominal_flatmap_exposes_a_nominal_element_result_with_an_explicit_view() {
    let report = validate(
        "A\nB\nAs = List<A>\nBs = List<B>\nexpand: A -> Bs",
        "goal: As -> Bs",
    );
    assert_eq!(costs(&report), vec![Cost {
        functions: 1,
        rules: 3
    }]);
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        unreachable!()
    };
    assert!(
        report
            .proofs
            .expression(proofs[0], &report.types)
            .contains("view")
    );
}

#[test]
fn wide_sum_narrowing_has_no_silent_twelve_variant_cutoff() {
    let atoms = (0..14).map(|i| format!("V{i}")).collect::<Vec<_>>();
    let defs = format!("{}\nS = {}", atoms.join("\n"), atoms.join(" | "));
    assert_eq!(costs(&validate(&defs, "goal: List<S> -> List<V0>")), vec![
        Cost {
            functions: 0,
            rules: 1
        }
    ]);
}

#[test]
fn exhaustive_search_can_synthesize_a_product_and_certify_minimum_cost() {
    let report = validate_source(
        "input",
        "DEFINITIONS:\nFEATURES:\nf: () -> ((), ())\n",
        &ValidationOptions {
            exhaustive: true,
            max_depth: 1,
            ..ValidationOptions::default()
        },
    )
    .unwrap();
    assert_eq!(costs(&report), vec![Cost {
        functions: 0,
        rules: 3
    }]);
}

#[test]
fn full_documentation_examples_keep_their_expected_outcomes() {
    let doc = include_str!("../doc.md");
    let mut count = 0;
    for block in doc.split("~~~stn\n").skip(1) {
        let source = block.split("~~~").next().unwrap();
        if !source.starts_with("DEFINITIONS:") || !source.contains("FEATURES:") {
            continue;
        }
        count += 1;
        let result = validate_source("input", source, &ValidationOptions::default());
        if source.contains("f<T from Choices>") {
            assert!(result.is_err());
        } else {
            let report = result.unwrap();
            if source.contains("summary:") {
                assert_eq!(costs(&report), vec![Cost {
                    functions: 2,
                    rules: 5
                }]);
            }
            if source.contains("validItems:") {
                assert_eq!(costs(&report), vec![Cost {
                    functions: 1,
                    rules: 3
                }]);
            }
            if source.contains("resultWithError:") {
                assert!(matches!(
                    report.features[0].status,
                    FeatureStatus::Proved { .. }
                ));
                assert!(matches!(
                    report.features[1].status,
                    FeatureStatus::UnresolvableWithinUniverse { .. }
                ));
            }
        }
    }
    assert!(count >= 6);
}
