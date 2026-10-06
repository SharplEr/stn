use stn_validator::{
    Cost, FeatureStatus, ProofNode, ProofStore, Rule, ValidationOptions, validate_source,
};

#[test]
fn shared_premises_count_each_occurrence_without_copying_nodes() {
    let source = "DEFINITIONS:\nA\nFEATURES:\nrepeat: A -> (A, A)\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
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
    report.proofs.check(root, source, &report.types).unwrap();
}

#[test]
fn compaction_retains_multiple_roots_and_reuses_identical_feature_proofs() {
    let source = "DEFINITIONS:\nA\nB\nUnused\nUnusedPair = (A, Unused)\n\
        FEATURES:\nfirst: A -> A\nsecond: B -> B\nagain: A -> A\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
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
        report.proofs.check(root, source, &report.types).unwrap();
    }
}

#[test]
fn external_checker_rejects_cyclic_and_missing_premises() {
    let source = "DEFINITIONS:\nA\nFEATURES:\nrepeat: A -> (A, A)\n";
    let report = validate_source("input", source, &ValidationOptions::default()).unwrap();
    let FeatureStatus::Proved { proofs } = &report.features[0].status else {
        panic!("expected proof");
    };
    // Deliberately misuse foreign indices to construct malformed external records.
    // The original fanout's first child is at zero; in an empty store it becomes
    // the inserted parent itself, so importing it must detect the cycle.
    let mut cyclic = ProofStore::default();
    let cycle = cyclic.insert(report.proofs[proofs[0]].clone());
    let error = cyclic.check(cycle, source, &report.types).unwrap_err();
    assert!(error.to_string().contains("cycle"));

    let mut wrong_child = report.proofs[proofs[0]].clone();
    wrong_child.node = ProofNode::Inference {
        rule: Rule::Compose,
        children: vec![proofs[0]],
    };
    let mut missing = ProofStore::default();
    let root = missing.insert(wrong_child);
    let error = missing.check(root, source, &report.types).unwrap_err();
    assert!(error.to_string().contains("invalid proof identifier"));
}
