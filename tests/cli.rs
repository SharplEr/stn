use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};
static NEXT_ID: AtomicU64 = AtomicU64::new(0);
fn binary() -> Command {
    Command::new(env!("CARGO_BIN_EXE_stn-validator"))
}
fn example(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(name)
}
fn assert_code(output: &Output, code: i32) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
fn temporary() -> PathBuf {
    std::env::temp_dir().join(format!(
        "stn-test-{}-{}",
        std::process::id(),
        NEXT_ID.fetch_add(1, Ordering::Relaxed)
    ))
}

#[test]
fn cli_outputs_checked_proofs() {
    let output = binary()
        .arg(example("examples/search.stypes"))
        .output()
        .unwrap();
    assert_code(&output, 0);
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("PROVED"));
    assert!(text.contains("cost: functions=2, rules=3"));
    assert!(text.contains("searchScores = matchDocs >>> extend(mapSet(score))"));
    assert!(!text.contains(" -> ") && !text.contains('@'));
}

#[test]
fn cli_writes_report_to_requested_file() {
    let path = temporary();
    let output = binary()
        .arg("-o")
        .arg(&path)
        .arg(example("examples/search.stypes"))
        .output()
        .unwrap();
    assert_code(&output, 0);
    assert!(output.stdout.is_empty());
    assert!(std::fs::read_to_string(&path).unwrap().contains("PROVED"));
    std::fs::remove_file(path).unwrap();
}

#[test]
fn cli_distinguishes_configuration_io_unresolved_and_resource_errors() {
    assert_code(&binary().arg("--unknown").output().unwrap(), 2);
    for flag in ["--max-proofs", "--max-types", "--max-steps"] {
        // A missing input would produce an I/O error if parsing accepted zero.
        let output = binary()
            .args([flag, "0"])
            .arg(temporary())
            .output()
            .unwrap();
        assert_code(&output, 2);
        assert!(String::from_utf8_lossy(&output.stderr).contains(flag));
    }
    assert_code(&binary().arg(temporary()).output().unwrap(), 1);
    let input = temporary();
    std::fs::write(&input, "DEFINITIONS:\nA\nB\nFEATURES:\nf: A -> B\n").unwrap();
    let unresolved = binary().arg(&input).output().unwrap();
    std::fs::remove_file(input).unwrap();
    assert_code(&unresolved, 3);
    assert!(
        String::from_utf8_lossy(&unresolved.stdout).contains("UNRESOLVABLE_IN_RELEVANT_UNIVERSE")
    );
    let incomplete = binary()
        .args(["--max-steps", "1"])
        .arg(example("examples/search.stypes"))
        .output()
        .unwrap();
    assert_code(&incomplete, 4);
    assert!(String::from_utf8_lossy(&incomplete.stdout).contains("SEARCH_INCOMPLETE"));
}

#[test]
fn cli_reports_validation_and_output_failures_with_context() {
    let input = temporary();
    for source in [
        "DEFINITIONS:\nFEATURES:\nbroken: () ->\n",
        "DEFINITIONS:\nA\nFEATURES:\nunknown: A -> Missing\n",
    ] {
        std::fs::write(&input, source).unwrap();
        let output = binary().arg(&input).output().unwrap();
        assert_code(&output, 2);
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains(&input.display().to_string()));
    }

    // Writing the report must succeed before an unresolved-feature code is returned.
    std::fs::write(&input, "DEFINITIONS:\nA\nB\nFEATURES:\ngoal: A -> B\n").unwrap();
    let directory = temporary();
    std::fs::create_dir(&directory).unwrap();
    let output = binary()
        .arg(&input)
        .arg("-o")
        .arg(&directory)
        .output()
        .unwrap();
    std::fs::remove_file(input).unwrap();
    std::fs::remove_dir(&directory).unwrap();
    assert_code(&output, 1);
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains(&directory.display().to_string()));
}

#[test]
fn version_does_not_print_usage() {
    let output = binary().arg("--version").output().unwrap();
    assert_code(&output, 0);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("stn-validator {}\n", env!("CARGO_PKG_VERSION"))
    );
}

#[cfg(unix)]
#[test]
fn accepts_non_utf8_file_paths() {
    use std::{ffi::OsString, os::unix::ffi::OsStringExt};
    let mut bytes = temporary().into_os_string().into_vec();
    bytes.push(0xff);
    let path = PathBuf::from(OsString::from_vec(bytes));
    std::fs::write(&path, "DEFINITIONS:\nA\nFEATURES:\nf: A -> A\n").unwrap();
    let output = binary().arg("--").arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    assert_code(&output, 0);
}
