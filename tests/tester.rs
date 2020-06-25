use assert_cmd::*;
use predicates::prelude::*;

#[test]
fn test_repl() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["repl", "--color", "none"])
        .write_stdin("a := (fun i:Int => i) 12")
        .assert()
        .stderr("--> a : Int = 12\n")
        .success();
}

#[test]
fn test_basic() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/basic.pk"])
        .assert()
        .stdout("5\n")
        .success();
}

#[test]
fn test_tag() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/tag.pk"])
        .assert()
        .stdout("3\n")
        .success();
}

#[test]
fn test_error() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["build", "tests/error.pk"])
        .assert()
        .failure();
}

#[test]
fn test_closures_llvm() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/closure.pk"])
        .assert()
        .stdout("(2, 12)\n")
        .success();
}

#[test]
fn test_struct() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/struct.pk"])
        .assert()
        .stdout("(12, 4)\n")
        .success();
}

#[test]
fn test_struct_env() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/struct_env.pk"])
        .assert()
        .stdout("(2, 3)\n")
        .success();
}

#[test]
fn test_match() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/match.pk"])
        .assert()
        .stdout("(8, 4)\n")
        .success();
}

#[test]
fn test_match_int() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/match_int.pk"])
        .assert()
        .stdout("(12, 4)\n")
        .success();
}

#[test]
fn test_missing_branch() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["build", "tests/missing_branch.pk"])
        .assert()
        .failure();
}

#[test]
fn test_fib() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/fib.pk"])
        .assert()
        .stdout("610\n")
        .success();
}

#[test]
fn test_fib_intepret() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["repl"])
        .write_stdin(
            r#"fib := fun { 0 => 1; 1 => 1; i:Int => (fib (i - 1)) + (fib (i - 2)) }
main := fib 14
"#,
        )
        .assert()
        .stderr(predicate::str::contains("610"))
        .success();
}

#[test]
fn test_unordered_struct() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["run", "tests/unordered_struct.pk"])
        .assert()
        .stdout("(6, 720)\n")
        .success();
}

#[test]
fn test_affine_pass() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["build", "tests/affine_pass.pk"])
        .assert()
        .success();
}

#[test]
fn test_affine_fail() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["build", "tests/affine_fail.pk"])
        .assert()
        .failure();
}

#[test]
fn test_affine_fail_fun() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["build", "tests/affine_fail_fun.pk"])
        .assert()
        .failure();
}
