use assert_cmd::*;
use predicates::str::*;

#[test]
fn test_basic() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/basic.pk"])
        .assert()
        .success();
}

// Currently, this test takes over a minute to run on debug builds, so it's disabled.
// It's still worth running `cargo run tests/smalltt.pk` before committing anything, though, to make sure it's not broken.
// #[test]
// fn test_smalltt() {
//     Command::cargo_bin("pika")
//         .unwrap()
//         .args(&["tests/smalltt.pk"])
//         .assert()
//         .success();
// }

#[test]
fn test_data() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/data.pk"])
        .assert()
        .success();
}

#[test]
fn test_match() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/match.pk"])
        .assert()
        .success();
}

#[test]
fn test_gadt() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/gadt.pk"])
        .assert()
        .success();
}

#[test]
fn test_numbers() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/numbers.pk"])
        .assert()
        .success();
}

#[test]
fn test_bools() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/bools.pk"])
        .assert()
        .success();
}

#[test]
fn test_fact() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/fact.pk"])
        .assert()
        .success();
}

#[test]
fn test_unit() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/unit.pk"])
        .assert()
        .success();
}

#[test]
fn test_mutual() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/mutual.pk"])
        .assert()
        .success();
}

#[test]
fn test_type_in_do() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/type_in_do.pk"])
        .assert()
        .success();
}

// Tests for type errors

#[test]
fn test_curry_errors() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/curry_errors.pk"])
        .assert()
        .stderr(contains("Too few arguments 1"))
        .stderr(contains("Too many arguments 3"))
        .stderr(contains("expects 2 arguments"))
        .stderr(contains("Could not match types"))
        .stderr(is_match("expects 1 argument[^s]").unwrap())
        .failure();
}

#[test]
fn test_wrong_if_type() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/wrong_if_type.pk"])
        .assert()
        .stderr(is_match("Expected value of type.*Bool").unwrap())
        .failure();
}

#[test]
fn test_untyped_literal() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/untyped_literal.pk"])
        .assert()
        .stderr(contains("Could not infer type"))
        .failure();
}

#[test]
fn test_inexhaustive() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/inexhaustive.pk"])
        .assert()
        .stderr(contains("Inexhaustive"))
        .stderr(predicates::str::is_match("False.* not covered").unwrap())
        .failure();
}

#[test]
fn test_wrong_cons() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/wrong_cons.pk"])
        .assert()
        .stderr(contains("Invalid"))
        .failure();
}

#[test]
fn test_duplicate_constructor() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/duplicate_constructor.pk"])
        .assert()
        .stderr(contains("Duplicate"))
        .failure();
}

#[test]
fn test_wrong_constructor_type() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/wrong_constructor_type.pk"])
        .assert()
        .stderr(contains("Constructor return type"))
        .failure();
}

#[test]
fn test_fail() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/fail.pk"])
        .assert()
        .failure();
}
