use assert_cmd::*;
use predicates::prelude::*;
use predicates::str::*;

#[test]
fn test_basic() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/basic.pk"])
        .assert()
        .success();
}

#[test]
fn test_smalltt() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/smalltt.pk"])
        .assert()
        .success();
}

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
fn test_inexhaustive() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/inexhaustive.pk"])
        .assert()
        .stderr(contains("Inexhaustive"))
        .stderr(contains("'False' not covered"))
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
