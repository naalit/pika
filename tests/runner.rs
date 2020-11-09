use assert_cmd::*;
use predicates::prelude::*;

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
fn test_fail() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/fail.pk"])
        .assert()
        .failure();
}
