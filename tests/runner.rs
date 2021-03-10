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

#[test]
fn test_effects() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/effects.pk"])
        .assert()
        .success();
}

#[test]
fn test_basic_print() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/basic_print.pk"])
        .assert()
        .stdout("3\n")
        .success();
}

#[test]
fn test_effects_run() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/effects_run.pk"])
        .assert()
        .stdout("1\n2\n3\n5\n")
        .success();
}

#[test]
fn test_multi_eff() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/multi_eff.pk"])
        .assert()
        .stdout("0\n1\n2\n3\n5\n")
        .success();
}

#[test]
fn test_coroutines() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/coroutines.pk"])
        .assert()
        .stdout("0\n1\n2\n3\n4\n5\n6\n")
        .success();
}

#[test]
fn test_poly_effects() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/poly_effects.pk"])
        .assert()
        .stdout("1\n2\n3\n4\n")
        .success();
}

#[test]
fn test_new_parsing() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/new_parsing.pk"])
        .assert()
        .success();
}

// Tests for type errors

#[test]
fn test_eff_not_allowed() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["tests/eff_not_allowed.pk"])
        .assert()
        .stderr(is_match("Effect .* not allowed in this context").unwrap())
        .stderr(contains("this context does not allow effects"))
        .stderr(contains("this context allows effects "))
        .stderr(contains("effects are not allowed in the top level context"))
        .failure();
}

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
