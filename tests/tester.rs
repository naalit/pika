use assert_cmd::*;

#[test]
fn test_repl() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["repl", "--color", "none"])
        .write_stdin("a := (fun i:Int => i) 12")
        .assert()
        .stderr("--> a : Int = 12\n");
}

#[test]
fn test_basic() {
    Command::cargo_bin("pika")
        .unwrap()
        .args(&["build", "tests/basic.pk"])
        .assert()
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
