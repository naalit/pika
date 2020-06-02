use assert_cmd::*;

#[test]
fn test_repl() {
    Command::cargo_bin("pika")
        .unwrap()
        .arg("repl")
        .write_stdin("a := (fun i:Int => i) 12\n")
        .assert()
        .stdout("a0 : Int = 12\n");
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
