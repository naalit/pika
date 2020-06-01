use assert_cmd::*;

#[test]
fn test_repl() {
    Command::cargo_bin("pika")
        .unwrap()
        .write_stdin("a := (fun i:Int => i) 12\n")
        .assert()
        .stdout("a0 : Int = 12\n");
}

#[test]
fn test_basic() {
    Command::cargo_bin("pika")
        .unwrap()
        .arg("tests/basic.pk")
        .assert()
        .success();
}

#[test]
fn test_error() {
    Command::cargo_bin("pika")
        .unwrap()
        .arg("tests/error.pk")
        .assert()
        .failure();
}
