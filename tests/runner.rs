use pika2::*;

struct Test {
    result: ElabResult,
    errors: Vec<ElabError>,
}
impl Test {
    fn write_errs(&self) {
        for e in &self.errors {
            e.write_err(&self.result);
        }
    }

    fn succeeds(self) -> Test {
        if !self.errors.is_empty() {
            self.write_errs();
            panic!("Test failed with {} errors", self.errors.len())
        }
        self
    }

    fn num_errors(self, n: usize) -> Test {
        assert_eq!(self.errors.len(), n);
        self
    }
}
fn test(files: &[&str]) -> Test {
    let files: Vec<_> = files
        .iter()
        .map(|x| format!("tests/{}", x).into())
        .collect();
    let result = elab_files(&files).unwrap();
    let errors = result.all_errors();
    Test { result, errors }
}

#[test]
fn smalltt() {
    test(&["Smalltt.pk"]).succeeds();
}

#[test]
fn dep_errors() {
    test(&["DepErrors.pk"]).num_errors(1);
    let errors = elab_files(&["tests/DepErrors.pk".into()])
        .unwrap()
        .all_errors();
    assert_eq!(errors.len(), 1); // TODO verify the content of the error
}

#[test]
fn references() {
    test(&["References.pk"]).succeeds();
}

#[test]
fn ref_errors() {
    test(&["ReferencesErr.pk"]).num_errors(29);
}

#[test]
fn gadts() {
    test(&["GADTs.pk"]).succeeds();
}

#[test]
fn structs() {
    test(&["Structs.pk"]).succeeds();
}

#[test]
fn traits() {
    test(&["Traits.pk"]).succeeds();
}
