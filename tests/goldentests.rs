use goldentests::*;

#[test]
fn run_golden_tests() -> TestResult<()> {
    let config = TestConfig::new("target/debug/alpha", "tests/golden", "# ")?;
    config.run_tests()
}
