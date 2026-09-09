use shinri_bench::report::render;
use shinri_bench::results::read_all;
use std::path::Path;

#[test]
fn report_matches_golden() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let (fx, rows) = read_all(&dir.join("report_rows.jsonl")).unwrap();
    let got = render(fx.as_ref(), &rows);
    let want = std::fs::read_to_string(dir.join("report_golden.md")).unwrap();
    if std::env::var_os("UPDATE_GOLDEN").is_some() {
        std::fs::write(dir.join("report_golden.md"), &got).unwrap();
        return;
    }
    assert_eq!(
        got, want,
        "run with UPDATE_GOLDEN=1 to regenerate after an intentional change"
    );
}
