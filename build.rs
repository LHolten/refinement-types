fn main() {
    println!("cargo:rerun-if-changed=src/parse/code.lalrpop");
    lalrpop::process_root().unwrap();
}
