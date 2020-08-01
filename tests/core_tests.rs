use moplec::*;
use moplec::core::language::*;
use InnerTerm::*;

#[test]
fn return_vars() {
    let term1: Term<()> =
        w(FunctionElim(
            w(FunctionIntro(
                w(Var(0))
            )),
            w(Var(0))
        ));
    assert_eq!(normalize(term1, Vec::new()), w(Var(0)));

    let term2: Term<()> =
        w(FunctionElim(
            w(FunctionIntro(
                w(Var(0))
            )),
            w(Var(1))
        ));
    assert_eq!(normalize(term2, Vec::new()), w(Var(1)));
}