use moplec::{
    core::{
        language::{
            *,
            InnerTerm::*,
            List::*
        },
        context::*,
        typing::*,
        eval::*
    }
};

#[test]
fn return_vars() {
    fn w(term: InnerTerm<()>) -> Term<()> { Term(Box::new(term), ()) }

    let term1: Term<()> =
        w(FunctionElim(
            w(FunctionIntro(
                w(Var(0))
            )),
            w(Var(0))
        ));
    assert_eq!(normalize(term1, Context::new()), w(Var(0)));

    let term2: Term<()> =
        w(FunctionElim(
            w(FunctionIntro(
                w(Var(0))
            )),
            w(Var(1))
        ));
    assert_eq!(normalize(term2, Context::new()), w(Var(1)));
}

#[test]
fn check_identity() {
    fn w<'a>(info: &'a str, term: InnerTerm<&'a str>) -> Term<&'a str> { Term(Box::new(term), info) }

    let term1: Term<_> =
        w("", Ann(
            w("", FunctionIntro(
                w("", Ann(
                    w("", FunctionIntro(
                        w("", Ann(
                            w("inner fn var 0", Var(0)),
                            w("inner fn var 1", Var(1))
                        ))
                    )),
                    w("", FunctionTypeIntro(
                        w("", Ann(
                            w("", CapturesListIntro(Cons(
                                w("", UniverseIntro(0, Usage::Unique)),
                                w("", Ann(
                                    w("", CapturesListIntro(Nil)),
                                    w("", CapturesListTypeIntro(0))
                                ))
                            ))),
                            w("", CapturesListTypeIntro(0))
                        )),
                        w("outer fn type ann var 0", Var(0)),
                        w("outer fn type ann var 1", Var(1)),
                    ))
                ))
            )),
            w("", Ann(
                w("", FunctionTypeIntro(
                    w("", Ann(
                        w("", CapturesListIntro(Nil)),
                        w("", CapturesListTypeIntro(0))
                    )),
                    w("", UniverseIntro(0, Usage::Unique)),
                    w("", FunctionTypeIntro(
                        w("", Ann(
                            w("", CapturesListIntro(Cons(
                                w("", UniverseIntro(0, Usage::Unique)),
                                w("", Ann(
                                    w("", CapturesListIntro(Nil)),
                                    w("", CapturesListTypeIntro(0))
                                ))
                            ))),
                            w("", CapturesListTypeIntro(0))
                        )),
                        w("outer fn type ann var 0", Var(0)),
                        w("outer fn type ann var 1", Var(1)),
                    ))
                )),
                w("", UniverseIntro(1, Usage::Unique))
            ))
        ));
    let term2: Term<_> =
        w("", Ann(
            w("", FunctionTypeIntro(
                w("", Ann(
                    w("", CapturesListIntro(Nil)),
                    w("", CapturesListTypeIntro(0))
                )),
                w("", UniverseIntro(0, Usage::Unique)),
                w("", FunctionTypeIntro(
                    w("", Ann(
                        w("", CapturesListIntro(Cons(
                            w("", UniverseIntro(0, Usage::Unique)),
                            w("", Ann(
                                w("", CapturesListIntro(Nil)),
                                w("", CapturesListTypeIntro(0))
                            ))
                        ))),
                        w("", CapturesListTypeIntro(0))
                    )),
                    w("outer fn type ann var 0", Var(0)),
                    w("outer fn type ann var 1", Var(1)),
                ))
            )),
            w("", UniverseIntro(1, Usage::Unique))
        ));

    match term1.r#type(Context::new()) {
        Ok(r#type) =>
            match check(&term1, r#type, Context::new()) {
                Ok(()) => {},
                Err(errs) => panic!("{:#?}", errs)
            },
        Err(errs) => panic!("{:#?}", errs)
    }
    match term2.r#type(Context::new()) {
        Ok(r#type) =>
            match check(&term2, r#type, Context::new()) {
                Ok(()) => {},
                Err(errs) => panic!("{:#?}", errs)
            },
        Err(errs) => panic!("{:#?}", errs)
    }
}

#[test]
fn check_capturing() {
    fn w(term: InnerTerm<()>) -> Term<()> { Term(Box::new(term), ()) }
    
    let term1: Term<_> =
        w(Ann(
            w(FunctionIntro(
                w(Ann(
                    w(FunctionIntro(
                        w(Var(1))
                    )),
                    w(FunctionTypeIntro(
                        w(Ann(
                            w(CapturesListIntro(Cons(
                                w(UniverseIntro(0, Usage::Unique)),
                                w(Ann(
                                    w(CapturesListIntro(Nil)),
                                    w(CapturesListTypeIntro(0))
                                ))
                            ))),
                            w(CapturesListTypeIntro(0))
                        )),
                        w(EnumTypeIntro(1)),
                        w(EnumTypeIntro(1))
                    ))
                ))
            )),
            w(FunctionTypeIntro(
                w(Ann(
                    w(CapturesListIntro(Nil)),
                    w(CapturesListTypeIntro(0))
                )),
                w(EnumTypeIntro(1)),
                w(FunctionTypeIntro(
                    w(Ann(
                        w(CapturesListIntro(Cons(
                            w(UniverseIntro(0, Usage::Unique)),
                            w(Ann(
                                w(CapturesListIntro(Nil)),
                                w(CapturesListTypeIntro(0))
                            ))
                        ))),
                        w(CapturesListTypeIntro(0))
                    )),
                    w(EnumTypeIntro(1)),
                    w(EnumTypeIntro(1))
                ))
            ))
        ));

    match term1.r#type(Context::new()) {
        Ok(r#type) =>
            match check(&term1, r#type, Context::new()) {
                Ok(()) => {},
                Err(errs) => panic!("{:#?}", errs)
            },
        Err(errs) => panic!("{:#?}", errs)
    }
}