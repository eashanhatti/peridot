#[macro_export]
macro_rules! Univ {
    () => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::TypeTypeIntro),
            None)
    };
    (,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::TypeTypeIntro),
            Some(Box::new($ann)))
    }
}

#[macro_export]
macro_rules! var {
    ($index:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::Var($index)),
            None)
    };
    ($index:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::Var($index)),
            Some(Box::new($ann)))
    };
    ($index:expr, $note:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new_with_note(
            Note(String::from($note)),
            Box::new(crate::lang::core::lang::InnerTerm::Var($index)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! pair {
    ($fst:expr, $snd:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::PairIntro(
                $fst,
                $snd)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! Pair {
    ($fst_type:expr, $snd_type:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::PairTypeIntro(
                $fst_type,
                $snd_type)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! split {
    ($discrim:expr, in $body:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::PairElim(
                $discrim,
                $body)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! Doub {
    (,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::DoubTypeIntro),
            Some(Box::new($ann)))
    };
    ($note:expr ,: $ann:expr) => {
        crate::lang::core::lang::Term::new_with_note(
            Note(String::from($note)),
            Box::new(crate::lang::core::lang::InnerTerm::DoubTypeIntro),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! doub {
    (this,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::DoubIntro(crate::lang::core::lang::Doub::This)),
            Some(Box::new($ann)))
    };
    (that,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::DoubIntro(crate::lang::core::lang::Doub::That)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! case {
    ($discrim:expr, l => $lbranch:expr; r => $rbranch:expr;,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::DoubElim(
                $discrim,
                $lbranch,
                $rbranch)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! unit {
    (,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::UnitIntro),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! Unit {
    (,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::UnitTypeIntro),
            Some(Box::new($ann)))
    };
    ($note:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new_with_note(
            Note(String::from($note)),
            Box::new(crate::lang::core::lang::InnerTerm::UnitTypeIntro),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! Void {
    (,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::VoidTypeIntro),
            Some(Box::new($ann)))
    };
    ($note:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new_with_note(
            Note(String::from($note)),
            Box::new(crate::lang::core::lang::InnerTerm::VoidTypeIntro),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! pi {
    ($in_type:expr, $out_type:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::FunctionTypeIntro(
                $in_type,
                $out_type)),
            Some(Box::new($ann)))
    };
    ($note:expr, $in_type:expr, $out_type:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new_with_note(
            Note(String::from($note)),
            Box::new(crate::lang::core::lang::InnerTerm::FunctionTypeIntro(
                $in_type,
                $out_type)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! fun {
    ($body:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::FunctionIntro($body)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! rec {
    ($body:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::Rec($body)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! apply {
    ($abs:expr, $arg:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::FunctionElim(
                $abs,
                $arg)),
            None)
    };
    ($abs:expr, $arg:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::FunctionElim(
                $abs,
                $arg)),
            Some(Box::new($ann)))
    };

}

#[macro_export]
macro_rules! postulate {
    ($sym:expr ,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::Postulate($sym)),
            Some(Box::new($ann)))
    };
}

#[macro_export]
macro_rules! Indexed {
    ($index:expr, $inner:expr,: $ann:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::IndexedTypeIntro($index, $inner)),
            Some(Box::new($ann)))  
    };
}

#[macro_export]
macro_rules! let_bind {
    ($bindings:expr, $body:expr) => {
        crate::lang::core::lang::Term::new(
            Box::new(crate::lang::core::lang::InnerTerm::Let(
                $bindings,
                $body)),
            None)
    };
}