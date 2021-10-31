#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SExp<'a> {
    List(Vec<SExp<'a>>),
    // TODO: this should already be interned here to allow macros + gensym in the Alpha.
    Symbol(&'a str),
    Integer(&'a str),
    Float(&'a str),
}

impl<'a> SExp<'a> {
    pub fn as_list(&self) -> Option<&[SExp]> {
        match self {
            SExp::List(v) => Some(&v),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<&str> {
        if let SExp::Symbol(s) = self {
            Some(&s)
        } else {
            None
        }
    }

}

impl<'a> std::fmt::Display for SExp<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            SExp::List(v) => {
                write!(f, "(")?;
                let mut first = true;
                for i in v {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", i)?;
                    first = false;
                }
                write!(f, ")")
            }
            SExp::Symbol(s) => {
                write!(f, ":{}", s)
            }
            SExp::Integer(n) => {
                write!(f, "{}", n)
            }
            SExp::Float(n) => {
                write!(f, "{}", n)
            }
        }
    }
}
