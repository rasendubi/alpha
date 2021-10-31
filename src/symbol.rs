use string_interner::{StringInterner, symbol::SymbolU32};

#[derive(Debug)]
pub struct SymbolInterner(StringInterner);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(SymbolU32);

impl SymbolInterner {
    pub fn new() -> Self {
        SymbolInterner(StringInterner::new())
    }

    pub fn get_or_intern<T: AsRef<str>>(&mut self, s: T) -> Symbol {
        Symbol(self.0.get_or_intern(s))
    }

    pub fn get<T: AsRef<str>>(&self, s: T) -> Option<Symbol> {
        self.0.get(s).map(Symbol)
    }

    pub fn resolve(&self, symbol: Symbol) -> Option<&str> {
        self.0.resolve(symbol.0)
    }
}
