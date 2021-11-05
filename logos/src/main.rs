use typed_arena::Arena;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Alphabet {
  X,
  Y,
  Z,
}

#[derive(Debug, Clone)]
enum Expr<'arena> {
    Tectum,
    Falsum,
    Variable(Alphabet),
    And(&'arena Expr<'arena>, &'arena Expr<'arena>),
    Or(&'arena Expr<'arena>, &'arena Expr<'arena>),
    Not(&'arena Expr<'arena>),
}

use self::Alphabet::*;
use self::Expr::*;

impl PartialEq for Expr<'_> {
    fn eq(&self, other: &Self) -> bool {
       match (self, other) {
        (Or(x, y), Or(a, b)) => x == a && y == b,
        (And(x, y), And(a, b)) => x == a && y == b,
        (Not(x), Not(y)) => x == y,
        (Tectum, Tectum) => true,
        (Falsum, Falsum) => true,
        (Variable(a), Variable(b)) => a == b,
        _ => false,
       }
    }
}

impl Eq for Expr<'_> {}

impl Expr<'a> {
    fn simplify(self) -> Expr<'a> {
        match self {
            And(x, y) if x == y => x,
            Or(x, y) if x == y => x,
            Not(Not(x)) => x,
            And(x, y) => And(&x.simplify(), &y.simplify()),
            Or(x, y) => Or(&x.simplify(), &y.simplify()),
            _ => self
        }
    }
}



fn main() {
    let arena = Arena::new();
    let vx = arena.alloc(Variable(X));
    let vy = arena.alloc(Variable(Y));
    let expr = arena.alloc(And(vx, vy));
    print!("foo = {:?}", expr)
}
