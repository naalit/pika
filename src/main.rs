mod term;
use term::*;
mod error;

use lalrpop_util::*;
lalrpop_mod!(pub grammar);

use string_interner::Sym;
use std::ops::{Deref, DerefMut};
use std::collections::HashMap;

pub struct Env(HashMap<Sym, Term>, usize);
impl std::fmt::Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for (k, v) in self.0.iter() {
            writeln!(f, "\t{} = {}", INTERN.read().unwrap().resolve(*k).unwrap(), v)?;
        }
        write!(f, "  }}")
    }
}
impl Env {
    fn new() -> Self {
        Env(HashMap::new(), 0)
    }
    fn next_tv(&mut self) -> Sym {
        let mut intern = INTERN.write().unwrap();
        let mut s = intern.get_or_intern(format!("t{}", self.1));
        while self.0.contains_key(&s) {
            self.1 += 1;
            s = intern.get_or_intern(format!("t{}", self.1));
        }
        self.1 += 1;
        s
    }
}
impl Deref for Env {
    type Target = HashMap<Sym, Term>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for Env {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Gathers constraints (in the form of `type = type`) and returns the type of `t`
/// Note that env here stores the TYPE of each variable
fn gather(t: &Term, env: &mut Env, cons: &mut Vec<(Term, Term)>) -> Term {
    match t {
        Term::I32(_) => Term::Builtin(Builtin::Int),
        Term::Builtin(Builtin::Int) => Term::Type,
        Term::Type => Term::Type,
        Term::Arrow(_, _) => Term::Type,
        Term::App(f, x) => {
            let ft = gather(f, env, cons);
            let xt = gather(x, env, cons);
            let tv = Term::Var(env.next_tv());
            cons.push((ft, Term::Arrow(Box::new(xt), Box::new(tv.clone()))));
            tv
        }
        Term::Var(s) => match env.get(s) {
            Some(t) => t.clone(),
            None => Term::Var(*s),
        }
        Term::Fun(x, b) => {
            let xt = Term::Var(env.next_tv());
            let old = env.remove(x);
            env.insert(*x, xt.clone());
            let bt = gather(b, env, cons);
            env.remove(x);
            if let Some(old) = old {
                env.insert(*x, old);
            }
            Term::Arrow(Box::new(xt), Box::new(bt))
        }
    }
}

#[derive(Debug, Clone)]
enum TypeError {
    Infinite(Sym, Term),
    Constraint(Term, Term),
}

/// Figures out whether this constraint set is solvable, and if so solves it
fn unify(mut cons: Vec<(Term, Term)>) -> Result<Env, TypeError> {
    let mut env = Env::new();
    loop {
        if cons.is_empty() {
            break;
        }
        let c = cons.pop().unwrap();
        match c {
            (Term::Arrow(ax, ar), Term::Arrow(bx, br)) => {
                cons.push((*ax, *bx));
                cons.push((*ar, *br));
            }
            (Term::Builtin(a), Term::Builtin(b)) if a == b => (),
            (Term::Type, Term::Type) => (),
            (Term::Var(v), x) | (x, Term::Var(v)) => if x.occurs(v) {
                return Err(TypeError::Infinite(v, x))
            } else {
                for (a, b) in cons.iter_mut() {
                    a.sub(v, &x);
                    b.sub(v, &x);
                }
                for i in env.values_mut() {
                    i.sub(v, &x);
                }
                env.insert(v, x);
            }
            (x, y) => return Err(TypeError::Constraint(x, y)),
        }
    }
    Ok(env)
}

fn main() {
    let mut rl = rustyline::Editor::<()>::new();
    let parser = grammar::TermParser::new();
    loop {
        let readline = rl.readline("> ");
        match readline {
            Err(_) => break,
            Ok(line) => {
                let f = error::FILES.write().unwrap().add("<input>".to_string(), line.clone());
                match parser.parse(&line) {
                    Ok(t) => {
                        println!("{}", t);
                        let mut cons = Vec::new();
                        let ty = gather(&t, &mut Env::new(), &mut cons);
                        match unify(cons) {
                            Ok(env) => println!("  : {}\n  where {}", ty, env),
                            Err(e) => println!("Type error: {:?}", e),
                        }
                    },
                    Err(e) => error::Error::from_lalrpop(e, f).write().unwrap(),
                }
            }
        }
    }
}
