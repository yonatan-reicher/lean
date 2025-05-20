import Lean

macro x:ident ":" t:term " => " y:term : term =>
  `(fun $x : $t => $y)
#reduce x : Nat => x + 1


inductive Lam
  | var : String -> Lam
  | app : Lam -> Lam -> Lam
  | func : String -> Lam -> Lam


declare_syntax_cat lam
syntax "lambda" lam : term
syntax "(" lam ")" : lam
syntax str : lam
syntax lam lam : lam
syntax str " => " lam : lam

macro_rules
  | `(lambda ( $x:lam )) => `(lambda $x)
  | `(lambda $x:str) => `(Lam.var $x)
  | `(lambda $x:str => $y:lam) => `(Lam.func $x (lambda $y))
  | `(lambda $x:lam $y:lam) => `(Lam.app (lambda $x) (lambda $y))


#reduce lambda ("x" => "y" => "x" "y" "y")
