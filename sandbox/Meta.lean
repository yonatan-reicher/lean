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


-- cast is already taken
def cst {α} (x : α) (h : α = β := by congr 1 <;> solve | simp_all | omega) : β := cast h x


inductive Vec (a : Type) : Nat -> Type
  | nil : Vec a 0
  | cons : a -> Vec a n -> Vec a (n + 1)

-- This type checks without cst...
def vappend {a n m} (x: Vec a n) (y: Vec a m) : Vec a (m + n) :=
  match x with
  | .nil => y
  | .cons h t => .cons h (vappend t y)

-- But this doesn't! (Swapped n and m around)
def vappend' {a n m} (x: Vec a n) (y: Vec a m) : Vec a (n + m) :=
  match x with
  | .nil => cst y
  | .cons h t =>
    let x := Vec.cons h (vappend t y)
    have : n + 1 + m = m + n + 1 := by omega
    have : Vec a (n + 1 + m) = Vec a (m + n + 1) := by simp_all
    cst x
