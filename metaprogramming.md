# Meta-Programming in Lean
- [Meta-Programming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/main/01_intro.html)

Was last in:
https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html

Lean is split to meta-level code and object-level code.
The meta-level code has access to the Concrete Syntax Tree (via the `Syntax`
type) and to the AST (via the `Expr` type).


Lean uses Lisp-like syntax for quotations:
```
`(fun $x => $e).
```


