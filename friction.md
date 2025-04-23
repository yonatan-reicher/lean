# Friction

This file documents places of "friction" with using Lean for theorem proving
(and maybe for general purpose programing as well).

#### Mathlib is Too Big
Mathlib is too big, compiled and downloaded, it takes gigabytes.
Mathlib can be installed globally for all projects, but:
1. It is not documented how.
2. It is not clear whether/how to do it for multiple versions of Lean+Mathlib.
3. May be problematic to keep projects and Mathlib versions compatible.

#### Mathlib is Too Slow
Starting the language server on a file that import Mathlib takes minutes.

#### Implicit Conversions
While making code much more readable, it makes it hard to write and hard to
change. Example: Sets have an implicit conversion to Sort. Sure, it makes
things easy to read, but it makes a "wrong model" in the user's head about the
language.

#### Missing Expected Syntax
For example, one can write `∑ x ∈ A, f x` but not `∑ h : x ∈ A, f x = 0` (to
take the hypothesis that x is in A as a variable).
Additionally, you can write `{ f x | x : T }` but not `{ x + 1 | x : T }`. (You
can only do function applications).

#### Hard to find certain contructions
For example, it was not clear to know to use `Finset.attach` in a specific
situation.
1. More general documentation for each types, focusing on the most common
   functinos would be very helpful in my opinion.

#### Suffices vs. Have Syntax Difference
The syntax for `have` allows you to write `have : P := e` as short for
`have this : P := e`, but suffices writes the very similiar shorthand without
the colon: `suffices P by e` for `suffices this : P by e`.

#### Lemmas in Different Places
Lemmas are sometimes placed in the `Init` (the core library), sometimes in the
`Std` library, sometimes in `Mathlib` (or even someplace else!).
It's a chore to look for lemmas in all of these places!
1. Loogle very much helps with finding lemmas.

#### Showing all Functions in a Namespace
It would be very helpful to have a command that shows all functions in a given
namespace. It would be mostly helpful for programing.

