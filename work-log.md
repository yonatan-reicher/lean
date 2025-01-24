2025-01-16: Download lean and have lots of problems
2025-01-17: Download elan + start lean number game
⋮⋮⋮⋮⋮⋮⋮⋮⋮⋮⋮
2025-01-24: Finish number game!

## Links
- [mathematics in lean](https://leanprover-community.github.io/mathematics_in_lean/C01_Introduction.html)
- [lean language reference](https://lean-lang.org/doc/reference/latest/)

## Ideas 

- Proofs are unreadable
  Proofs with comments (explaining the goal) are very readable

- example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b
  From level 2 in Algorithm World from The Natural Numbers Game
  The narrator starts with suggesting `repeat rw [add_assoc]` to push all the
  parentheses to the right. This is an example of syntactic normalization, useful
  to represent abstractions that we humans take for granted! (If two things are
  equivalent, they should be syntactically equal)
  Type class for types with a syntactic normal form?


## Case Study

A surprisingly hard and unreadable proof for a very very simple theorem

```lean
theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
    -- if x = 0 /\ y = 0 then trivial
    -- if x = succ x0 /\ y = succ y0 then induction!
    induction x with x0 hx0
    left
    exact zero_le y
    cases hx0
    cases h with w h
    cases w
    rw [add_zero] at *
    rw [h]
    right
    apply le_succ_self
    cases a
    rw [add_succ, add_zero] at *
    rw [h]
    left
    apply le_refl
    rw [h]
    repeat rw [add_succ]
    left
    use succ a_1
    rw [add_succ]
    rw [succ_add]
    rfl
    right
    cases h
    use (succ w)
    rw [add_succ]
    rw [h_1]
    rfl
```
How would we prove this with pen & paper? I'll limit myself to the definition
of (x ≤ y ⇔ ∃ z, y = x + z) and no inverse assumption.
Let x, y be natural numbers.
If x = 0, then y = 0 + y, so x ≤ y. Done.
If y = 0, then x = 0 + x, so y ≤ x. Done.
Else x = succ x₀, y = succ y₀.
Now we assume by induction x₀ ≤ y₀ ∨ y₀ ≤ x₀.
Now inject succ on both sides, and we get succ x₀ ≤ succ y₀ ∨ succ y₀ ≤ succ x₀.
Rewrite, and we get x ≤ y ∨ y ≤ x. Done.
