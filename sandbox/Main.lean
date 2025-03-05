import Mathlib.Tactic

variable {n m : ℕ}
variable {X Y : Finset ℕ}
variable {data : X -> Y -> ℤ}

theorem test_theorem_1
-- PROBLEM
-- Here we want to use a sum, but we defined `data` to take elements only of X.
-- So we need to turn our `x` into `{ x : ℕ // x ∈ X }` but we are lacking a
-- proof for `x ∈ X`!
-- : (∑ x ∈ X, ∑ y ∈ Y, data ⟨x, _⟩ y) = (∑ y ∈ Y, ∑ x ∈ X, data x y) := by
-- The missing piece was `Finset.attach`!
: (∑ x ∈ X.attach, ∑ y ∈ Y.attach, data x y)
  = (∑ y ∈ Y.attach, ∑ x ∈ X.attach, data x y) := by
  -- The proof was solved with a simple call to `apply?`
  -- (exact Finset.sum_comm)
  unfold Finset.sum
  exact Multiset.sum_map_sum_map X.attach.val Y.attach.val
  -- unfold Multiset.map

theorem test_theorem_2
-- This proposition is taken directly from the domino proof.
: (∑ x ∈ X, ∑ y ∈ Y, y % 2) % 2 
  = (∑ x ∈ X, (∑ y ∈ Y, y) % 2) % 2 := by
  -- `apply?` takes so long...
  -- `suffices :` is different from `suffices`! apparantly..
  suffices (X.card * ∑ y ∈ Y, y % 2) % 2 = (X.card * (∑ y ∈ Y, y) % 2) % 2 by
    simpa
  suffices (∑ y ∈ Y, y % 2) % 2 = (∑ y ∈ Y, y) % 2 by
    rw [Nat.mod_mod]
    rw [Nat.mul_mod]
    rw [this]
    simp_all
  exact Eq.symm (Finset.sum_nat_mod Y _ _)

