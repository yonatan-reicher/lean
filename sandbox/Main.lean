import Mathlib.Tactic

variable {n m : ℕ}
variable {X Y : Finset ℕ}
variable {data : X -> Y -> ℕ}

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
: (∑ _ ∈ X, ∑ y ∈ Y, y % 2) % 2
  = (∑ _ ∈ X, (∑ y ∈ Y, y) % 2) % 2 := by
  -- `apply?` takes so long...
  -- `suffices :` is different from `suffices`! apparantly..
  suffices (X.card * ∑ y ∈ Y, y % 2) % 2 = (X.card * (∑ y ∈ Y, y) % 2) % 2 by
    simpa
  suffices (∑ y ∈ Y, y % 2) % 2 = (∑ y ∈ Y, y) % 2 by
    -- These lemmas have had to be found manually by opening the docs..
    -- Every lemma must be looked for in three places: Init, Std, and MathLib.
    -- - then, you must look at Basic/Lemmas/Whatever that namespace divides
    -- definitions into.
    rw [Nat.mod_mod]
    rw [Nat.mul_mod]
    rw [this]
    rw [Nat.mul_mod_mod, Nat.mod_mul_mod]
  -- The following 3 lines of code all solve the current goal:
  -- 1. exact Eq.symm (Finset.sum_nat_mod Y _ _)
  -- 2. simp [Finset.sum_nat_mod]
  -- 3. rw [<-Finset.sum_nat_mod]
  -- I think the rewrite is the most intuitive for me.
  rw [<-Finset.sum_nat_mod]

abbrev Finset.a (x: Finset α) := Finset.attach x
theorem test_theorem_3
-- This proposition is taken directly from the domino proof.
: (∑ x ∈ X.a, ∑ y ∈ Y.a, data x y % 2) % 2
  = (∑ x ∈ X.a, (∑ y ∈ Y.a, data x y % 2) % 2) % 2 := by
  -- `apply?` takes so long...
  -- `suffices :` is different from `suffices`! apparantly..
  have : (∑ x ∈ X.a, ∑ y ∈ Y.a, Fin.ofNat' 2 (data x y))
     = Fin.ofNat' 2 (∑ x ∈ X.a, ∑ y ∈ Y.a, data x y) := by
    apply?



  suffices ∀ x, (∑ y ∈ Y.a, data x y % 2) % 2 = (∑ y ∈ Y.a, data x y) % 2 by
    -- These lemmas have had to be found manually by opening the docs..
    -- Every lemma must be looked for in three places: Init, Std, and MathLib.
    -- - then, you must look at Basic/Lemmas/Whatever that namespace divides
    -- definitions into.
    rw [Nat.mod_mod]
    rw [Nat.mul_mod]
    rw [this]
    rw [Nat.mul_mod_mod, Nat.mod_mul_mod]
  -- The following 3 lines of code all solve the current goal:
  -- 1. exact Eq.symm (Finset.sum_nat_mod Y _ _)
  -- 2. simp [Finset.sum_nat_mod]
  -- 3. rw [<-Finset.sum_nat_mod]
  -- I think the rewrite is the most intuitive for me.
  rw [<-Finset.sum_nat_mod]

-- PROBLEM: Monad notation acting weird with explicit name in `map`.
def inc : StateM Nat Nat := do
  let x ← get
  set (x + 1)
  return x

example : (inc.map fun x => x % 2) = ((fun x => x % 2) <$> inc) := by
  -- simp should be able to solve this, but it can't. This leads to various
  -- problems, when wanting to use StateT.map with an explicit name like that.
  -- it seems that it was not intended to be called by name like that, but that
  -- is not something I have seen documented.
  rfl
