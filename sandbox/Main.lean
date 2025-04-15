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
  
  have myLemma {β} {A : Finset β} {f : A -> Nat}
  : (∑ a ∈ A.a, f a) % 2 = (∑ a ∈ A.a, (f a % 2)) % 2 := by
    -- Found by `exact?`
    exact Finset.sum_nat_mod A.a 2 f

  rw [myLemma]


inductive Dir where
  | left
  | right
  | stay


instance : HAdd Nat Dir Nat where
  hAdd
  | n, .left => n - 1
  | n, .stay => n
  | n, .right => n + 1


abbrev Alphabet := Finset Char


-- Can't use Σ as an identifier in Lean
structure TuringMachine (Γ : Alphabet) where
  {Q : Type}
  finite_Q : Finite Q
  accept : Q
  reject : Q
  transition
  : { q : Q // q ≠ accept ∧ q ≠ reject } × Option Γ -> Q × Option Γ × Dir


structure Tape (Γ : Alphabet) where
  chars : List (Option Γ)
  h : chars.getLast? ≠ some none


structure Configuration (Q : Type) (Γ : Alphabet) where
  state : Q
  cursor : Nat
  tape : List (Option Γ) -- How do we make this infinite?
  

variable {Q : Type} {finite_Q : Finite Q} {Γ : Alphabet}


abbrev TuringMachine.Q_not_accept_not_reject (m : TuringMachine Γ) :=
  { q : m.Q // q ≠ m.accept ∧ q ≠ m.reject }


def stripLeftNones {α} : List (Option α) -> List (Option α)
    | [] => []
    | none :: l => stripLeftNones l
    | some a :: l => some a :: l


def stripRightNones {α} (l : List (Option α)) :=
    l.reverse
    |> stripLeftNones
    |>.reverse


def Tape.ofList (l : List (Option Γ)) : Tape Γ :=
  { chars := stripRightNones l
    h := by
      unfold stripRightNones
      rw [List.getLast?_reverse]
      induction l.reverse with
      | nil => exact ne_of_beq_false rfl
      | cons head tail ih =>
        cases head with
        | some head =>
          unfold stripLeftNones
          exact ne_of_beq_false rfl
        | none => 
          unfold stripLeftNones
          exact ih
  }


def Configuration.current (c : Configuration Q Γ) : Option Γ :=
  c.tape[c.cursor]?.join


def Tape.set (tape : Tape Γ) (cursor : Nat) (current' : Option Γ) :=
  tape.chars
  |> extendToCursor
  |>.set cursor current'
  |> Tape.ofList
  where
    extendToCursor (l : List _) : List _ :=
      l ++ List.replicateTR (cursor - l.length) none

    stripRightNones {α} (l : List (Option α)) :=
      l.reverse
      |> stripLeftNones
      |>.reverse

    stripLeftNones {α} : List (Option α) -> List (Option α) 
      | [] => []
      | none :: l => stripLeftNones l
      | some a :: l => some a :: l


def TuringMachine.step
(m : TuringMachine Γ) (c : Configuration m.Q_not_accept_not_reject Γ)
: Configuration m.Q Γ :=
  m.transition (c.state, c.current)
  |> fun ⟨state', current', dir⟩ =>
    { state := state'
      cursor := c.cursor + dir
      tape := c.tape.set c.cursor current'
    }


def accepts (m : TuringMachine Γ) (c : Configuration m.Q Γ) : Prop :=
  ∃ (n : Nat), (m.step^[n] c).state = 0


class Computable (f : α -> β)


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
