import MathLib

variable {α : Type}
variable {a : α}

-- Problem: Proof irrelevance. https://www.pointedset.ca/blog/2020/02/06/proptype.html

/-- This type class states that the sort `α` has some partial normal form
    form. -/
class NormalForm (α : Sort u) where
  nf : α -> α
  eq : ∀ a, a = nf a

export NormalForm (nf)

@[simp]
lemma nf_nf [NormalForm α] : nf (nf a) = nf a :=
  -- by rw [NormalForm.eq (nf a)]
  NormalForm.eq (nf a) |>.symm

instance {n : ℕ} : NormalForm (n + 1) where
  nf
  | Prop.True => True
  eq a := rfl

instance : NormalForm (1 + n) where
  nf := Nat.succ n
  eq_x_eq_nf := by simp [Nat.add_comm (m := 1)]
