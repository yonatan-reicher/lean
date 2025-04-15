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



-- Definition of domino tiling

@[ext]
structure Point where
  x : ℕ
  y : ℕ
deriving Repr, DecidableEq

def point (pt : ℕ × ℕ) : Point :=
  ⟨pt.1, pt.2⟩

inductive Domino
| H (lft : Point)
| V (top : Point)
deriving Repr

def cells : Domino → Finset Point
| Domino.H lft => ⟨{ ⟨lft.x, lft.y⟩, ⟨lft.x + 1, lft.y⟩ }, by simp⟩
| Domino.V top => ⟨{ ⟨top.x, top.y⟩, ⟨top.x, top.y + 1⟩ }, by simp⟩

def board (n m : ℕ) : Finset Point :=
  Finset.map ⟨point, by simp [Function.Injective, point]⟩
    (Finset.range n ×ˢ Finset.range m)

structure DominoTiling (n m : ℕ) where
  tiles : Finset Domino
  disjoint : Set.PairwiseDisjoint tiles (cells ·)
  union : tiles.disjiUnion (cells ·) disjoint = board n m

-- lemmas about cardinalities

-- I am marking lemmas and theorems that could be @[simp] with `-- SIMP`

-- SIMP
lemma card_domino (domino : Domino) : (cells domino).card = 2 := by
  cases domino <;> trivial

-- SIMP
lemma card_board : (board n m).card = n * m := by
  unfold board
  rw [Finset.card_map]
  nth_rewrite 2 [←Finset.card_range n]
  nth_rewrite 2 [←Finset.card_range m]
  rw [←Finset.card_product]

-- SIMP
lemma card_tiling (tiling : DominoTiling n m) :
  2 * tiling.tiles.card = n * m := by
  have := tiling.tiles.card_disjiUnion (cells ·) tiling.disjoint
  simp only [tiling.union, card_board, card_domino, Finset.sum_const, smul_eq_mul] at this
  omega

-- classification of dominos

-- Finset.filter requires a decidable predicate Domino → Prop
-- for some reason, DecidablePred is synthesized automatically only for predicates of type Domino → Bool
-- we can convert Domino → Bool to Domino → Prop by an (implicit or explicit) cast

def horizontal : Domino → Bool
| Domino.H _ => true
| Domino.V _ => false

def vertical : Domino → Bool
| Domino.H _ => false
| Domino.V _ => true

lemma disjoint_hv : Disjoint (horizontal · : Domino → Prop) (vertical ·) := by
  apply Pi.disjoint_iff.mpr
  intros
  unfold horizontal vertical
  split <;> simp

lemma either_hv : ∀ x, horizontal x ∨ vertical x := by
  intros
  unfold horizontal vertical
  split <;> simp

-- decomposition of tiling into horizontal and vertical parts

def htiles (tiling : DominoTiling n m) : Finset Domino :=
  tiling.tiles.filter (horizontal ·)

def vtiles (tiling : DominoTiling n m) : Finset Domino :=
  tiling.tiles.filter (vertical ·)

lemma disjoint_hvtiles (tiling : DominoTiling n m) :
  Disjoint (htiles tiling) (vtiles tiling) := by
  unfold htiles vtiles
  apply Finset.disjoint_filter_filter'
  exact disjoint_hv

-- this could become part of Mathlib
lemma disjUnion_filter.{u} {α : Type u} (s : Finset α) {p q : α → Prop}
  [DecidablePred p] [DecidablePred q]
  (disjoint : Disjoint (s.filter p) (s.filter q))
  (either : ∀ x, p x ∨ q x) :
  Finset.disjUnion (s.filter p) (s.filter q) disjoint = s := by
  ext x
  simp [Finset.mem_disjUnion]
  constructor
  · rintro (h|h) <;> exact h.1
  intro hs
  cases either x
  · left; constructor; repeat assumption
  · right; constructor; repeat assumption

lemma union_hvtiles (tiling : DominoTiling n m) :
  Finset.disjUnion (htiles tiling) (vtiles tiling) (disjoint_hvtiles tiling) = tiling.tiles := by
  exact disjUnion_filter tiling.tiles (disjoint_hvtiles tiling) either_hv

lemma card_hvtiles (tiling : DominoTiling n m) :
  (htiles tiling).card + (vtiles tiling).card = tiling.tiles.card := by
  rw [←Finset.card_disjUnion _ _ (disjoint_hvtiles tiling), union_hvtiles]

-- lemmas for the main theorem

lemma x_sum_board :
  ∑ pt ∈ board n m, pt.x = n*(n-1)/2 * m := by
  calc
    ∑ pt ∈ board n m, pt.x =
      ∑ pt ∈ Finset.range n ×ˢ Finset.range m, pt.1 := by
      apply Finset.sum_map
    _ = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range m, x := by
      apply Finset.sum_product
    _ = ∑ y ∈ Finset.range m, ∑ x ∈ Finset.range n, x := by
      apply Finset.sum_comm
    _ = ∑ y ∈ Finset.range m, n*(n-1)/2 := by
      rw [Finset.sum_range_id]
    _ = (Finset.range m).card * (n*(n-1)/2) := by
      apply Finset.sum_const_nat
      intros; trivial
    _ = (n*(n-1)/2) * m := by
      rw [Finset.card_range, mul_comm]

lemma x_parity_tiling (tiling : DominoTiling n m) :
  n*(n-1)/2*m ≡ (htiles tiling).card [MOD 2] := by
  calc
    n*(n-1)/2*m % 2 = (∑ pt ∈ board n m, pt.x % 2) % 2 := by
      rw [←x_sum_board, Finset.sum_nat_mod]
    _ = (∑ tile ∈ tiling.tiles, ∑ pt ∈ cells tile, pt.x % 2) % 2 := by
      rw [←tiling.union, Finset.sum_disjiUnion]
    _ = (∑ tile ∈ tiling.tiles, (∑ pt ∈ cells tile, pt.x % 2) % 2) % 2 := by
      rw [Finset.sum_nat_mod]
    _ = (∑ tile ∈ tiling.tiles, (∑ pt ∈ cells tile, pt.x) % 2) % 2 := by
      congr; ext
      rw [←Finset.sum_nat_mod]
    _ = ((∑ tile ∈ htiles tiling, (∑ pt ∈ cells tile, pt.x) % 2) +
      (∑ tile ∈ vtiles tiling, (∑ pt ∈ cells tile, pt.x) % 2)) % 2 := by
      rw [←union_hvtiles tiling, Finset.sum_disjUnion (disjoint_hvtiles tiling)]
    _ = ((∑ tile ∈ htiles tiling, 1) +
              (∑ tile ∈ vtiles tiling, (∑ pt ∈ cells tile, pt.x) % 2)) % 2 := by
      congr 2
      apply Finset.sum_congr; trivial
      intro x hx
      cases htile : x with
      | H lft => simp [cells]; omega
      | V top => simp [htiles, htile, horizontal] at hx
    _ = ((∑ tile ∈ htiles tiling, 1) + (∑ tile ∈ vtiles tiling, 0)) % 2 := by
      congr 2
      apply Finset.sum_congr; trivial
      intro x hx
      cases htile : x with
      | H lft => simp [vtiles, htile, vertical] at hx
      | V top => simp [cells]; omega
    _ = (∑ i ∈ htiles tiling, 1) % 2 := by
      rw [Finset.sum_const_zero, add_zero]
    _ = ((htiles tiling).card * 1) % 2 := by
      rw [Finset.sum_const_nat ?const]
      intros; trivial
    _ = (htiles tiling).card % 2 := by
      rw [mul_one]

-- main theorem

theorem puzzle (tiling : DominoTiling 10 10) :
  (htiles tiling).card ≠ (vtiles tiling).card := by
  by_contra
  have := card_hvtiles tiling
  have := card_tiling tiling
  have card_htiles : (htiles tiling).card = 25 := by omega
  have := x_parity_tiling tiling
  simp [card_htiles, Nat.ModEq] at this
