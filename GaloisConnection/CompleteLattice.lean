import GaloisConnection.Poset
import Mathlib.Data.Set.Basic

class CompleteLattice (L : Type*) extends Poset L where
  sup    : Set L → L
  inf    : Set L → L
  le_sup : ∀ {s x}, x ∈ s → le x (sup s)
  sup_le : ∀ {s y}, (∀ x ∈ s, le x y) → le (sup s) y
  inf_le : ∀ {s x}, x ∈ s → le (inf s) x
  le_inf : ∀ {s y}, (∀ x ∈ s, le y x) → le y (inf s)

notation:50 "⊔" s => CompleteLattice.sup s
notation:50 "⊓" s => CompleteLattice.inf s

-- a ⊆ b → sup a ≤ sup b
lemma sup_subset_to_le {L : Type*} [CompleteLattice L] {a b : Set L}
  (subset : a ⊆ b) :
  (⊔ a) ≤[L] (⊔ b) := by
  apply CompleteLattice.sup_le
  intros x x_in
  have : x ∈ b := subset x_in
  have : x ≤[L] ⊔ b := CompleteLattice.le_sup this
  exact this

-- x ≤ y -> sup {x, y} = y
lemma sup_pair_eq_right {L : Type*} [CompleteLattice L] {x y : L}
  (h : x ≤[L] y) :
  (⊔ {x, y}) = y := by
  have h1 : (⊔ {x, y}) ≤[L] y := by
    apply CompleteLattice.sup_le
    intros z z_in
    cases z_in
    case a.inl x_eq =>
      rw [x_eq]
      exact h
    case a.inr y_eq =>
      rw [y_eq]
      exact Poset.le_refl y
  have h2 : y ≤[L] ⊔ {x, y} := by
    apply CompleteLattice.le_sup
    right
    exact rfl
  exact Poset.le_antisym h1 h2

-- x ≤ y -> inf {x, y} = x
lemma inf_pair_eq_left {L : Type*} [CompleteLattice L] {x y : L}
  (h : x ≤[L] y) :
  (⊓ {x, y}) = x := by
  have h1 : x ≤[L] (⊓ {x, y}) := by
    apply CompleteLattice.le_inf
    intros z z_in
    cases z_in
    case a.inl x_eq =>
      rw [x_eq]
      exact Poset.le_refl x
    case a.inr y_eq =>
      rw [y_eq]
      exact h
  have h2 : (⊓ {x, y}) ≤[L] x := by
    apply CompleteLattice.inf_le
    left
    exact rfl
  exact Poset.le_antisym h2 h1

-- L が完備束のとき
-- 最大元 ⊤L と最小元 ⊥L が存在する
def top_of_complete_lattice {L : Type*} [CompleteLattice L] :
  L := ⊔ (Set.univ : Set L)
def bottom_of_complete_lattice {L : Type*} [CompleteLattice L] :
  L := ⊓ (Set.univ : Set L)
notation:50 "⊤[" L "]" => @top_of_complete_lattice L _
notation:50 "⊥[" L "]" => @bottom_of_complete_lattice L _

-- ⊥L は L の最小元
theorem bottom_is_le_of_complete_lattice {L : Type*} [CompleteLattice L] :
  ∀ l : L, ⊥[L] ≤[L] l := by
  intro l
  have : l ∈ (Set.univ : Set L) := Set.mem_univ l
  have : ⊥[L] ≤[L] l := CompleteLattice.inf_le this
  exact this

-- ⊤L は L の最大元
theorem top_is_ge_of_complete_lattice {L : Type*} [CompleteLattice L] :
  ∀ l : L, l ≤[L] ⊤[L] := by
  intro l
  have : l ∈ (Set.univ : Set L) := Set.mem_univ l
  have : l ≤[L] ⊤[L] := CompleteLattice.le_sup this
  exact this
