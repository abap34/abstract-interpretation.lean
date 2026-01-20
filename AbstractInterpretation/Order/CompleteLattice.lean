import AbstractInterpretation.Order.Poset
import Mathlib.Data.Set.Basic
import AbstractInterpretation.Order.Poset

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


-- Tarski の不動点定理により、完備束上の単調関数は最小不動点を持ち，
--   lfp F = inf {x | F x ≤ x}
def lfp {L : Type*} [CompleteLattice L] (f : L → L) : L :=
  ⊓ {x | f x ≤[L] x}

axiom Tarskis_fixed_point_theorem_lfp {L : Type*} [CompleteLattice L]
  (f : L → L) (f_mon : monotone f) :
  f (lfp f) = lfp f


-- 同様に，
--   gfp F = sup {x | x ≤ F x}
def gfp {L : Type*} [CompleteLattice L] (f : L → L) : L :=
  ⊔ {x | x ≤[L] f x}

axiom Tarskis_fixed_point_theorem_gfp {L : Type*} [CompleteLattice L]
  (f : L → L) (f_mon : monotone f) :
  f (gfp f) = gfp f


-- 前不動点は最小不動点より大きい
theorem prefixed_point_ge_lfp {L : Type*} [CompleteLattice L]
  (f : L → L) (x : L) (h : f x ≤[L] x) :
  lfp f ≤[L] x := by
  unfold lfp
  apply CompleteLattice.inf_le
  exact h

-- 後不動点は最大不動点より小さい
theorem postfixed_point_le_gfp {L : Type*} [CompleteLattice L]
  (f : L → L) (x : L) (h : x ≤[L] f x) :
  x ≤[L] gfp f := by
  unfold gfp
  apply CompleteLattice.le_sup
  exact h


-- (L, ≤) が完備束のとき
-- x ≤' y ↔ y ≤ y で定義される順序関係 ≤' を L に入れても
-- (L, ≤') も完備束になる
def dual_complete_lattice {L : Type*} [CompleteLattice L] :
  CompleteLattice L := {
  toPoset := dual_poset L
  sup := fun s => ⊓ s
  inf := fun s => ⊔ s
  le_sup := fun h => CompleteLattice.inf_le h
  sup_le := fun h => CompleteLattice.le_inf h
  inf_le := fun h => CompleteLattice.le_sup h
  le_inf := fun h => CompleteLattice.sup_le h
}


-- (L ≤) の lfp は (L ≤') の gfp に等しい
theorem lfp_eq_gfp_dual {L : Type*} [inst : CompleteLattice L]
  (f : L → L) (_f_mon : monotone f) :
  @lfp L inst f = @gfp L dual_complete_lattice f := by
  rfl

-- (L ≤) の gfp は (L ≤') の lfp に等しい
theorem gfp_eq_lfp_dual {L : Type*} [inst : CompleteLattice L]
  (f : L → L) (_f_mon : monotone f) :
  @gfp L inst f = @lfp L dual_complete_lattice f := by
  rfl
