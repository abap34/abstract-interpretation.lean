import Mathlib.Data.Set.Basic

class Poset (α : Type*) where
  le : α → α → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisym : ∀ {x y}, le x y → le y x → x = y

notation:20 x " ≤[" α "] " y => @Poset.le α _ x y

def monotone {L M : Type*} [Poset L] [Poset M] (f : L → M) : Prop :=
  ∀ x y, (x ≤[L] y) → (f x ≤[M] f y)

structure GaloisConnection {L M : Type*} [Poset L] [Poset M]
  (alpha : L → M) (gamma : M → L) : Prop where
  alpha_mon : monotone alpha
  gamma_mon : monotone gamma
  unit  : ∀ l, l ≤[L] gamma (alpha l)
  counit: ∀ m, alpha (gamma m) ≤[M] m

-----------------------------------------------
-- Galois 接続 <-> Adjunction
-----------------------------------------------m
structure Adjunction {L M : Type*} [Poset L] [Poset M]
  (alpha : L → M) (gamma : M → L) : Prop where
  adj : ∀ l m, (l ≤[L] gamma m) ↔ (alpha l ≤[M] m)

lemma galois_to_adjunction {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma) :
  Adjunction alpha gamma := {
    adj := by
      intro l m
      constructor
      case mp =>
        intros h
        have h1 : alpha l ≤[M] alpha (gamma m) := gc.alpha_mon l (gamma m) h
        have h2 : alpha (gamma m) ≤[M] m := gc.counit m
        apply Poset.le_trans h1 h2
      case mpr =>
        intros h
        have h1 : l ≤[L] gamma (alpha l) := gc.unit l
        have h2 : gamma (alpha l) ≤[L] gamma m := gc.gamma_mon (alpha l) m h
        apply Poset.le_trans h1 h2
  }

lemma adjunction_to_unit {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma : M → L}
  (adj : Adjunction alpha gamma) (l : L) :
  l ≤[L] gamma (alpha l) := by
  have h : alpha l ≤[M] alpha l := Poset.le_refl (alpha l)
  have h1 : l ≤[L] gamma (alpha l) := (adj.adj l (alpha l)).mpr h
  exact h1

lemma adjunction_to_counit {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma : M → L}
  (adj : Adjunction alpha gamma) (m : M) :
  alpha (gamma m) ≤[M] m := by
  have h : gamma m ≤[L] gamma m := Poset.le_refl (gamma m)
  have h1 : alpha (gamma m) ≤[M] m := (adj.adj (gamma m) m).mp h
  exact h1

lemma adjunction_to_galois {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma : M → L}
  (adj : Adjunction alpha gamma) :
  GaloisConnection alpha gamma := {
    alpha_mon := by
      intros l1 l2 h
      have h1 : l2 ≤[L] gamma (alpha l2) := adjunction_to_unit adj l2
      have h2 : l1 ≤[L] gamma (alpha l2) := Poset.le_trans h h1
      have h3 : alpha l1 ≤[M] alpha l2 := (adj.adj l1 (alpha l2)).mp h2
      exact h3,
    gamma_mon := by
      intros m1 m2 h
      have h1 : alpha (gamma m1) ≤[M] m1 := adjunction_to_counit adj m1
      have h2 : alpha (gamma m1) ≤[M] m2 := Poset.le_trans h1 h
      have h3 : gamma m1 ≤[L] gamma m2 := (adj.adj (gamma m1) m2).mpr h2
      exact h3,
    unit := adjunction_to_unit adj,
    counit := adjunction_to_counit adj
  }

theorem adjunction_iff_galois {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma : M → L} :
  Adjunction alpha gamma ↔ GaloisConnection alpha gamma :=
  ⟨adjunction_to_galois, galois_to_adjunction⟩


-----------------------------------------------
-- α ∘ γ ∘ α = α, γ ∘ α ∘ γ = γ
-----------------------------------------------
theorem galois_alpha_idem {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma) (l : L) :
  alpha (gamma (alpha l)) = alpha l := by
  have adj : Adjunction alpha gamma := galois_to_adjunction gc
  have h1 : l ≤[L] gamma (alpha l) := gc.unit l
  have h2 : alpha l ≤[M] alpha (gamma (alpha l)) := gc.alpha_mon l (gamma (alpha l)) h1
  have h3 : gamma (alpha l) ≤[L] gamma (alpha l) := Poset.le_refl (gamma (alpha l))
  have h4 : alpha (gamma (alpha l)) ≤[M] alpha l := (adj.adj (gamma (alpha l)) (alpha l)).mp h3
  have h5 : alpha (gamma (alpha l)) = alpha l := Poset.le_antisym h4 h2
  exact h5

theorem galois_gamma_idem {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma) (m : M) :
  gamma (alpha (gamma m)) = gamma m := by
  have adj : Adjunction alpha gamma := galois_to_adjunction gc
  have h1 : alpha (gamma m) ≤[M] m := gc.counit m
  have h2 : gamma (alpha (gamma m)) ≤[L] gamma m := gc.gamma_mon (alpha (gamma m)) m h1
  have h3 : alpha (gamma m) ≤[M] alpha (gamma m) := Poset.le_refl (alpha (gamma m))
  have h4 : gamma m ≤[L] gamma (alpha (gamma m)) := (adj.adj (gamma m) (alpha (gamma m))).mpr h3
  have h5 : gamma (alpha (gamma m)) = gamma m := Poset.le_antisym h2 h4
  exact h5

-----------------------------------------------
-- α は完全加法的, γ は完全乗法的
-----------------------------------------------
class CompleteLattice (L : Type*) extends Poset L where
  sup    : Set L → L
  inf    : Set L → L
  le_sup : ∀ {s x}, x ∈ s → le x (sup s)
  sup_le : ∀ {s y}, (∀ x ∈ s, le x y) → le (sup s) y
  inf_le : ∀ {s x}, x ∈ s → le (inf s) x
  le_inf : ∀ {s y}, (∀ x ∈ s, le y x) → le y (inf s)

notation:50 "⊔" s => CompleteLattice.sup s
notation:50 "⊓" s => CompleteLattice.inf s

-- alpha (sup L') ≤ ub  <->  sup (alpha '' L') ≤ ub
lemma alpha_preserve_ub {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma) (ub : M) (L' : Set L) :
  (alpha (⊔ L') ≤[M] ub) ↔ ((⊔ (alpha '' L')) ≤[M] ub) := by
  constructor
  case mp =>
    intros h
    have adj : Adjunction alpha gamma := galois_to_adjunction gc
    have h1 : (⊔ L') ≤[L] gamma ub := (adj.adj (⊔ L') ub).mpr h
    have h2 : ∀ l ∈ L', l ≤[L] gamma ub := by
      intros l l_in
      have : l ≤[L] ⊔ L' := CompleteLattice.le_sup l_in
      have : l ≤[L] gamma ub := Poset.le_trans this h1
      exact this
    have h3 : ∀ l ∈ L', alpha l ≤[M] ub := by
      intros l l_in
      have : alpha l ≤[M] ub := (adj.adj l ub).mp (h2 l l_in)
      exact this
    have h4 : ∀ m ∈ (alpha '' L'), m ≤[M] ub := by
      intro m m_in
      have : m ∈ alpha '' L' ↔ ∃ l ∈ L', alpha l = m := (Set.mem_image alpha L' m)
      have : ∃ l ∈ L', alpha l = m := this.mp m_in
      obtain ⟨l, l_in, eq⟩ := this
      rw [show m = alpha l from eq.symm]
      have : alpha l ≤[M] ub := h3 l l_in
      exact this
    have h5 : (⊔ (alpha '' L')) ≤[M] ub := CompleteLattice.sup_le h4
    exact h5
  case mpr =>
    intros h
    have adj : Adjunction alpha gamma := galois_to_adjunction gc
    have h1 : ∀ m ∈ (alpha '' L'), m ≤[M] ub := by
      have : ∀ m ∈ (alpha '' L'), m ≤[M] ⊔ (alpha '' L') := by
        intros m m_in
        have : m ≤[M] ⊔ (alpha '' L') := CompleteLattice.le_sup m_in
        exact this
      intros m m_in
      have : m ≤[M] ⊔ (alpha '' L') := this m m_in
      have : m ≤[M] ub := Poset.le_trans this h
      exact this
    have h2 : ∀ l ∈ L', alpha l ≤[M] ub := by
      intros l l_in
      have : alpha l ∈ (alpha '' L') := Set.mem_image_of_mem alpha l_in
      have : alpha l ≤[M] ub := h1 (alpha l) this
      exact this
    have h3 : ∀ l ∈ L', l ≤[L] gamma ub := by
      intros l l_in
      have : alpha l ≤[M] ub := h2 l l_in
      have : l ≤[L] gamma ub := (adj.adj l ub).mpr this
      exact this
    have h4 : (⊔ L') ≤[L] gamma ub := CompleteLattice.sup_le h3
    have h5 : alpha (⊔ L') ≤[M] ub := (adj.adj (⊔ L') ub).mp h4
    exact h5

-- α は完全加法的
theorem galois_to_alpha_is_additive {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma) :
  ∀ L' : Set L, alpha (⊔ L') = (⊔ (alpha '' L')) := by
  intros L'
  have h1 : alpha (⊔ L') ≤[M] ⊔ (alpha '' L') := by
    apply (alpha_preserve_ub gc (⊔ (alpha '' L')) L').mpr
    apply Poset.le_refl (⊔ (alpha '' L'))
  have h2 : (⊔ (alpha '' L')) ≤[M] alpha (⊔ L') := by
    apply (alpha_preserve_ub gc (alpha (⊔ L')) L').mp
    apply Poset.le_refl (alpha (⊔ L'))
  have h3 : alpha (⊔ L') = (⊔ (alpha '' L')) := Poset.le_antisym h1 h2
  exact h3

-----------------------------------------------
-- γ は α によって一意に定まる．
-- とくに L, M が完備束のとき
-- gamma (m) = sup { l | alpha(l) ≤ m }
-----------------------------------------------
theorem galois_gamma_uniqueness {L M : Type*} [Poset L] [Poset M]
  {alpha : L → M} {gamma1 gamma2 : M → L}
  (gc1 : GaloisConnection alpha gamma1)
  (gc2 : GaloisConnection alpha gamma2) :
  ∀ m : M, gamma1 m = gamma2 m := by
  intros m
  have adj1 : Adjunction alpha gamma1 := galois_to_adjunction gc1
  have adj2 : Adjunction alpha gamma2 := galois_to_adjunction gc2
  have h1 : ∀ m, gamma1 m ≤[L] gamma2 m := by
    intros m
    have : alpha (gamma1 m) ≤[M] m := gc1.counit m
    have : gamma1 m ≤[L] gamma2 m := (adj2.adj (gamma1 m) m).mpr this
    exact this
  have h2 : ∀ m, gamma2 m ≤[L] gamma1 m := by
    intros m
    have : alpha (gamma2 m) ≤[M] m := gc2.counit m
    have : gamma2 m ≤[L] gamma1 m := (adj1.adj (gamma2 m) m).mpr this
    exact this
  have h3 : gamma1 m = gamma2 m := Poset.le_antisym (h1 m) (h2 m)
  exact h3

def gamma_by_alpha {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  (alpha : L → M) :
  M → L := fun m => ⊔ { l | alpha l ≤[M] m }

-- a ⊆ b → sup a ≤ sup b
lemma sup_subset_to_le {L : Type*} [CompleteLattice L] {a b : Set L}
  (subset : a ⊆ b) :
  (⊔ a) ≤[L] (⊔ b) := by
  apply CompleteLattice.sup_le
  intros x x_in
  have : x ∈ b := subset x_in
  have : x ≤[L] ⊔ b := CompleteLattice.le_sup this
  exact this

lemma gamma_by_alpha_mono {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  (alpha : L → M) :
  monotone (gamma_by_alpha alpha) := by
    intros m1 m2 h
    have : { l | alpha l ≤[M] m1 } ⊆ { l | alpha l ≤[M] m2 } := by
      intros l l_in
      have : alpha l ≤[M] m1 := l_in
      have : alpha l ≤[M] m2 := Poset.le_trans this h
      apply Set.mem_setOf.mpr
      exact this
    have : gamma_by_alpha alpha m1 ≤[L] gamma_by_alpha alpha m2 :=
      sup_subset_to_le this
    exact this

lemma gamma_by_alpha_unit {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  (alpha : L → M) :
  ∀ l, l ≤[L] (gamma_by_alpha alpha) (alpha l) := by
    intro l
    have : l ∈ { l | alpha l ≤[M] alpha l } := by
      apply Set.mem_setOf.mpr
      apply Poset.le_refl (alpha l)
    have : l ≤[L] (gamma_by_alpha alpha) (alpha l) := CompleteLattice.le_sup this
    exact this

def determine_gamma_by_alpha {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma) :
  GaloisConnection alpha (gamma_by_alpha alpha) := {
    alpha_mon := gc.alpha_mon,
    gamma_mon := gamma_by_alpha_mono alpha,
    unit := gamma_by_alpha_unit alpha,
    counit := by
      intro m
      have : (⊔ (alpha '' { l | alpha l ≤[M] m })) ≤[M] m := by
        apply CompleteLattice.sup_le
        intros m' m'_in
        obtain ⟨l, l_in, eq⟩ := m'_in
        rw [show m' = alpha l from eq.symm]
        have : alpha l ≤[M] m := Set.mem_setOf.mp l_in
        exact this
      have : alpha (⊔ { l | alpha l ≤[M] m }) ≤[M] m := by
        apply (alpha_preserve_ub gc m { l | alpha l ≤[M] m }).mpr
        exact this
      exact this
  }

theorem galois_gamma_by_alpha {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma) :
  ∀ m : M, gamma m = gamma_by_alpha alpha m := by
  intros m
  have gc' : GaloisConnection alpha (gamma_by_alpha alpha) :=
    determine_gamma_by_alpha gc
  have h : ∀ m, gamma m = (gamma_by_alpha alpha) m := galois_gamma_uniqueness gc gc'
  exact h m

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
  have : (⊔ {x, y}) = y := Poset.le_antisym h1 h2
  exact this

theorem alpha_additive_to_galois {L M : Type*} [CompleteLattice L] [CompleteLattice M] {alpha : L → M}
  (alpha_additive : ∀ L' : Set L, alpha (⊔ L') = (⊔ (alpha '' L'))) :
  GaloisConnection alpha (gamma_by_alpha alpha) := {
    alpha_mon := by
      intros l1 l2 h
      have : (⊔ {l1, l2}) = l2 := sup_pair_eq_right h
      have : alpha (⊔ {l1, l2}) = alpha l2 := by rw [this]
      have h1 : alpha l2 = alpha (⊔ {l1, l2}) := Eq.symm this
      have h2 : alpha (⊔ {l1, l2}) = (⊔ (alpha '' {l1, l2})) := alpha_additive {l1, l2}
      have h3 : alpha l2 = (⊔ (alpha '' {l1, l2})) := Eq.trans h1 h2
      have : alpha l1 ∈ (alpha '' {l1, l2}) := by
        apply Set.mem_image_of_mem alpha
        left
        exact rfl
      have : alpha l1 ≤[M] ⊔ (alpha '' {l1, l2}) := CompleteLattice.le_sup this
      have : alpha l1 ≤[M] alpha l2 := by
        rw [h3]
        exact this
      exact this
    gamma_mon := gamma_by_alpha_mono alpha,
    unit := gamma_by_alpha_unit alpha,
    counit := by
      intro m
      have h1 : (⊔ (alpha '' { l | alpha l ≤[M] m })) ≤[M] m := by
        apply CompleteLattice.sup_le
        intros m' m'_in
        obtain ⟨l, l_in, eq⟩ := m'_in
        rw [show m' = alpha l from eq.symm]
        have : alpha l ≤[M] m := Set.mem_setOf.mp l_in
        exact this
      have : alpha (⊔ { l | alpha l ≤[M] m }) ≤[M] m := by
        have : alpha (⊔ { l | alpha l ≤[M] m }) = (⊔ (alpha '' { l | alpha l ≤[M] m })) :=
          alpha_additive { l | alpha l ≤[M] m }
        rw [this]
        exact h1
      exact this
  }
