import Mathlib.Data.Set.Basic

class Poset (α : Type*) where
  le : α → α → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisym : ∀ {x y}, le x y → le y x → x = y

notation:20 x " ≤[" α "] " y => @Poset.le α _ x y

def monotone {L M : Type*} [Poset L] [Poset M] (f : L → M) : Prop :=
  ∀ x y, (x ≤[L] y) → (f x ≤[M] f y)
