import Mathlib.Data.Set.Basic

class Poset (α : Type*) where
  le : α → α → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisym : ∀ {x y}, le x y → le y x → x = y

notation:20 x " ≤[" α "] " y => @Poset.le α _ x y

def monotone {L M : Type*} [Poset L] [Poset M] (f : L → M) : Prop :=
  ∀ x y, (x ≤[L] y) → (f x ≤[M] f y)

-- (L, ≤) が poset のとき
-- x ≤' y ↔ y ≤ x と定義した 関係 ≤' も poset になる
def dual_poset (L : Type*) [Poset L] : Poset L := {
  le := fun x y => y ≤[L] x
  le_refl := fun x => Poset.le_refl x
  le_trans := fun {x y z} hxy hyz => Poset.le_trans hyz hxy
  le_antisym := fun {x y} hxy hyx => Poset.le_antisym hyx hxy
}
