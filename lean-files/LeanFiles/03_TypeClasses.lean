import Mathlib.Data.Complex.Exponential

#print Group

class Magma' (α : Type) : Type where
  add: α -> α -> α

class Group' (α : Type) extends Magma' α where
  assoc: ∀ a b c : α, add a (add b c) = add (add a b) c
  e: α
  l_id: ∀ x : α, add e x = x
  invert: α -> α
  l_inverse: ∀ x : α, add (invert x) x = e

instance NatGroup : Group' ℤ where
  add := sorry
  assoc := sorry
  e := sorry
  l_id := sorry
  invert := sorry
  l_inverse := sorry

infixr : 65 " ⊙ " => Magma'.add 
postfix : 80 "⁻¹" => Group'.invert

lemma Group'.l_cancle {α : Type} [Group' α] : ∀ a b c : α, (a ⊙ b = a ⊙ c) -> b = c := by
  sorry


lemma Group'.r_id {α : Type} [Group' α] : ∀ x : α,x ⊙ e = x := by
  sorry

lemma Group'.r_inverse {α : Type} [Group' α] : ∀ x : α, x ⊙ x⁻¹ = e := by
  sorry

lemma Group'.r_cancle {α : Type} [Group' α] : ∀ a b c : α, (b ⊙ a = c ⊙ a) -> b = c := by
  sorry

lemma Group'.inverse_idempotent {α : Type} [Group' α] : ∀ x : α,  x⁻¹⁻¹ = x := by
  sorry
  
