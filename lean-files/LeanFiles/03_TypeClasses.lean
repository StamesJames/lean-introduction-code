import Mathlib.Data.Complex.Exponential

#print Group

class Magma' (α : Type) : Type where
  add: α -> α -> α
infixr : 65 " ⊙ " => Magma'.add 

class Group' (α : Type) extends Magma' α where
  assoc: ∀ a b c : α,  a ⊙ (b ⊙ c) =  (a ⊙ b) ⊙ c
  e: α
  l_id: ∀ x : α, e ⊙ x = x
  invert: α -> α
  l_inverse: ∀ x : α, (invert x) ⊙ x = e
postfix : 80 "⁻¹" => Group'.invert

instance NatGroup : Group' ℤ where
  add := sorry
  assoc := sorry
  e := sorry
  l_id := sorry
  invert := sorry
  l_inverse := sorry

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
  
