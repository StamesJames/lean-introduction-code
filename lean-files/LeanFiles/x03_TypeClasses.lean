import Mathlib.Data.Complex.Exponential

#print Group

class Magma' (α : Type) : Type where
  add: α -> α -> α

infixr : 65 " ⊙ " => Magma'.add 
postfix : 80 "⁻¹" => Group'.invert

class Group' (α : Type) extends Magma' α where
  assoc: ∀ a b c : α,  a ⊙ (b ⊙ c) = (a ⊙ b) ⊙ c
  e: α
  l_id: ∀ x : α, e ⊙ x = x
  invert: α -> α
  l_inverse: ∀ x : α, (invert x) ⊙ x = e

instance NatGroup : Group' ℤ where
  add a b := a + b
  assoc := by
    intro a b c
    ring
  e := 0
  l_id := by
    intro x
    simp
  invert x := -x
  l_inverse := by 
    intro x
    simp


lemma Group'.l_cancle {α : Type} [Group' α] : ∀ a b c : α, (a ⊙ b = a ⊙ c) -> b = c := by
  intro a b c h
  have h1 : a⁻¹ ⊙ (a ⊙ b) =  a⁻¹ ⊙ (a ⊙ c) := by rw [h]
  simp [assoc] at h1
  simp [l_inverse] at h1 
  simp [l_id] at h1
  assumption


lemma Group'.r_id {α : Type} [Group' α] : ∀ x : α,x ⊙ e = x := by
  intro x
  apply Group'.l_cancle (x⁻¹)
  simp [assoc, l_inverse, l_id]

lemma Group'.r_inverse {α : Type} [Group' α] : ∀ x : α, x ⊙ x⁻¹ = e := by
  intro x 
  apply Group'.l_cancle (x⁻¹)
  simp [assoc, l_inverse, l_id, r_id]

lemma Group'.r_cancle {α : Type} [Group' α] : ∀ a b c : α, (b ⊙ a = c ⊙ a) -> b = c := by
  intro a b c h
  have h1 : (b ⊙ a) ⊙ a⁻¹ = (c ⊙ a) ⊙ a⁻¹ := by rw [h]
  simp [<- assoc, r_inverse, r_id] at h1
  assumption

lemma Group'.inverse_idempotent {α : Type} [Group' α] : ∀ x : α,  x⁻¹⁻¹ = x := by
  intro x
  apply Group'.l_cancle (x⁻¹)
  simp [l_inverse, r_inverse]
  
