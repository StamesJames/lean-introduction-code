import Mathlib.Data.Complex.Exponential
-- Natural Numbers are defined inductive
#print Nat

example : x + 10 = y + 5 -> x + 10 + 5 = y + 10 := by
  sorry

def Odd' (n : Nat) := ∃ x : Nat, n = 2 * x + 1
def Even' (n : Nat) := ∃ x : Nat, n = 2 * x

example : Odd' 3 := by
  sorry

lemma odd_plus_one : ∀ n : Nat, Odd' n -> Even' (n + 1) := by
  sorry
lemma even_plus_one : ∀ n : Nat, Even' n -> Odd' (n + 1) := by
  sorry

example : ∀ n : Nat, Odd' n ∨ Even' n := by
  sorry

-- All opperators on Nat (e.g. +, *, /, ^) are defines as functions
def add_nat (a b : Nat) : Nat :=
  sorry
#print Nat.add

def sum_n (n : Nat) : Nat :=
  sorry

lemma gauss_sum_x_2 : ∀ n : Nat, sum_n n * 2 = n^2 + n := by 
  sorry

lemma gauss_sum : ∀ n : Nat, sum_n n = (n^2 + n) / 2 := by
  sorry

lemma help : ∀ n:Nat, 2∣(n + n^2) := by
  sorry


example : ∀ n : Nat, sum_n n = (n^2 + n) / 2 := by
  sorry

inductive Leq : Nat -> Nat -> Prop where

#print Nat.le

example : 3 ≤ 6 := by
  sorry

example (x y z w : Nat) : x ≤ y -> y = z -> z ≤ w -> x ≤ w := by
  sorry
