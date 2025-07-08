import Mathlib.Data.Complex.Exponential
-- Natural Numbers are defined inductive
#print Nat

example : x + 10 = y + 5 -> x + 10 + 5 = y + 10 := by
  intro h
  rw [h]

def Odd' (n : Nat) := ∃ x : Nat, n = 2 * x + 1
def Even' (n : Nat) := ∃ x : Nat, n = 2 * x

example : Odd' 3 := by
  unfold Odd'
  use 1

lemma odd_plus_one : ∀ n : Nat, Odd' n -> Even' (n + 1) := by
  /- intro n ⟨x, hx⟩ -/
  intro n h
  obtain ⟨x, hx⟩ := h
  unfold Even'
  rw [hx]
  use (x + 1)
  ring
lemma even_plus_one : ∀ n : Nat, Even' n -> Odd' (n + 1) := by
  /- intro n ⟨x, hx⟩ -/
  intro n h
  obtain ⟨x, hx⟩ := h
  unfold Odd'
  rw [hx]
  use x

example : ∀ n : Nat, Odd' n ∨ Even' n := by
  intro n
  induction n
  case zero => 
    right
    use 0
  case succ n hn =>
    cases hn
    case inl h =>
      right
      apply odd_plus_one n h
    case inr h =>
      left
      apply even_plus_one n h

-- All opperators on Nat (e.g. +, *, /, ^) are defines as functions
def add_nat (a b : Nat) : Nat :=
  match a with
  | .zero => b
  | .succ a => add_nat a (.succ b)
#print Nat.add

def sum_n (n : Nat) : Nat :=
  match n with
  | .zero => 0
  | .succ x => sum_n x + n

lemma gauss_sum_x_2: ∀ n : Nat, sum_n n * 2 = n^2 + n := by 
  intro n 
  induction n
  case zero =>
    unfold sum_n
    simp
  case succ n hn =>
    simp [sum_n]
    ring_nf
    rw [hn]
    ring

lemma gauss_sum : ∀ n : Nat, sum_n n = (n^2 + n) / 2 := by
  intro n 
  refine Nat.eq_div_of_mul_eq_right ?_ ?_ -- apply?
  · simp
  · rw [mul_comm]
    exact gauss_sum_x_2 n

lemma help : ∀ n:Nat, 2∣(n + n^2) := by
  intro n
  cases Nat.even_or_odd n
  case inl h =>
    obtain ⟨c, hc⟩ := h
    use (c + 2*c^2)
    rw [hc]
    ring
  case inr h =>
    obtain ⟨c, hc⟩ := h
    use (1+c*3 + 2*c^2)
    rw [hc]
    ring

#eval 3/2
example : 3/2 + 3/2 ≠ (3+3)/2 := by
  --       1  +  1  ≠     6/2=3
  simp

example : ∀ n : Nat, sum_n n = (n^2 + n) / 2 := by
  intro n
  induction n
  case zero =>
    simp [sum_n]
  case succ n hn =>
    simp [sum_n]
    rw [hn]
    ring_nf
    calc
      1 + n + (n + n^2) / 2 = 2/2 + n + (n + n^2)/2 := by ring
      _ = ((1 + n)*2)/2 + (n + n^2)/2 := by simp
      _ = ((1 + n)*2 + (n + n^2)) / 2 := by
        have h' : 2∣(n+n^2) := help n
        exact Eq.symm (Nat.add_div_of_dvd_left h') -- apply?
      _ = (2 + n * 3 + n ^ 2) / 2 := by ring

inductive Leq : Nat -> Nat -> Prop where
  | rfl : ∀ a : Nat, Leq a a
  | step : ∀ a b : Nat, Leq a b -> Leq a (Nat.succ b)

#print Nat.le

example : 3 ≤ 6 := by
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.refl

example (x y z w : Nat) : x ≤ y -> y = z -> z ≤ w -> x ≤ w := by
  intro h h' h''
  calc 
    x ≤ y := by exact h
    _ ≤ w := by 
      rw [<- h'] at h''
      exact h''
    _ ≤ w := by rfl
