-- source: https://github.com/lftcm2023/lftcm2023/blob/master/LftCM/C11_Algebraic_Geometry/S11A_Algebraic_Geometry_exercises_withSols.lean
import Mathlib.Tactic

set_option autoImplicit false

variable {R : Type*} [Semiring R] {r : R}

open Polynomial

#check Polynomial R
#check R[X]
#check r
#check C r
#check (C r * X^3 + X^2 + C r: R[X])

#check ℕ[X]
#check ℤ[X]

example : ((X + 1) ^ 2 : R[X]) = X ^ 2 + 2 * X + 1 := by
  rw [sq, mul_add, add_mul, add_mul, ← sq, add_assoc, add_assoc]
  simp
  congr 1  -- matches the common parts of the expressions
  rw [← add_assoc, two_mul]

variable {S} [CommSemiring S] in
example : ((X + C 1) ^ 2 : S[X]) = X ^ 2 + 2 * X + 1 := by
  simp
  ring

noncomputable
example {R} [CommRing R] (p : R[X]) : R[X] →+* R[X] :=
(aeval p).toRingHom

example [Nontrivial R] : natDegree (X + C 1) = 1 := by
  -- simp  --uncomment this `simp` and `exact?` fails
  exact?
