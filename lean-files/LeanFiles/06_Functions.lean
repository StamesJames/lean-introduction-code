import Mathlib.Data.Complex.Exponential

def surjective (f : X -> Y) := ∀ (y : Y), ∃ (x : X), f x = y

lemma lawvere (e : X -> (X -> Y)) : surjective e -> ∀ (f : Y -> Y), ∃ y, y = f y := by
   intros He f
   obtain ⟨x, Hx⟩ := He (fun x => f (e x x))
   use e x x
   apply congrFun at Hx
   specialize Hx x
   exact Hx


lemma cantor : ¬ (∃ (f : X -> (X -> Bool)), surjective f) := by
  intro ⟨f, Hf⟩
  obtain ⟨b, Hb⟩ := lawvere f Hf Bool.not
  cases b
  case false =>
    simp at Hb
  case true =>
    simp at Hb
