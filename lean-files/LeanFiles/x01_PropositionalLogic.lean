-- Proofs as terms
-- Modus Ponens
example : 
           A  ->              (A -> B) -> B        :=
  sorry

-- tactic mode
example : A -> (A -> B) -> B := by
  sorry


-- And and the product type
example : A -> B -> A ∧ B := by
  sorry

-- destructing an And
example : (A ∧ B) -> (A -> B -> C) -> C := by
  sorry

-- this is done by match statements 
example : 
                A ∧ B ->                   (A -> B -> C) -> C :=
  sorry

-- Or and the tagged sum type
example : A -> A ∨ B := by
  sorry
example : B -> A ∨ B := by
  sorry

-- destructing an Or
example {C : Prop} : (A ∨ B) -> (A -> C) -> (B -> C) -> C := by
  sorry

-- Negation 
example : A -> ¬¬A := by
  sorry

example : (B -> A) -> B -> ¬A -> C := by
  sorry
