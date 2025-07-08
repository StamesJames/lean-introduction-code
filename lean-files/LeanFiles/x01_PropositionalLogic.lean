-- Proofs as terms
-- Modus Ponens
example : 
           A  ->              (A -> B) -> B        :=
  fun (a : A) => fun (a_to_b : A -> B) => a_to_b a

-- tactic mode
example : A -> (A -> B) -> B := by
  intro a a_to_b
  apply a_to_b
  apply a


-- And and the product type
example : A -> B -> A ∧ B := by
  intro ha hb 
  apply And.intro -- the goal gets split in two
  · apply ha
  · assumption -- assumption searches all assumptions for the goal

-- destructing an And
example : (A ∧ B) -> (A -> B -> C) -> C := by
  intro a_and_b a_to_b_to_c
  obtain ⟨a, b⟩ := a_and_b
  apply a_to_b_to_c
  · apply a
  · apply b

-- this is done by match statements 
example : 
                A ∧ B ->                   (A -> B -> C) -> C :=
  fun a_and_b : A ∧ B => fun a_to_b_to_c : (A -> B -> C) => 
    match a_and_b with
    | And.intro a b => a_to_b_to_c a b

-- Or and the tagged sum type
example : A -> A ∨ B := by
  intro a
  left
  apply a
example : B -> A ∨ B := by
  intro b
  right
  apply b

-- destructing an Or
example {C : Prop} : (A ∨ B) -> (A -> C) -> (B -> C) -> C := by
  intro a_or_b a_to_c b_to_c
  rcases a_or_b with a | b
  · apply a_to_c a
  · apply b_to_c b

-- Negation 
example : A -> ¬¬A := by
  intro a na
  apply na
  apply a 

example : (B -> A) -> B -> ¬A -> C := by
  intro b_to_a b na
  specialize na (b_to_a b)
  cases na
