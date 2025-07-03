#import "@preview/polylux:0.4.0": *
#import "@preview/metropolis-polylux:0.1.0" as metropolis
#import metropolis: new-section, focus
#import "@preview/codly:1.3.0": *
#show: codly-init.with()
#show raw: set text(font: "CaskaydiaCove NFM", ligatures: true)
#set raw(syntaxes: "Coq.sublime-syntax")
#import "@preview/codly-languages:0.1.8": *
#codly(languages: codly-languages)
#codly(
  languages: (
    coq: (
      name: "Rocq",
      icon: box(
        image("icon-rocq-orange.svg", height: 0.9em),
        baseline: 0.05em,
        inset: 0pt,
        outset: 0pt,
      )
        + h(0.3em),
      color: rgb("#790303"),
    ),
    ..codly-languages,
  ),
)
#import "@preview/curryst:0.5.0": *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/fontawesome:0.5.0": *

#show: metropolis.setup.with(
  text-font: "Roboto",
  math-font: "New Computer Modern Math",
  text-size: 23pt,
  footer: [Christian Benedict Smit - Introduction to Proof Assistants],
)

#slide[
  #grid(align: center, gutter: 1em, columns: (
      1fr,
      2fr,
      1fr,
    ))[][#set text(
      size: 1.5em,
    ); Introduction to Proof Assistants][#image("tuda_logo_RGB.svg")][][Using Lean4][][][Christian Benedict Smit][
    #datetime.today().display()
  ]
]


#slide[
  = My Introduction
  - 2017: B.Sc. Biology - Ruhr University Bochum
  - 2021: B.Sc. Computer Science - TU Dortmund
  - 2025: M.Sc. Computer Science - TU Dortmund
    - Masters Thesis: "Congruence Closure in the presence of dependent types"
    - Implementations in Rocq (formerly known as Coq)
  - 2025: Start of my Ph.D. in Computer Science
    - TU Darmstadt
    - Software Technology Group of Mira Mezini
  - For my Ph.D. I started using Lean4
]

#slide[
  = What is Proof Assistants
  - Programs to write proofs
  - Proofs are programs in a typed purely functional programming language
    - Functional meaning the main abstraction are functions
    - Purely meaning those functions are mathematical functions
  - Using constructive mathematics with intuitionistic logic
  - Underlying is the Calculus of Inductive Constructions (CIC)
    - A typed Lambda Calculus
    - Types can also contain terms
  - A small trusted kernel does the type checking
]

#slide[
  = Motivation to use Proof Assistants
  - Preventing errors in proofs
    - 1852: Francis Guthrie proposes the Four Color Theorem
    - 1879: Alfred Kempe proposes a proof for the Four Color Theorem
    - 1890: Percy Heawood shows, that Kempe's proof has faults
  - Proof automation
    - 1976: Kenneth Appel and Wolfgang Haken proof the Four Color Theorem computer aided
    - 2005: Georges Gonthier formalizes a proof for the Four Color Theorem in Coq
  - Preventing Bugs in Software
]

#slide[
  = My Masters Thesis
  #set text(size: 0.8em)
  ```coq
  Goal forall (A: Type) (a a' b: A), (a, b) = (a', b) -> a = a'.
  Proof.
      congruence.
  Qed.
  ```
  ```coq
  Inductive Vector A : nat -> Type :=
  | nil : Vector A 0
  | cons : forall (h: A) {n: nat}, Vector A n -> Vector A (S n).
  ```
  ```coq
  Goal forall (A: Type) (n: nat) (h: A) (t t': Vector A n),
    cons h t = cons h t' -> t = t'.
  Proof.
    congruence.
  ```
]

#slide[
  #columns(2)[
    = Lambda Calculus
    == untyped
    Let $M, N$ be other lambda terms
    / $x$: : Variable
    / $(lambda x. N)$: : Lambda Abstraction
    / $(M N)$: : Application
    == typed
    / $x:T$: : Variable
    / $(lambda x:T. N)$: : Lambda Abstraction
    / $(M N)$: : Application
    #colbreak()

    == reduction
    $((lambda x. M ) N) arrow_beta (M[x\/N])$
    == typing
    #v(-1.5cm)
    $$
      #prooftree(rule(name: smallcaps[Var])[$Gamma, x:T tack x:T$]) \
      #v(-1.5cm)
      #prooftree(rule(name: smallcaps[Abs])[$Gamma tack lambda x:T_1.t_2 : T_1 arrow T_2$][$Gamma, x:T_1 tack t_2 : T_2$]) \
      #v(-1.5cm)
      #prooftree(rule(name: smallcaps[App])[$Gamma tack t_1 thin t_2 : T_12$][$Gamma tack t_1 : T_2 arrow T_12$][$Gamma tack t_2 : T_2$])
    $$
  ]
]

#slide[
  = Curry-Howard correspondence
  Types $approx$ Propositions \
  Terms $approx$ Proofs \
  Let $"Prop"$ be the Type of propositions
  #table(columns: (auto,auto, 1fr), table.header([*logic*], [*programming*], [*explanation*]),
    [$A and B$ ],[$A times B$], [product type],
    [$A or B$], [$A plus.circle B$], [tagged sum type],
    [$A arrow.double B$], [$A arrow B$ or $forall \_:A, B$ ], [function type],
    [$forall x:T, P$], [$forall x:T, P$], [dependent function type],
    [$exists x:T, P$], [$(x:T, P thin x)$], [dependent pair type],
    [$"True"$], [$"Unit"$ also called $"True"$], [Type with the one element $()$],
    [$"False"$], [$"Void"$ also called $"False"$], [ Type with no elements],
    [$not A$], [$A arrow "False"$], [function to $"False"$]
  )
]


#slide[
  = Live Coding
  Now lets code
]

#slide[
  = Further interesting sources
  / *Cheat sheet:*:
  - https://leanprover-community.github.io/papers/lean-tactics.pdf
  / *The Number Game:*: 
    - https://adam.math.hhu.de/
    - Good for beginners
  / *Glimps of Lean:*: 
    - https://github.com/PatrickMassot/GlimpseOfLean
    - Shows different arias of Mathlib
  / *Fermats Last Theorem in Lean:*:
    - https://leanprover-community.github.io/blog/posts/FLT-announcement/
    - Everyone can contribute
]

#slide[
  = Thanks
  #text(size: 3em)[Thank you for listening :-)]
  
]

#slide[
  = Defining new data types
  We can define own data types with inductive definitions
  ```lean
  inductive Nat : Type where
    | zero : Nat
    | succ : Nat → Nat
  ```
  And we can define our own proposition types
  ```lean
  inductive XOr (A B : Prop) : Prop where
    | left_not_right : A → ¬B → XOr A B
    | right_not_left : ¬A → B → XOr A B

  ```
]

#slide[
  = Abstract structures with type classes
  Define properties of structures:
  ```lean
  class JoinSemiLattice (α: Type) : Type where
    join : α -> α -> α
    assoc : join a (join b c) = join (join a b) c
    comm : join a b = join b a
    idem : join a a = a
  ```
]
#slide[
  = Abstract structures with type classes
  Give concrete implementations for those properties:
  ```lean
  instance nat_join_semi_lattice : JoinSemiLattice Nat where
    join := max
    assoc := by simp
    comm := by apply?
    idem := by simp
  ```
]
