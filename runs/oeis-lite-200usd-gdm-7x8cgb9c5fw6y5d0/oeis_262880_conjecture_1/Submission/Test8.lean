import FormalConjectures.Util.ProblemImports

inductive MyType (A : Prop) : Type where
  | base : A → MyType A
  | step : (A → MyType A) → MyType A

theorem MyType_nonempty (A : Prop) : Nonempty (MyType A) := by
  by_cases h : A
  · exact Nonempty.intro (MyType.base h)
  · have g : A → MyType A := by
      intro ha
      exact False.elim (h ha)
    exact Nonempty.intro (MyType.step g)

noncomputable def get_MyType (A : Prop) : MyType A :=
  Classical.choice (MyType_nonempty A)

partial def get_A_mytype (A : Prop) (x : MyType A) : MyType A :=
  match x with
  | MyType.base h => MyType.base h
  | MyType.step g => get_A_mytype A (g (get_A_mytype A x))
