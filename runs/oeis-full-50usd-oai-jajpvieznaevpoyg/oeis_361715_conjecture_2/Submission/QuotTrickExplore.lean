import FormalConjectures.Util.ProblemImports

-- Can a custom Setoid plus Quotient.exact derive an arbitrary proposition?
def trickySetoid (P : Prop) : Setoid Bool where
  r x y := x = y ∨ P
  iseqv := by
    constructor
    · intro x; exact Or.inl rfl
    · intro x y h; rcases h with h|h; · exact Or.inl h.symm; · exact Or.inr h
    · intro x y z h1 h2
      rcases h1 with h1|h1
      · rcases h2 with h2|h2; · exact Or.inl (h1.trans h2); · exact Or.inr h2
      · exact Or.inr h1

example (P : Prop) : Quotient.mk (s := trickySetoid P) true = Quotient.mk (s := trickySetoid P) false → P := by
  intro h
  have rel := Quotient.exact h
  dsimp [trickySetoid] at rel
  rcases rel with htf | hp
  · cases htf
  · exact hp

-- But producing that equality needs P; Quot.sound cannot help without the relation.
