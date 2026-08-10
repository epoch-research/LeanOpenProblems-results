import FormalConjectures.Util.ProblemImports
axiom P : Prop
partial def sigDec (_ : Unit) : Σ d : Decidable P, match d with | .isTrue h => P | .isFalse h => ¬ P := sigDec ()
#print axioms sigDec
example : P ∨ ¬ P := by
  rcases sigDec () with ⟨d,h⟩
  cases d with
  | isTrue hp => exact .inl hp
  | isFalse hn => exact .inr hn
