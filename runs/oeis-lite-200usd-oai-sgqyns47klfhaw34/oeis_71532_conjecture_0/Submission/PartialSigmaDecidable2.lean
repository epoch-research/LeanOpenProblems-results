import FormalConjectures.Util.ProblemImports
axiom P : Prop

abbrev GoodDec (P : Prop) : Type := Σ d : Decidable P, match d with | .isTrue _ => PUnit | .isFalse _ => Empty
partial def gd (_ : Unit) : GoodDec P := gd ()
#print axioms gd
example : P := by
  rcases gd () with ⟨d, h⟩
  cases d with
  | isTrue hp => exact hp
  | isFalse hn => cases h

abbrev BadDec (P : Prop) : Type := Σ d : Decidable P, match d with | .isTrue _ => Empty | .isFalse _ => PUnit
partial def bd (_ : Unit) : BadDec P := bd ()
#print axioms bd
example : ¬ P := by
  intro hp
  rcases bd () with ⟨d,h⟩
  cases d with
  | isTrue hp2 => cases h
  | isFalse hn => exact hn hp
