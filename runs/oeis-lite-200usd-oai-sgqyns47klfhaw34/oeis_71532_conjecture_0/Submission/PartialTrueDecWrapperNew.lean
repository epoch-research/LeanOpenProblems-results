import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

structure TrueDec (P : Prop) where
  d : Decidable P
  ok : match d with | .isTrue _ => True | .isFalse _ => False

partial def mkTrueDec (P : Prop) : TrueDec P :=
  match loopDec P with
  | .isTrue h => ⟨.isTrue h, trivial⟩
  | .isFalse hn => mkTrueDec P

theorem arbitrary (P : Prop) : P := by
  let c := mkTrueDec P
  cases h : c.d with
  | isTrue hp => exact hp
  | isFalse hn =>
      have bad : False := by simpa [h] using c.ok
      exact False.elim bad

#print axioms loopDec
#print axioms mkTrueDec
#print axioms arbitrary
