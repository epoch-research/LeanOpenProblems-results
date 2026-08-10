import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

noncomputable def getP (P : Prop) : P := by
  let rec hp : P := by
    have heq : loopDec P = Decidable.isTrue hp := Subsingleton.elim _ _
    cases h : loopDec P with
    | isTrue htrue => exact htrue
    | isFalse hfalse =>
      rw [h] at heq
      cases heq
  exact hp

theorem arb (P : Prop) : P := getP P
#print axioms loopDec
#print axioms getP
#print axioms arb
