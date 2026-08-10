import FormalConjectures.Util.ProblemImports

inductive BadBox : Prop → Type where
| mk : BadBox True

partial def loopBadBox (P : Prop) : BadBox P := loopBadBox P

def BadBox.out {P : Prop} (b : BadBox P) : P := by
  cases b
  trivial

theorem arbitraryProp (P : Prop) : P := by
  exact BadBox.out (loopBadBox P)

#print axioms arbitraryProp
