import FormalConjectures.Util.ProblemImports

namespace QuotAsym

def r (p q : Prop) : Prop := q

def Q := Quot r

def qP (P : Prop) : Q := Quot.mk r P

#check Quot.sound (r := r)
#check Quot.out
#check Quot.out_eq

example (P : Prop) : qP P = qP True := Quot.sound trivial
example (P : Prop) : qP True = qP P := Eq.symm (Quot.sound (a:=P) (b:=True) trivial)

inductive Carr : Q → Prop where
| intro : Carr (qP True)

theorem carrP (P : Prop) : Carr (qP P) := by
  rw [show qP P = qP True from Quot.sound trivial]
  exact Carr.intro

theorem tryExtract (P : Prop) : Carr (qP P) → P := by
  intro h
  cases h with
  | intro =>
    -- goal P, no assumptions?
    trace_state
    sorry

#print tryExtract

end QuotAsym
