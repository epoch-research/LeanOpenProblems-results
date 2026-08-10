import FormalConjectures.Util.ProblemImports

namespace QuotTruthFamily

def R (A B : Prop) : Prop := A → B
abbrev Q := Quot R

inductive Holds : Q → Prop
| intro (A : Prop) (h : A) : Holds (Quot.mk R A)

-- True holds at mk True
def hTrue : Holds (Quot.mk R True) := Holds.intro True trivial

-- Since P -> True, mk P = mk True, hence mk True = mk P by symmetry.
def hP_family (P : Prop) : Holds (Quot.mk R P) := by
  have e : (Quot.mk R P : Q) = Quot.mk R True := Quot.sound (fun hp : P => trivial)
  exact Eq.ndrec hTrue e.symm

-- Can eliminating Holds (mk P) recover P?
theorem arbitrary (P : Prop) : P := by
  have h := hP_family P
  cases h with
  | intro A hA =>
    -- context? target P
    -- try exact hA
    trace_state
    sorry

#print axioms hP_family
#print axioms arbitrary
end QuotTruthFamily
