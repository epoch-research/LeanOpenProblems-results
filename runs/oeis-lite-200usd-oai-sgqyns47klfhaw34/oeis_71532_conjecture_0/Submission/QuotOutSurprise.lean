import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True
def q (P : Prop) := Quot.mk R P

theorem out_eq_mk (P : Prop) : Quot.out (q P) = P := by
  simp [q]
#print axioms out_eq_mk
#print out_eq_mk

theorem false_by_quot : False := by
  have e : q True = q False := Quot.sound trivial
  -- Try use out_eq to relate
  have hT : Quot.out (q True) := by simpa [out_eq_mk True]
  have hf : Quot.out (q False) := by simpa [e] using hT
  simpa [out_eq_mk False] using hf
#print axioms false_by_quot
