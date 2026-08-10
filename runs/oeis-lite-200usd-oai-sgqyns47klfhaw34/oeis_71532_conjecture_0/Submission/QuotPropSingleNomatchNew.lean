import FormalConjectures.Util.ProblemImports

def r (P Q : Prop) : Prop := True
abbrev Q := Quot r
def q (P : Prop) : Q := Quot.mk r P
inductive I : Q → Prop where
| c : I (q True)

theorem iFalse : I (q False) := by
  have hq : q True = q False := Quot.sound trivial
  exact hq ▸ I.c

theorem bad : False := by
  cases iFalse with
  | c =>
    trace_state
    contradiction

#print axioms iFalse
#print axioms bad
