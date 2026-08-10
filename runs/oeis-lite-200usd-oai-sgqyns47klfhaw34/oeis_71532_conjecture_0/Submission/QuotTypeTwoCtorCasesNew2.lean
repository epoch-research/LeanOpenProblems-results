import FormalConjectures.Util.ProblemImports

def r (P Q : Prop) : Prop := True
abbrev Q := Quot r
def q (P : Prop) : Q := Quot.mk r P
inductive Bad : Q → Type where
| cT : Bad (q True)
| cF : Bad (q False)
lemma hidx : q True = q False := Quot.sound trivial
def cT_at_F : Bad (q False) := hidx ▸ Bad.cT

example : False := by
  let x : Bad (q False) := cT_at_F
  cases x with
  | cT =>
      trace_state
      exact False.elim (by contradiction)
  | cF =>
      trace_state
      exact False.elim (by contradiction)
