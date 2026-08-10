import FormalConjectures.Util.ProblemImports
axiom P : Prop

-- Try to get equality of representatives from quotient equality via eliminators
inductive Rel : Prop → Prop → Prop where | mk : Rel True False | refl (p) : Rel p p

def qtrue : Quot Rel := Quot.mk Rel True
def qfalse : Quot Rel := Quot.mk Rel False

example : qtrue = qfalse := Quot.sound Rel.mk

-- Can quotient induction expose a cast from True to False?
example : False := by
  have hq : qtrue = qfalse := Quot.sound Rel.mk
  -- no direct way; try subst/simp
  fail_if_success subst hq
  fail_if_success cases hq
  sorry
