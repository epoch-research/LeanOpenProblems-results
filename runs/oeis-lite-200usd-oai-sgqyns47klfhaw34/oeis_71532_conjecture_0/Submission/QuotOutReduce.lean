import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True
def q (P : Prop) := Quot.mk R P
example (P : Prop) : Quot.out (q P) = P := by
  fail_if_success rfl
  fail_if_success simp [q]
  sorry
#eval ("ok")
