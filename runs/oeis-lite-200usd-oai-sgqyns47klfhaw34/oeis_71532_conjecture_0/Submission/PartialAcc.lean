import FormalConjectures.Util.ProblemImports

partial def badAcc (u : Unit) : Acc (fun _ _ : Unit => True) u :=
  Acc.intro u (fun y h => badAcc y)

#print axioms badAcc

def badWF : WellFounded (fun _ _ : Unit => True) := ⟨badAcc⟩
#print axioms badWF

example : False := by
  have h := badWF.apply ()
  cases h with
  | intro _ ih =>
    exact False.elim (by exact False.elim (False.elim ?x))
