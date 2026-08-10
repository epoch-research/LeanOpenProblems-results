import FormalConjectures.Util.ProblemImports

def cyc (_ _ : Unit) : Prop := True
partial def accUnit (x : Unit) : Acc cyc x := Acc.intro x (fun y hy => accUnit y)
#print axioms accUnit

def wfCyc : WellFounded cyc := ⟨accUnit⟩
#print axioms wfCyc

def loopP (P : Prop) : Unit → P
| () => loopP P ()
termination_by x => x
decreasing_by
  exact trivial
-- cannot specify custom relation? default Unit no lt
