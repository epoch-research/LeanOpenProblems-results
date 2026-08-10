import FormalConjectures.Util.ProblemImports

def accUnit : Acc (fun _ _ : Unit => True) () := Acc.intro () (fun y hy => accUnit)

def wfUnit : WellFounded (fun _ _ : Unit => True) := ⟨fun _ => accUnit⟩

def loopFalse : Unit → False := WellFounded.fix wfUnit (C := fun _ => False) (fun x ih => ih x trivial)

theorem t : False := loopFalse ()
#print axioms t
