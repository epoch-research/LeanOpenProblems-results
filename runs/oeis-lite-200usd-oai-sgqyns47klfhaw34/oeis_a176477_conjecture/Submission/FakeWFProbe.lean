import FormalConjectures.Util.ProblemImports

def badAcc : (n : Nat) → Acc (fun _ _ : Nat => True) n
| n => Acc.intro n (fun m _ => badAcc m)

def badWF : WellFounded (fun _ _ : Nat => True) := ⟨badAcc⟩

def loopFalse (n : Nat) : False := by
  exact loopFalse (n+1)
termination_by n
-- decreasing_by exact badWF.rel ???
#print axioms badWF
