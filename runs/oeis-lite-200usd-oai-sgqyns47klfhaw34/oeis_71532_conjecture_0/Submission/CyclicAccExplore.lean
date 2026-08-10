import FormalConjectures.Util.ProblemImports

def badAcc : Acc (fun _ _ : Unit => True) () := Acc.intro () (fun y hy => badAcc)

def loopFalse : False := WellFounded.fix ⟨fun _ => badAcc⟩ (motive := fun _ => False) (fun x rec => rec x trivial) ()

#print axioms loopFalse
