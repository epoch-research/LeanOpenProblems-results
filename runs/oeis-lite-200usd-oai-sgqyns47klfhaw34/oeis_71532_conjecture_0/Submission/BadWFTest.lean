import FormalConjectures.Util.ProblemImports

def R (_ _ : Unit) := True

def badWF : WellFounded R := ⟨fun a => Acc.intro a (fun b h => badWF.apply b)⟩
#print axioms badWF

def loopFalse : Unit → False := WellFounded.fix badWF (motive := fun _ => False) (fun x rec => rec () trivial)
example : False := loopFalse ()
#print axioms loopFalse

partial def pbadWF (_ : Unit) : WellFounded R := pbadWF ()
#print axioms pbadWF
