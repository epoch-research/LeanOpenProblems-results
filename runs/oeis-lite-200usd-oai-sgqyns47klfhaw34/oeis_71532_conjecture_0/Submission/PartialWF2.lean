import FormalConjectures.Util.ProblemImports

partial def wfTrueNat (_ : Unit) : WellFounded (fun _ _ : Nat => True) := wfTrueNat ()
#print axioms wfTrueNat
