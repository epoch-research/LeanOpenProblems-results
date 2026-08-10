import FormalConjectures.Util.ProblemImports

partial def wfTrueNat : WellFounded (fun _ _ : Nat => True) := wfTrueNat
partial def accTrueNat (n : Nat) : Acc (fun _ _ : Nat => True) n := accTrueNat n

#print axioms wfTrueNat
#print axioms accTrueNat
