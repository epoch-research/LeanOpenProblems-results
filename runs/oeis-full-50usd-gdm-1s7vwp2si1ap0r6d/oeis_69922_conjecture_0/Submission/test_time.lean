import FormalConjectures.Util.ProblemImports

def A069922 (n : ℕ) : ℕ :=
  by let L := n ^ n ; let R := n ^ n + n ^ 2 ; exact (Finset.Icc L R).filter Nat.Prime |>.card

#eval A069922 4
#eval A069922 15
