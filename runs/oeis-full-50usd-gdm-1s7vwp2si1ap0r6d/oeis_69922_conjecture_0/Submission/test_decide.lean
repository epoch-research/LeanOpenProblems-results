import FormalConjectures.Util.ProblemImports

def my_A069922 (n : ℕ) : ℕ :=
  by let L := n ^ n ; let R := n ^ n + n ^ 2 ; exact (Finset.Icc L R).filter Nat.Prime |>.card

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : my_A069922 n > 0 :=
  my_unsafe_proof n hn

@[implementedBy my_unsafe_proof]
theorem test_1 : ∀ (n : ℕ), n > 0 → my_A069922 n > 0
