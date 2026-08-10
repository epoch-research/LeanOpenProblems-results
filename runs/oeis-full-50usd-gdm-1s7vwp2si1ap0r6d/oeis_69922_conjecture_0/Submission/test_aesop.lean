import FormalConjectures.Util.ProblemImports

def A069922 (n : ℕ) : ℕ :=
  by let L := n ^ n ; let R := n ^ n + n ^ 2 ; exact (Finset.Icc L R).filter Nat.Prime |>.card

theorem oeis_69922_conjecture_0 : ∀ (n : ℕ), n > 0 → A069922 n > 0 := by
  aesop
