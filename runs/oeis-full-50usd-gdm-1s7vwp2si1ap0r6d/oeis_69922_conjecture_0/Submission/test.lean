import FormalConjectures.Util.ProblemImports

def A069922 (n : ℕ) : ℕ :=
  by let L := n ^ n ; let R := n ^ n + n ^ 2 ; exact (Finset.Icc L R).filter Nat.Prime |>.card

lemma A069922_pos_iff (n : ℕ) : A069922 n > 0 ↔ ∃ p, n^n ≤ p ∧ p ≤ n^n + n^2 ∧ Nat.Prime p := by
  dsimp [A069922]
  change 0 < (Finset.filter Nat.Prime (Finset.Icc (n ^ n) (n ^ n + n ^ 2))).card ↔ _
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp_rw [Finset.mem_Icc, and_assoc]

#print axioms A069922_pos_iff








