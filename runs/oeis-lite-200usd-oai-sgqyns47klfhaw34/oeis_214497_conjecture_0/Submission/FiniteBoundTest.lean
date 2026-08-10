import FormalConjectures.Util.ProblemImports
open Nat

lemma no_witness_of_pow_le_k {n k : ℕ} (hk : 3 ^ n ≤ k) :
    ¬ (Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  intro h
  have hsub : 3 ^ n - k = 0 := Nat.sub_eq_zero_of_le hk
  have hzero : (3 ^ n - k) * (2 ^ n) - 1 = 0 := by simp [hsub]
  have hnot : ¬ Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) := by
    simpa [hzero] using Nat.not_prime_zero
  exact hnot h.1

#check Fin.exists_iff
#check Finset.exists_iff
#check Fintype.exists_iff
