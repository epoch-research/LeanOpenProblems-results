import FormalConjectures.Util.ProblemImports
open Nat

def good (n k : ℕ) : Prop := Nat.Prime ((3 ^ n - k) * 2 ^ n - 1) ∧ Nat.Prime ((3 ^ n - k) * 2 ^ n + 1)

lemma no_good_ge {n k : ℕ} (hk : 3 ^ n ≤ k) : ¬ good n k := by
  intro h
  have hsub : 3 ^ n - k = 0 := Nat.sub_eq_zero_of_le hk
  have hzero : (3 ^ n - k) * 2 ^ n - 1 = 0 := by simp [good, hsub]
  exact (by simpa [hzero] using Nat.not_prime_zero) h.1

#check Finite.exists_max
#check Finset.exists_max_image
#check Fintype.exists_max
#check Set.Finite.exists_maximal_wrt
#check Nat.find
#check Nat.findGreatest
#check Nat.findGreatest_spec
#check Nat.findGreatest_is_greatest
