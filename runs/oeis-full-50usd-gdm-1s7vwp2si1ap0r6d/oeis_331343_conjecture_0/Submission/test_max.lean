import FormalConjectures.Util.ProblemImports

open Nat

#check Nat.maxPrimeFac
#check Nat.prime_maxPrimeFac_of_one_lt

lemma maxPrimeFac_dvd (n : ℕ) (h : 1 < n) : Nat.maxPrimeFac n ∣ n := by
  set s := {p : ℕ | p.Prime ∧ p ∣ n} with hs
  have hs₀ : s.Nonempty := by
    simp only [Set.Nonempty, Set.mem_setOf_eq, ← ne_one_iff_exists_prime_dvd, hs]
    omega
  have hs₁ : BddAbove s := by
    use n
    simp only [hs, mem_upperBounds, Set.mem_setOf_eq, and_imp]
    exact fun p _ hp ↦ Nat.le_of_dvd (zero_lt_of_lt h) hp
  exact (Nat.sSup_mem hs₀ hs₁).2

lemma maxPrimeFac_lt (n : ℕ) (h1 : 1 < n) (hc : ¬ Nat.Prime n) : Nat.maxPrimeFac n < n := by
  have hp : Nat.Prime (Nat.maxPrimeFac n) := Nat.prime_maxPrimeFac_of_one_lt n h1
  have hdvd : Nat.maxPrimeFac n ∣ n := maxPrimeFac_dvd n h1
  have hle : Nat.maxPrimeFac n ≤ n := Nat.le_of_dvd (by omega) hdvd
  by_cases heq : Nat.maxPrimeFac n = n
  · have : Nat.Prime n := by rwa [← heq]
    contradiction
  · omega

