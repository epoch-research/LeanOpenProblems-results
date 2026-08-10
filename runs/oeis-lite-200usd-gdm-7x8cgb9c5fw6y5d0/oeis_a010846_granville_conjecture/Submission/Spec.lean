import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

theorem prime_factors_singleton {p : ℕ} (hp : Nat.Prime p) : primeFactors p = {p} := by
  ext q
  simp only [mem_primeFactors, mem_singleton]
  constructor
  · rintro ⟨hq, hqdvd, hp_ne_zero⟩
    rcases hp.eq_one_or_self_of_dvd q hqdvd with h1 | h2
    · exfalso
      exact hq.ne_one h1
    · exact h2
  · rintro rfl
    exact ⟨hp, dvd_rfl, hp.ne_zero⟩

theorem prime_factors_one : primeFactors 1 = ∅ := by
  unfold primeFactors
  rw [primeFactorsList_one]
  rfl

theorem filter_prime_eq {p : ℕ} (hp : Nat.Prime p) :
    (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = {1, p} := by
  ext k
  simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨h1, hkp⟩, hsub⟩
    by_cases hk : k = 1
    · left; exact hk
    · right
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hk
      have hq_mem : q ∈ primeFactors k := by
        rw [mem_primeFactors]
        refine ⟨hq, hqdvd, by omega⟩
      have hq_mem_p := hsub hq_mem
      rw [prime_factors_singleton hp, mem_singleton] at hq_mem_p
      have hp_dvd : p ∣ k := by rwa [hq_mem_p] at hqdvd
      have hp_le_k := Nat.le_of_dvd (by omega) hp_dvd
      omega
  · rintro (rfl | rfl)
    · constructor
      · refine ⟨by omega, hp.two_le.trans' (by omega)⟩
      · rw [prime_factors_one]
        exact empty_subset _
    · constructor
      · refine ⟨hp.two_le.trans' (by omega), le_rfl⟩
      · exact subset_rfl

theorem a_prime_eq_two {p : ℕ} (hp : Nat.Prime p) : a p = 2 := by
  unfold a
  rw [filter_prime_eq hp]
  have h1 : 1 ≠ p := by
    have := hp.two_le
    omega
  have h2 : 1 ∉ ({p} : Finset ℕ) := by simp [h1]
  rw [card_insert_of_notMem h2]
  simp

theorem exp_four_lt_100 : Real.exp 4 < 100 := by
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  rw [h4]
  rw [← Real.exp_one_pow 4]
  have h_exp_one : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h_pow : (Real.exp 1) ^ 4 < 3 ^ 4 := by
    apply pow_lt_pow_left₀ h_exp_one (by positivity) (by decide)
  have h_calc : (3 ^ 4 : ℝ) < 100 := by norm_num
  exact h_pow.trans h_calc

theorem log_one_hundred_gt_four : 4 < Real.log 100 := by
  have h1 : 0 < Real.exp 4 := by positivity
  have h2 : Real.exp 4 < 100 := exp_four_lt_100
  have h3 := Real.log_lt_log h1 h2
  rwa [Real.log_exp] at h3

theorem log_prime_gt_four {p : ℕ} (hp : 100 ≤ p) : 4 < Real.log p := by
  have h_le : (100 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h_log_le : Real.log 100 ≤ Real.log p := Real.log_le_log (by norm_num) h_le
  exact log_one_hundred_gt_four.trans_le h_log_le

theorem rpow_inequality {p : ℕ} (hp : 100 ≤ p) : 2 < (Real.log p) ^ (1/2 : ℝ) := by
  have h_log_gt : 4 < Real.log p := log_prime_gt_four hp
  have h_pow : (4 : ℝ) ^ (1/2 : ℝ) < (Real.log p) ^ (1/2 : ℝ) := by
    apply Real.rpow_lt_rpow (by norm_num) h_log_gt (by norm_num)
  have h_four_pow : (4 : ℝ) ^ (1/2 : ℝ) = 2 := by norm_num
  rwa [h_four_pow] at h_pow

/--
Granville's ABC-Conjecture implies that for any $\epsilon > 0$,
the function $a(n)$ is bounded below by $(\log n)^{1 - \epsilon}$ for sufficiently large $n$.
This is a formalization of a claim implied by the context:
OEIS C: "This function of n appears in an ABC-conjecture by Andrew Granville. See Goldfeld."
Granville (via Goldfeld) showed that ABC conjecture $\iff$ $\forall \epsilon > 0, \exists N, \forall n > N, a(n) \ge (\log n)^{1-\epsilon}$.
-/
theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  have h_eps : 0 < (1 / 2 : ℝ) := by norm_num
  obtain ⟨N, hN⟩ := h (1 / 2) h_eps
  obtain ⟨p, hp_le, hp⟩ := Nat.exists_infinite_primes (max N 100)
  have hp_ge_N : N ≤ p := (le_max_left N 100).trans hp_le
  have hp_ge_100 : 100 ≤ p := (le_max_right N 100).trans hp_le
  have h_ineq := hN p hp_ge_N
  have h_exp : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [h_exp] at h_ineq
  have h_ap : a p = 2 := a_prime_eq_two hp
  rw [h_ap] at h_ineq
  have h_gt : 2 < (Real.log p) ^ (1 / 2 : ℝ) := rpow_inequality hp_ge_100
  have h_coer : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h_coer] at h_ineq
  exact lt_irrefl 2 (h_gt.trans_le h_ineq)
