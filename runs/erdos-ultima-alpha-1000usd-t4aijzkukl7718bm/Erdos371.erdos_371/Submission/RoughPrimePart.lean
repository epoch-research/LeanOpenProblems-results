import Submission.QuantileBalanced

/-! Canonical small- and large-prime parts, and a uniform logarithmic bound
showing that the latter retains almost all of an integer's logarithmic size. -/

namespace Erdos371

noncomputable def smoothPrimePart (B n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ≤ B, p ^ n.factorization p

noncomputable def roughPrimePart (B n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with B < p, p ^ n.factorization p

lemma smoothPrimePart_pos (B n : ℕ) : 0 < smoothPrimePart B n := by
  exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _

lemma roughPrimePart_pos (B n : ℕ) : 0 < roughPrimePart B n := by
  exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _

lemma roughPrimePart_mul_smoothPrimePart (B n : ℕ) (hn : n ≠ 0) :
    roughPrimePart B n * smoothPrimePart B n = n := by
  have h := Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => B < p)
    (fun p => p ^ n.factorization p)
  have hf : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
    Nat.factorization_prod_pow_eq_self hn
  simpa only [roughPrimePart, smoothPrimePart, not_lt, hf] using h

lemma roughPrimePart_dvd (B n : ℕ) (hn : n ≠ 0) : roughPrimePart B n ∣ n :=
  ⟨smoothPrimePart B n, (roughPrimePart_mul_smoothPrimePart B n hn).symm⟩

lemma roughPrimePart_prime_large (B n p : ℕ) (hp : p.Prime) (hpa : p ∣ roughPrimePart B n) : B < p := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finset_prod_iff _).mp hpa
  obtain ⟨hqn, hBq⟩ := Finset.mem_filter.mp hq
  have he : p = q := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
    (hp.dvd_of_dvd_pow hpq)
  omega

lemma roughPrimePart_minFac (B n : ℕ) (ha : 1 < roughPrimePart B n) :
    B < (roughPrimePart B n).minFac :=
  roughPrimePart_prime_large B n _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)

lemma roughPrimePart_squarefree (B n : ℕ) (hn : n ≠ 0)
    (hfree : ∀ p, p.Prime → B < p → ¬p^2 ∣ n) : Squarefree (roughPrimePart B n) := by
  apply Nat.squarefree_of_factorization_le_one (roughPrimePart_pos B n).ne'
  intro p
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ roughPrimePart B n
    · have hpB := roughPrimePart_prime_large B n p hp hpa
      have hnp : n.factorization p ≤ 1 := by
        have h := hfree p hp hpB
        rw [hp.pow_dvd_iff_le_factorization hn] at h
        omega
      exact ((Nat.factorization_le_iff_dvd (roughPrimePart_pos B n).ne' hn).mpr
        (roughPrimePart_dvd B n hn) p).trans hnp
    · rw [Nat.factorization_eq_zero_of_not_dvd hpa]
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    omega

lemma log_smoothPrimePart (B n : ℕ) : Real.log (smoothPrimePart B n) = smallPrimeLog (B + 1) n := by
  rw [smoothPrimePart, Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
    unfold smallPrimeLog
    apply Finset.sum_subset
    · intro p hp
      obtain ⟨hpn, hpB⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_of_mem_primeFactors hpn⟩
    · intro p hp hnot
      have hpB : p ≤ B := by have := (Nat.mem_primesBelow.mp hp).1; omega
      have hpn : p ∉ n.primeFactors := by simpa only [Finset.mem_filter, hpB, and_true] using hnot
      have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpn
      simp [hz]
  · intro p hp
    exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

lemma log_roughPrimePart (B n : ℕ) (hn : n ≠ 0) :
    Real.log (roughPrimePart B n) = Real.log n - smallPrimeLog (B + 1) n := by
  have h := congrArg (fun m : ℕ => Real.log (m : ℝ)) (roughPrimePart_mul_smoothPrimePart B n hn)
  dsimp only at h
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (roughPrimePart_pos B n).ne')
    (by exact_mod_cast (smoothPrimePart_pos B n).ne'), log_smoothPrimePart] at h
  linarith

lemma factorial_log_lower (N : ℕ) : N * Real.log N - N ≤ Real.log N.factorial := by
  by_cases hN : N = 0
  · simp [hN]
  have h := Stirling.le_log_factorial_stirling hN
  have hlog := Real.log_natCast_nonneg N
  have hπ : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

lemma roughPrimePart_log_deficit_nonneg (B N n : ℕ) (hn : n ∈ Finset.range N) :
    0 ≤ Real.log N - Real.log (roughPrimePart B (n + 1)) := by
  have hnN := Finset.mem_range.mp hn
  apply sub_nonneg.mpr
  apply Real.log_le_log (by exact_mod_cast roughPrimePart_pos B (n + 1))
  exact_mod_cast (Nat.le_of_dvd (by omega : 0 < n + 1)
    (roughPrimePart_dvd B (n + 1) (by omega))).trans (by omega : n + 1 ≤ N)

/-- The expected logarithmic deficit is at most 1 + 4 log(B+1). -/
theorem roughPrimePart_log_deficit_sum_bound (B N : ℕ) :
    (∑ n ∈ Finset.range N, (Real.log N - Real.log (roughPrimePart B (n + 1)))) ≤
      N + 4 * N * Real.log (B + 1 : ℝ) := by
  have hlog : (∑ n ∈ Finset.range N, Real.log (n + 1 : ℝ)) = Real.log N.factorial := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, Real.log_prod]
    · simp only [Nat.cast_add, Nat.cast_one]
    · intro n hn
      positivity
  have he (n : ℕ) : Real.log N - Real.log (roughPrimePart B (n + 1)) =
      Real.log N - Real.log (n + 1 : ℝ) + smallPrimeLog (B + 1) (n + 1) := by
    rw [log_roughPrimePart B (n + 1) (by omega)]
    push_cast
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hlog]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h := smallPrimeLog_sum_bound (B + 1) N
  push_cast at h
  linarith [factorial_log_lower N]

noncomputable def smallRoughPartCount (B N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => (roughPrimePart B (n + 1))^4 ≤ N^3).card

/-- Almost all rough parts exceed N^(3/4) when B is subpower. The powers in
the predicate keep the cutoff entirely in natural-number arithmetic. -/
theorem smallRoughPartCount_log_bound (B N : ℕ) (hN : 1 < N) :
    (smallRoughPartCount B N : ℝ) * Real.log N ≤
      4 * N + 16 * N * Real.log (B + 1 : ℝ) := by
  let S := (Finset.range N).filter fun n => (roughPrimePart B (n + 1))^4 ≤ N^3
  have hterm (n : ℕ) (hn : n ∈ S) : Real.log N ≤
      4 * (Real.log N - Real.log (roughPrimePart B (n + 1))) := by
    have hpow := (Finset.mem_filter.mp hn).2
    have hp : (roughPrimePart B (n + 1) : ℝ)^4 ≤ (N : ℝ)^3 := by exact_mod_cast hpow
    have ha0 : (0 : ℝ) < roughPrimePart B (n + 1) := by exact_mod_cast roughPrimePart_pos B (n + 1)
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (roughPrimePart B (n + 1) : ℝ)^4) hp
    simp only [Real.log_pow] at hlog
    norm_num at hlog
    linarith
  calc
    _ = ∑ n ∈ S, Real.log N := by simp [S, smallRoughPartCount]
    _ ≤ ∑ n ∈ S, 4 * (Real.log N - Real.log (roughPrimePart B (n + 1))) := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range N, 4 * (Real.log N - Real.log (roughPrimePart B (n + 1))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n hn _ => mul_nonneg (by norm_num) (roughPrimePart_log_deficit_nonneg B N n hn))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      have h := roughPrimePart_log_deficit_sum_bound B N
      linarith

open Filter in
theorem smallRoughPartCount_tendsto_zero (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => (smallRoughPartCount (B N) N : ℝ) / N) atTop (nhds 0) := by
  have hi : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have ht := (hi.const_mul (4 : ℝ)).add (hB.const_mul (16 : ℝ))
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop 1] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h := smallRoughPartCount_log_bound (B N) N hN
  have he : 4 * (Real.log N)⁻¹ + 16 * (Real.log (B N + 1 : ℝ) / Real.log N) =
      (4 * N + 16 * N * Real.log (B N + 1 : ℝ)) / (N * Real.log N) := by field_simp
  rw [he, le_div_iff₀ (mul_pos hN0 hlog)]
  convert h using 1 <;> field_simp

#print axioms roughPrimePart_squarefree
#print axioms log_roughPrimePart
#print axioms roughPrimePart_log_deficit_sum_bound
#print axioms smallRoughPartCount_tendsto_zero
end Erdos371
