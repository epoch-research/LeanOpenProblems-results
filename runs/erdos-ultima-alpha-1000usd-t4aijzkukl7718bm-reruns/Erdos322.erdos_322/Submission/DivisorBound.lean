import FormalConjecturesUtil

/-! Uniform subpolynomial divisor bounds, for studying the effect of scaling. -/

namespace Erdos322Research

open Filter

theorem divisor_count_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let δ : ℝ := (2 : ℝ) ^ ε - 1
  have hδ : 0 < δ := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hε)
  let B : ℝ := 1 + δ⁻¹
  have hB : 1 ≤ B := by
    dsimp [B]
    have := inv_nonneg.mpr hδ.le
    linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hδB : 1 ≤ B * δ := by
    have hi := inv_mul_cancel₀ (ne_of_gt hδ)
    dsimp [B]
    nlinarith
  have hlin (a : ℕ) : (a + 1 : ℝ) ≤ B * ((2 : ℝ) ^ ε) ^ a := by
    have hb := one_add_mul_le_pow (show -2 ≤ δ by linarith) a
    have he : 1 + δ = (2 : ℝ) ^ ε := by dsimp [δ]; ring
    rw [he] at hb
    calc
      (a + 1 : ℝ) ≤ B * (1 + a * δ) := by
        nlinarith [mul_le_mul_of_nonneg_left hδB (Nat.cast_nonneg a)]
      _ ≤ B * ((2 : ℝ) ^ ε) ^ a := mul_le_mul_of_nonneg_left hb hBpos.le
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 2)
  refine ⟨B ^ N, pow_pos hBpos _, ?_⟩
  intro n hn
  have hrpow (p a : ℕ) : ((p : ℝ) ^ ε) ^ a = ((p : ℝ) ^ a) ^ ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
      mul_comm ε (a : ℝ), Real.rpow_natCast_mul (Nat.cast_nonneg p)]
  have hlocal (p a : ℕ) (hp : p.Prime) :
      (a + 1 : ℝ) ≤ (if p < N then B else 1) * ((p : ℝ) ^ a) ^ ε := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    by_cases hpN : p < N
    · rw [if_pos hpN, ← hrpow]
      exact (hlin a).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) a)
        hBpos.le)
    · rw [if_neg hpN, one_mul, ← hrpow]
      have htwo : (a + 1 : ℝ) ≤ (2 : ℝ) ^ a := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := a)))
      exact htwo.trans (pow_le_pow_left₀ (by norm_num) (hN p (by omega)) a)
  have hconst : (∏ p ∈ n.primeFactors, if p < N then B else 1) ≤ B ^ N := by
    rw [← Finset.prod_filter, Finset.prod_const]
    apply pow_le_pow_right₀ hB
    have hs : n.primeFactors.filter (fun p ↦ p < N) ⊆ Finset.range N := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hs
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    have h := Nat.factorization_prod_pow_eq_self hn.ne'
    simpa [Finsupp.prod, Nat.support_factorization] using congrArg (fun m : ℕ ↦ (m : ℝ)) h
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, (n.factorization p + 1 : ℝ) := by
      rw [Nat.card_divisors hn.ne']
      simp
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then B else 1) * ((p : ℝ) ^ n.factorization p) ^ ε := by
      apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
      intro p hp
      exact hlocal p _ (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, if p < N then B else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, Real.finset_prod_rpow]
      · rw [hprod]
      · intro p hp; positivity
    _ ≤ B ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconst (by positivity)

end Erdos322Research
