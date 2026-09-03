import Submission.SelbergNormalizerProfile

/-! Arbitrarily sharp leading cumulative normalizer estimates. The additive
constant depends on the chosen accuracy, not on the prime set or the cutoff. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exp_one_div_succ_le (B : ℕ) (hB : 0 < B) :
    exp (1 / ((B : ℝ) + 1)) ≤ 1 + 1 / (B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hq : (0 : ℝ) < 1 + 1 / (B : ℝ) := by positivity
  have hl := one_sub_inv_le_log_of_pos hq
  have he : 1 - (1 + 1 / (B : ℝ))⁻¹ = 1 / ((B : ℝ) + 1) := by
    field_simp
    ring
  rw [he] at hl
  simpa only [exp_log hq] using exp_le_exp.mpr hl

lemma indexed_normalizer_log_upper_sharp (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R B : ℕ) (hB : 0 < B) :
    normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) ≤
      (1 + 1 / (B : ℝ)) * log R + normalizerOffset (B + 1) := by
  rw [normalizer_eq_smallDivisorFamily p hp hinj R]
  have hh := primeNormalizer_log_upper (univ.image p) R (B + 1)
    (fun a ha => by obtain ⟨i, hi, rfl⟩ := mem_image.mp ha; exact hp i) (by omega)
  apply hh.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (log_natCast_nonneg R)
  simpa only [Nat.cast_add, Nat.cast_one] using exp_one_div_succ_le B hB

lemma cumulative_prime_upper_sharp (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (B : ℕ) (hB : 0 < B) (t : ℝ) (ht : 0 ≤ t) :
    cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t ≤
      (1 + 1 / (B : ℝ)) * t + normalizerOffset (B + 1) := by
  let R := ⌊exp t⌋₊
  have hR1 : 1 ≤ R := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_exp ht)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hlog : log (R : ℝ) ≤ t := by
    have hh := log_le_log hR0 (Nat.floor_le (exp_pos t).le)
    simpa only [log_exp] using hh
  have hsum : cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t ≤
      normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) := by
    simp only [cumulativeMass, normalizer, ← weight_eq_inverse_variance,
      divisorSupport, sum_filter]
    apply sum_le_sum
    intro Q hQ
    by_cases hQt : primeLogLocation p Q < t
    · rw [if_pos hQt]
      have hQR : (∏ i ∈ Q, p i) ≤ R := by
        apply Nat.le_floor
        have hd : (0 : ℝ) < ∏ i ∈ Q, (p i : ℝ) := prod_pos (fun i _ => by exact_mod_cast (hp i).pos)
        rw [Nat.cast_prod, ← exp_log hd]
        apply exp_le_exp.mpr
        rw [← primeLogLocation_eq_log_prod p hp Q]
        exact hQt.le
      rw [if_pos hQR]
    · rw [if_neg hQt]
      split_ifs
      · exact (weight_pos _ (prime_marginals p hp) Q).le
      · rfl
  exact hsum.trans ((indexed_normalizer_log_upper_sharp p hp hinj R B hB).trans
    (add_le_add (mul_le_mul_of_nonneg_left hlog
      (by positivity : (0 : ℝ) ≤ 1 + 1 / (B : ℝ))) le_rfl))

/-- On the entire cutoff interval the error from Lebesgue mass is uniformly
  at most L/B plus a constant depending only on B. -/
theorem cumulative_prime_uniform_error (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (B : ℕ) (hB : 0 < B) (t : ℝ) (ht : 0 ≤ t) (htR : t ≤ log R) :
    |cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t - t| ≤
      log (R : ℝ) / B + normalizerOffset (B + 1) + 1 := by
  have hu := cumulative_prime_upper_sharp p hp hinj B hB t ht
  have hl := cumulative_prime_lower p hp hinj R hR hfull t ht htR
  have hdiv := div_le_div_of_nonneg_right htR (Nat.cast_nonneg B)
  have hnon : 0 ≤ log (R : ℝ) / B := div_nonneg (log_natCast_nonneg R) (Nat.cast_nonneg B)
  have hc := normalizerOffset_pos (B + 1)
  have he : (1 + 1 / (B : ℝ)) * t = t + t / B := by ring
  rw [he] at hu
  rw [abs_le]
  constructor <;> linarith

#print axioms cumulative_prime_upper_sharp
#print axioms cumulative_prime_uniform_error
end Erdos970.FiniteSelberg
