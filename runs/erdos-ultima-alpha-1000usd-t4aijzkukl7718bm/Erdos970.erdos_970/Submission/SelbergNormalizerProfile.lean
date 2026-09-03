import Submission.FiniteLayerCake
import Submission.SelbergSoftPrimeBound

/-! Cumulative-mass estimates for logarithmic Selberg profiles. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma indexed_normalizer_log_upper (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) :
    normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) ≤
      (65 / 64) * log R + normalizerOffset 65 := by
  rw [normalizer_eq_smallDivisorFamily p hp hinj R]
  apply primeNormalizer_log_upper_concrete
  intro a ha
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  exact hp i

noncomputable def primeLogLocation (p : ι → ℕ) (Q : Finset ι) : ℝ :=
  ∑ i ∈ Q, log (p i : ℝ)

lemma primeLogLocation_nonneg (p : ι → ℕ) (Q : Finset ι) :
    0 ≤ primeLogLocation p Q := sum_nonneg (fun i _ => log_natCast_nonneg _)

lemma primeLogLocation_eq_log_prod (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (Q : Finset ι) : primeLogLocation p Q = log (∏ i ∈ Q, (p i : ℝ)) := by
  exact (log_prod (fun i _ => by exact_mod_cast (hp i).ne_zero)).symm

lemma cumulative_prime_upper (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (t : ℝ) (ht : 0 ≤ t) :
    cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t ≤
      (65 / 64) * t + normalizerOffset 65 := by
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
  have hh := indexed_normalizer_log_upper p hp hinj R
  exact hsum.trans (hh.trans (add_le_add (mul_le_mul_of_nonneg_left hlog (by norm_num)) le_rfl))

lemma cumulative_prime_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (t : ℝ) (ht : 0 ≤ t) (htR : t ≤ log R) :
    t - 1 ≤ cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t := by
  by_cases ht1 : t ≤ 1
  · have hnon : 0 ≤ cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t := by
      apply sum_nonneg
      intro Q hQ
      split_ifs
      · exact (weight_pos _ (prime_marginals p hp) Q).le
      · rfl
    linarith
  · let S := ⌊exp (t - 1)⌋₊
    have hS1 : 1 ≤ S := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_exp (show 0 ≤ t - 1 by linarith))
    have hS0 : (0 : ℝ) < S := by exact_mod_cast (show 0 < S by omega)
    have hSR : S ≤ R := by
      have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
      have he : exp (t - 1) ≤ (R : ℝ) := by
        rw [← exp_log hR0]
        exact exp_le_exp.mpr (by linarith)
      have hh := Nat.floor_le_floor he
      simpa only [Nat.floor_natCast] using hh
    have hlogS : log (S : ℝ) < t := by
      have hh := log_le_log hS0 (Nat.floor_le (exp_pos (t - 1)).le)
      rw [log_exp] at hh
      linarith
    have hlow : t - 1 ≤ (harmonic S : ℝ) := by
      have hl := log_le_log (exp_pos (t - 1)) (Nat.lt_floor_add_one (exp (t - 1))).le
      rw [log_exp] at hl
      exact hl.trans (by exact_mod_cast log_add_one_le_harmonic S)
    have hn := harmonic_le_normalizer p hp hinj S (fun a ha haS => hfull a ha (haS.trans hSR))
    apply hlow.trans (hn.trans _)
    simp only [cumulativeMass, normalizer, ← weight_eq_inverse_variance,
      divisorSupport, sum_filter]
    apply sum_le_sum
    intro Q hQ
    by_cases hQS : (∏ i ∈ Q, p i) ≤ S
    · rw [if_pos hQS]
      have hQt : primeLogLocation p Q < t := by
        rw [primeLogLocation_eq_log_prod p hp Q]
        have hd : (0 : ℝ) < ∏ i ∈ Q, (p i : ℝ) := prod_pos (fun i _ => by exact_mod_cast (hp i).pos)
        have hprod : (∏ i ∈ Q, (p i : ℝ)) ≤ S := by exact_mod_cast hQS
        exact (log_le_log hd hprod).trans_lt hlogS
      rw [if_pos hQt]
    · rw [if_neg hQS]
      split_ifs
      · exact (weight_pos _ (prime_marginals p hp) Q).le
      · rfl

/-- The mass of the soft square has its cubic logarithmic size, up to a lower
order square term. This improves the earlier two-moment estimate. -/
theorem prime_soft_square_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    log (R : ℝ) ^ 3 / 3 - log (R : ℝ) ^ 2 ≤
      ∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q *
        softProfile (fun i => log (p i : ℝ)) (log R) Q ^ 2 := by
  have hh := soft_square_lower (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p)
    (primeLogLocation_nonneg p) (log R) 1 (log_natCast_nonneg R)
    (fun t ht => cumulative_prime_lower p hp hinj R hR hfull t ht.1 ht.2)
  simpa only [one_mul, softProfile, primeLogLocation] using hh

#print axioms cumulative_prime_upper
#print axioms cumulative_prime_lower
#print axioms prime_soft_square_lower
end Erdos970.FiniteSelberg
