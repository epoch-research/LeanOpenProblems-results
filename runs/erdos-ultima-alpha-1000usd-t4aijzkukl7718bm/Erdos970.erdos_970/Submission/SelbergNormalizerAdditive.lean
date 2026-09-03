import Submission.RadicalReciprocalBound
import Submission.CumulativePrimeSharp

/-! An absolute additive logarithmic bound for the Selberg normalizer,
proved by a positive radical-tail argument. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 1000000

lemma primeWeight_fiber_hasSum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    HasSum (fun b : Nat.factoredNumbers Q =>
      1 / (((∏ p ∈ Q, p : ℕ) * b.val : ℕ) : ℝ)) (primeWeight Q : ℝ) := by
  have h := (factored_reciprocal_hasSum Q hQ).mul_left
    (1 / ((∏ p ∈ Q, p : ℕ) : ℝ))
  have he : (1 / ((∏ p ∈ Q, p : ℕ) : ℝ)) *
      (∏ p ∈ Q, (1 - 1 / (p : ℝ))⁻¹) = primeWeight Q := by
    unfold primeWeight
    rw [Nat.cast_prod, one_div, ← prod_inv_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hQ p hp).ne_zero
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have hh : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
      linarith
    field_simp
  rw [he] at h
  convert h using 1
  funext b
  rw [Nat.cast_mul]
  ring

/-- The upper normalizer differs from the harmonic sum by at most an absolute
constant, independent of the cutoff and of which primes are present. -/
theorem primeNormalizer_harmonic_additive (P : Finset ℕ) (R : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeNormalizer P R ≤ (harmonic R : ℝ) + 2 * exp (4 * radicalTailSeries) := by
  classical
  let D := smallDivisorFamily P R
  let X := (Q : D) × Nat.factoredNumbers Q.val
  let d := fun Q : D => ∏ p ∈ Q.val, p
  let N := fun x : X => d x.1 * x.2.val
  have hQP (Q : D) : Q.val ⊆ P := (mem_smallDivisorFamily P Q.val R |>.mp Q.property).1
  have hQ (Q : D) : ∀ p ∈ Q.val, p.Prime := fun p hp => hP p (hQP Q hp)
  have hd (Q : D) : 0 < d Q := prod_pos (fun p hp => (hQ Q p hp).pos)
  have hfac (x : X) : (N x).primeFactors = x.1.val := by
    rw [Nat.primeFactors_mul (hd x.1).ne' (Nat.ne_zero_of_mem_factoredNumbers x.2.property)]
    rw [Nat.primeFactors_prod (hQ x.1)]
    exact union_eq_left.mpr (Nat.primeFactors_subset_of_mem_factoredNumbers x.2.property)
  have hinj : Function.Injective N := by
    intro x y hxy
    have hfst : x.1 = y.1 := Subtype.ext (by rw [← hfac x, ← hfac y, hxy])
    obtain ⟨Q, b⟩ := x
    obtain ⟨T, c⟩ := y
    dsimp only at hfst
    cases hfst
    have hbc : b = c := Subtype.ext (Nat.mul_left_cancel (hd Q) hxy)
    cases hbc
    rfl
  have hf (Q : D) : HasSum (fun b : Nat.factoredNumbers Q.val => 1 / (N ⟨Q, b⟩ : ℝ))
      (primeWeight Q.val) := primeWeight_fiber_hasSum Q.val (hQ Q)
  have hsum : Summable (fun x : X => 1 / (N x : ℝ)) := by
    apply (summable_sigma_of_nonneg (fun _ => by positivity)).mpr
    exact ⟨fun Q => (hf Q).summable, Summable.of_finite⟩
  have htotal : (∑' x : X, 1 / (N x : ℝ)) = primeNormalizer P R := by
    have ht := hsum.hasSum.sigma hf
    have he := ht.unique (hasSum_fintype (fun Q : D => primeWeight Q.val))
    exact he.trans (sum_coe_sort D primeWeight)
  rw [← htotal]
  apply hsum.tsum_le_of_sum_le
  intro s
  rw [← sum_image (f := fun n : ℕ => 1 / (n : ℝ)) (s := s) hinj.injOn]
  apply radical_reciprocal_finite_bound P _ R hP
  intro n hn
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
  have hn0 : N x ≠ 0 := mul_ne_zero (hd x.1).ne'
    (Nat.ne_zero_of_mem_factoredNumbers x.2.property)
  constructor
  · exact Nat.mem_factoredNumbers_of_primeFactors_subset hn0 (by rw [hfac x]; exact hQP x.1)
  · unfold primeRadical
    rw [hfac x]
    exact (mem_smallDivisorFamily P x.1.val R |>.mp x.1.property).2

noncomputable def additiveNormalizerConstant : ℝ := 1 + 2 * exp (4 * radicalTailSeries)

lemma additiveNormalizerConstant_pos : 0 < additiveNormalizerConstant := by
  unfold additiveNormalizerConstant
  positivity

/-- Uniform coefficient one, with a genuinely absolute additive constant. -/
theorem primeNormalizer_log_additive (P : Finset ℕ) (R : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeNormalizer P R ≤ log R + additiveNormalizerConstant := by
  have hh := primeNormalizer_harmonic_additive P R hP
  have hu := harmonic_le_one_add_log R
  unfold additiveNormalizerConstant
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma indexed_normalizer_log_additive (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) :
    normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) ≤
      log R + additiveNormalizerConstant := by
  rw [normalizer_eq_smallDivisorFamily p hp hinj R]
  exact primeNormalizer_log_additive (univ.image p) R
    (fun a ha => by obtain ⟨i, hi, rfl⟩ := mem_image.mp ha; exact hp i)

lemma cumulative_prime_upper_additive (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (t : ℝ) (ht : 0 ≤ t) :
    cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t ≤
      t + additiveNormalizerConstant := by
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
  exact hsum.trans ((indexed_normalizer_log_additive p hp hinj R).trans
    (add_le_add hlog le_rfl))

/-- The cumulative logarithmic mass has a uniformly bounded discrepancy on
  the full cutoff interval. There is no accuracy parameter growing with R. -/
theorem cumulative_prime_error_additive (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (t : ℝ) (ht : 0 ≤ t) (htR : t ≤ log R) :
    |cumulativeMass (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p) t - t| ≤
      additiveNormalizerConstant := by
  have hu := cumulative_prime_upper_additive p hp hinj t ht
  have hl := cumulative_prime_lower p hp hinj R hR hfull t ht htR
  have hc : 1 ≤ additiveNormalizerConstant := by
    unfold additiveNormalizerConstant
    have he := exp_pos (4 * radicalTailSeries)
    linarith
  rw [abs_le]
  constructor <;> linarith

#print axioms cumulative_prime_error_additive
#print axioms primeNormalizer_harmonic_additive
#print axioms primeNormalizer_log_additive
end Erdos970.FiniteSelberg
