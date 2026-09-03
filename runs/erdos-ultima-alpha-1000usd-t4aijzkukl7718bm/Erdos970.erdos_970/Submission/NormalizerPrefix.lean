import Submission.PrimeExponentialMoment
import Submission.SmoothNormalizerLower
import Submission.PrimeSupportMassBarrier

/-! Strict-prefix normalizer bounds and reciprocal Rankin tails. These are
ingredients for a first-hit sieve, not a bound for Jacobsthal's function. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma prime_density_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have := (div_lt_one hp0).mpr hp1
  linarith

lemma eulerMass_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : 0 < eulerMass P := by
  apply prod_pos
  intro p hp
  exact inv_pos.mpr (prime_density_pos (hP p hp))

lemma primeNormalizer_remove_le (P : Finset ℕ) (p N : ℕ)
    (hP : ∀ q ∈ P, q.Prime) (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) * primeNormalizer (insert p P) N ≤ primeNormalizer P N := by
  have hh := mul_le_mul_of_nonneg_left (primeNormalizer_insert_le P p N hP hp)
    (prime_density_pos hp).le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have he : (1 - 1 / (p : ℝ)) * (1 + 1 / ((p : ℝ) - 1)) = 1 := by
    field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
    <;> ring
  simpa only [← mul_assoc, he, one_mul] using hh

lemma primesBelow_succ_eq_insert {p : ℕ} (hp : p.Prime) :
    (p + 1).primesBelow = insert p p.primesBelow := by
  ext q
  simp only [Nat.mem_primesBelow, mem_insert]
  constructor
  · rintro ⟨hqp, hq⟩
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr ⟨by omega, hq⟩
  · rintro (rfl | ⟨hqp, hq⟩)
    · exact ⟨by omega, hp⟩
    · exact ⟨by omega, hq⟩

lemma eulerMass_strict_prefix {p : ℕ} (hp : p.Prime) :
    eulerMass p.primesBelow = (1 - 1 / (p : ℝ)) * eulerMass (p + 1).primesBelow := by
  rw [primesBelow_succ_eq_insert hp]
  have hnot : p ∉ p.primesBelow := by simp [Nat.mem_primesBelow]
  unfold eulerMass
  rw [prod_insert hnot, ← mul_assoc, mul_inv_cancel₀ (prime_density_pos hp).ne', one_mul]

lemma normalizer_strict_prefix_ge {p N : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) * primeNormalizer (p + 1).primesBelow N ≤
      primeNormalizer p.primesBelow N := by
  rw [primesBelow_succ_eq_insert hp]
  exact primeNormalizer_remove_le _ _ _ (fun q hq => (Nat.mem_primesBelow.mp hq).2) hp

/-- Removing the largest prime cannot worsen the relative omitted mass. -/
lemma normalizer_strict_prefix_tail {p N : ℕ} (hp : p.Prime) (r : ℝ)
    (ht : eulerMass (p + 1).primesBelow - primeNormalizer (p + 1).primesBelow N ≤
      eulerMass (p + 1).primesBelow * r) :
    eulerMass p.primesBelow - primeNormalizer p.primesBelow N ≤
      eulerMass p.primesBelow * r := by
  have hh := mul_le_mul_of_nonneg_left ht (prime_density_pos hp).le
  have hn := normalizer_strict_prefix_ge (N := N) hp
  rw [eulerMass_strict_prefix hp]
  nlinarith only [hh, hn]

/-- The absolute loss from passing to the strict prefix is at most three
in the range 1<=log N/log p<=3. -/
theorem strict_normalizer_lower_through_cube (p N : ℕ) (hp : p.Prime)
    (hpN : p ≤ N) (hL : 1 ≤ log (p : ℝ)) (u : ℝ) (hu : 1 ≤ u) (hu3 : u ≤ 3)
    (hlog : log (N : ℝ) = u * log (p : ℝ)) :
    (2 * u - 1 - u * log u) * log (p : ℝ) -
      12 * (WeightedMertens.boundConstant + 1) - 3 ≤ primeNormalizer p.primesBelow N := by
  let B : ℝ := (2 * u - 1 - u * log u) * log (p : ℝ) -
    12 * (WeightedMertens.boundConstant + 1)
  have hb : B ≤ primeNormalizer (p + 1).primesBelow N :=
    primeNormalizer_lower_through_cube p N hp.two_le hpN hL u hu hu3 hlog
  have hmul := mul_le_mul_of_nonneg_left hb (prime_density_pos hp).le
  have hn := normalizer_strict_prefix_ge (N := N) hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hC := WeightedMertens.boundConstant_pos
  have hu0 : 0 < u := by linarith
  have hlu := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hu0) hu0.le
  have hulu : u - 1 ≤ u * log u := by
    simpa only [mul_sub, mul_one, mul_inv_cancel₀ hu0.ne'] using hlu
  have hg : 2 * u - 1 - u * log u ≤ 3 := by linarith
  have hlp := log_le_sub_one_of_pos hp0
  have hBp : B ≤ 3 * (p : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hg (log_natCast_nonneg p)
    dsimp [B]
    linarith
  have hdiv : B / (p : ℝ) ≤ 3 := (div_le_iff₀ hp0).mpr hBp
  change B - 3 ≤ _
  have he : (1 - 1 / (p : ℝ)) * B = B - B / p := by ring
  rw [he] at hmul
  linarith

lemma reciprocal_excess_of_relative_tail (E G r : ℝ) (hE : 0 < E)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht : E - G ≤ E * r / 4) :
    0 < G ∧ 1 / G - 1 / E ≤ r / (3 * E) := by
  have hEr := mul_le_mul_of_nonneg_left hr1 hE.le
  have hGlo : 3 * E / 4 ≤ G := by linarith
  have hG : 0 < G := by linarith
  refine ⟨hG, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 3 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hGlo hr0
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hG).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < 3 * E by positivity)).mp
  field_simp
  nlinarith only [h1, h2]

/-- A strict-prefix reciprocal tail with no unmentioned largest-prime loss. -/
theorem strict_normalizer_reciprocal_rankin (p N : ℕ) (hp : p.Prime) (hN : 0 < N)
    (hL : 50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (u : ℝ) (hu : 3 ≤ u) (hlog : log (N : ℝ) = u * log (p : ℝ)) :
    0 < primeNormalizer p.primesBelow N ∧
    1 / primeNormalizer p.primesBelow N - 1 / eulerMass p.primesBelow ≤
      exp (-2 * (u - 3)) / (3 * eulerMass p.primesBelow) := by
  have he := eulerMass_pos (p + 1).primesBelow
    (fun q hq => (WeightedMertens.mem_primes.mp hq).1)
  have ht := (initial_normalizer_rankin_tail p N hN hL u hlog).trans
    (mul_le_mul_of_nonneg_left (rankin_exponential_le_quarter u) he.le)
  have ht' := normalizer_strict_prefix_tail (N := N) hp
    ((1 / 4 : ℝ) * exp (-2 * (u - 3))) ht
  apply reciprocal_excess_of_relative_tail _ _ _
    (eulerMass_pos _ (fun q hq => (Nat.mem_primesBelow.mp hq).2)) (exp_pos _).le
    (by rw [exp_le_one_iff]; linarith)
  convert ht' using 1 <;> ring

lemma eulerMass_strict_prefix_ge_three_halves (p : ℕ) (hp : p.Prime)
    (hL : supportMassLogThreshold ≤ log (p : ℝ)) :
    (3 / 2 : ℝ) * log (p : ℝ) ≤ eulerMass p.primesBelow := by
  have hh := mul_le_mul_of_nonneg_left
    (eulerMass_initial_ge_three_halves p hp.two_le hL) (prime_density_pos hp).le
  rw [← eulerMass_strict_prefix hp] at hh
  apply le_trans _ hh
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hA : 1 ≤ additiveNormalizerConstant := by
    unfold additiveNormalizerConstant
    linarith [exp_pos (4 * radicalTailSeries)]
  have hprod := mul_le_mul_of_nonneg_right hA (sub_nonneg.mpr hp1)
  have hlog := log_le_sub_one_of_pos hp0
  apply (mul_le_mul_iff_right₀ hp0).mp
  field_simp
  nlinarith only [hprod, hlog]

/-- The reciprocal excess is integrable in the logarithmic cutoff ratio.
Both the log threshold and the strict-prefix convention are explicit. -/
theorem strict_normalizer_reciprocal_log_tail (p N : ℕ) (hp : p.Prime) (hN : 0 < N)
    (hL : 50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hL' : supportMassLogThreshold ≤ log (p : ℝ))
    (u : ℝ) (hu : 3 ≤ u) (hlog : log (N : ℝ) = u * log (p : ℝ)) :
    1 / primeNormalizer p.primesBelow N - 1 / eulerMass p.primesBelow ≤
      2 * exp (-2 * (u - 3)) / (9 * log (p : ℝ)) := by
  have ht := (strict_normalizer_reciprocal_rankin p N hp hN hL u hu hlog).2
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have he := eulerMass_strict_prefix_ge_three_halves p hp hL'
  apply ht.trans
  have hh := div_le_div_of_nonneg_left (exp_pos (-2 * (u - 3))).le
    (show 0 < 3 * ((3 / 2 : ℝ) * log (p : ℝ)) by positivity)
    (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 3))
  convert hh using 1 <;> ring

#print axioms eulerMass_strict_prefix_ge_three_halves
#print axioms strict_normalizer_reciprocal_log_tail

#print axioms strict_normalizer_lower_through_cube
#print axioms strict_normalizer_reciprocal_rankin
end Erdos970.FiniteSelberg
