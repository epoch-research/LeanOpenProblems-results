import Submission.PrimeLogMoments

/-! A square-root split improves the second logarithmic prime moment. -/
namespace Erdos970.WeightedMertens
open Finset Real

noncomputable def logMomentOffset : ℝ := 1 + errorConstant + 2 * log 4

lemma log_four_le_offset : log (4 : ℝ) ≤ logMomentOffset := by
  have h4 := log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have he := errorConstant_nonneg
  unfold logMomentOffset
  linarith

lemma logMomentOffset_pos : 0 < logMomentOffset := by
  have h4 := log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have he := errorConstant_nonneg
  unfold logMomentOffset
  linarith

lemma log_square_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (t : ℝ)
    (ht : ∀ p ∈ S, log (p : ℝ) ≤ t) :
    (∑ p ∈ S, log p ^ 2 / p) ≤ t * ∑ p ∈ S, log p / p := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
  have hlog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast (hS p hp).one_le)
  have hh := mul_le_mul_of_nonneg_right (ht p hp) hlog
  have he : t * (log p / p) = (t * log p) / p := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hp0.le
  nlinarith only [hh]

lemma prime_second_log_upper (z : ℕ) (hz : 0 < z) :
    (∑ p ∈ (z + 1).primesBelow, log p ^ 2 / p) ≤
      (3 / 4) * log (z : ℝ) ^ 2 + logMomentOffset * log z := by
  let r := Nat.sqrt z
  let Q := (z + 1).primesBelow
  have hr : 0 < r := Nat.sqrt_pos.mpr hz
  have hrz : r ≤ z := Nat.sqrt_le_self z
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlz : 0 ≤ log (z : ℝ) := log_nonneg (by exact_mod_cast hz)
  have hsq : (r : ℝ) ^ 2 ≤ z := by
    have hh : r ^ 2 ≤ z := by simpa only [r, pow_two] using Nat.sqrt_le z
    exact_mod_cast hh
  have hlogr : 2 * log (r : ℝ) ≤ log z := by
    have hh := log_le_log (by positivity : (0 : ℝ) < (r : ℝ) ^ 2) hsq
    simpa only [log_pow, Nat.cast_ofNat] using hh
  have hzsq : (z : ℝ) ≤ 4 * (r : ℝ) ^ 2 := by
    have hh := Nat.lt_succ_sqrt' z
    change z < (r + 1) ^ 2 at hh
    have hnat : z ≤ 4 * r ^ 2 := by nlinarith
    exact_mod_cast hnat
  have hlogr' : log (z : ℝ) ≤ log 4 + 2 * log r := by
    have hh := log_le_log hz0 hzsq
    simpa only [log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hr0.ne'),
      log_pow, Nat.cast_ofNat] using hh
  have hsub : Q.filter (fun p => p ≤ r) = (r + 1).primesBelow := by
    ext p
    simp only [Q, mem_filter, mem_primes]
    exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2.trans hrz⟩, hh.2⟩⟩
  have hsplit1 := sum_filter_add_sum_filter_not Q (fun p => p ≤ r) (fun p => log p / p)
  rw [hsub] at hsplit1
  change primeSum r + (∑ p ∈ Q.filter (fun p => ¬p ≤ r), log p / p) = primeSum z at hsplit1
  have hlo := log_square_sum_le (Q.filter (fun p => p ≤ r))
    (fun p hp => (mem_primes.mp (mem_filter.mp hp).1).1) ((1 / 2) * log z) (by
      intro p hp
      have hpp := (mem_primes.mp (mem_filter.mp hp).1).1
      have hh := log_le_log (by exact_mod_cast hpp.pos : (0 : ℝ) < p)
        (by exact_mod_cast (mem_filter.mp hp).2 : (p : ℝ) ≤ r)
      linarith)
  have hhi := log_square_sum_le (Q.filter (fun p => ¬p ≤ r))
    (fun p hp => (mem_primes.mp (mem_filter.mp hp).1).1) (log z) (by
      intro p hp
      have hpp := (mem_primes.mp (mem_filter.mp hp).1).1
      exact log_le_log (by exact_mod_cast hpp.pos)
        (by exact_mod_cast (mem_primes.mp (mem_filter.mp hp).1).2))
  have hsplit2 := sum_filter_add_sum_filter_not Q (fun p => p ≤ r) (fun p => log p ^ 2 / p)
  rw [hsub] at hsplit2
  have hsplit1mul := congrArg (fun v : ℝ => log (z : ℝ) * v) hsplit1
  have hlow : log (r : ℝ) - (1 + errorConstant) ≤ primeSum r := by
    have hh := lower_bound_with_error r hr
    have he := errorSum_le r
    linarith
  have hupper := mul_le_mul_of_nonneg_left (upper_bound z hz) hlz
  have hlower := mul_le_mul_of_nonneg_left hlow hlz
  have hloglower := mul_le_mul_of_nonneg_left hlogr' hlz
  rw [hsub] at hlo
  change _ ≤ (1 / 2) * log z * primeSum r at hlo
  have h4 := log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have he := errorConstant_nonneg
  have hextra := mul_nonneg (by linarith : 0 ≤ (1 : ℝ) + errorConstant + log 4) hlz
  have hextra2 := mul_nonneg h4 hlz
  dsimp only [logMomentOffset]
  change (∑ p ∈ Q, log p ^ 2 / p) ≤ _
  nlinarith only [hlo, hhi, hsplit1mul, hsplit2, hupper, hlower, hloglower, hextra, hextra2]

lemma prime_small_second_log (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ) (hz : 0 < z) :
    (∑ p ∈ P.filter (fun p => p ≤ z), log p ^ 2 / p) ≤
      (3 / 4) * (log z + logMomentOffset) ^ 2 := by
  have hh : (∑ p ∈ P.filter (fun p => p ≤ z), log p ^ 2 / p) ≤
      (∑ p ∈ (z + 1).primesBelow, log p ^ 2 / p) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact mem_primes.mpr ⟨hP p (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
    · intro p hp hn
      positivity
  have hlz : 0 ≤ log (z : ℝ) := log_nonneg (by exact_mod_cast hz)
  have he := logMomentOffset_pos
  have hm := mul_nonneg he.le hlz
  exact hh.trans ((prime_second_log_upper z hz).trans (by nlinarith [sq_nonneg logMomentOffset]))

/-- The first moment is unchanged; the second-moment coefficient improves from
65/64 to49/64 after increasing the fixed additive logarithmic offset. -/
theorem prime_log_moments_improved (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ) (hz : 64 ≤ z) (hsize : 64 * P.card ≤ z) :
    (∑ p ∈ P, log p / p) ≤ (65 / 64) * (log z + logMomentOffset) ∧
    (∑ p ∈ P, log p ^ 2 / p) ≤ (49 / 64) * (log z + logMomentOffset) ^ 2 := by
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlz : 2 ≤ log (z : ℝ) := two_le_log_of_sixty_four_le (by exact_mod_cast hz)
  have hM : 0 < log z + logMomentOffset := by linarith [logMomentOffset_pos]
  refine ⟨(prime_log_moments P hP z hz hsize).1.trans (by linarith [log_four_le_offset]), ?_⟩
  have htail : (∑ p ∈ P.filter (fun p => ¬p ≤ z), log p ^ 2 / p) ≤
      log z ^ 2 / 64 := by
    calc
      _ ≤ ∑ _p ∈ P.filter (fun p => ¬p ≤ z), log z ^ 2 / z := by
        apply sum_le_sum
        intro p hp
        exact log_sq_div_le_of_le hz0 (by exact_mod_cast (by have := (mem_filter.mp hp).2; omega : z ≤ p)) hlz
      _ = ((P.filter (fun p => ¬p ≤ z)).card : ℝ) * (log z ^ 2 / z) := by simp
      _ ≤ (P.card : ℝ) * (log z ^ 2 / z) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_filter_le P (fun p => ¬p ≤ z)) (by positivity)
      _ ≤ log z ^ 2 / 64 := by
        have hsz : (64 : ℝ) * P.card ≤ z := by exact_mod_cast hsize
        have hh := mul_le_mul_of_nonneg_right hsz (sq_nonneg (log (z : ℝ)))
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
        apply (mul_le_mul_iff_right₀ hz0).mp
        have he : (z : ℝ) * ((P.card : ℝ) * (log z ^ 2 / z) * 64) =
            64 * (P.card : ℝ) * log z ^ 2 := by field_simp
        rw [he]
        nlinarith only [hh]
  have hsmall := prime_small_second_log P hP z (by omega)
  have hsplit := sum_filter_add_sum_filter_not P (fun p => p ≤ z) (fun p => log p ^ 2 / p)
  have hsq : log z ^ 2 ≤ (log z + logMomentOffset) ^ 2 := by nlinarith [logMomentOffset_pos]
  linarith

#print axioms prime_second_log_upper
#print axioms prime_log_moments_improved
end Erdos970.WeightedMertens
