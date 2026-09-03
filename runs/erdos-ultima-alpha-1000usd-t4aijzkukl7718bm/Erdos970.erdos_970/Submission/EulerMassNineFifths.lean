import Submission.EulerMassLogUpper

/-! A sharper elementary reciprocal Euler-product bound. The coefficient
9/5 replaces 19/10 in the variable-cutoff sieve, without using a prime number
theorem or a sharp Mertens-product asymptotic. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open scoped Topology

private lemma nonneg_from_derivative (f g : ℝ → ℝ)
    (h0 : f 0 = 0) (hd : ∀ x, HasDerivAt f (g x) x)
    (hg : ∀ x, 0 ≤ x → 0 ≤ g x) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hg x (interior_subset hx))
  simpa only [h0] using hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx

private lemma remainder_five (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 + exp (-x) := by
  linarith only [one_sub_exp_neg_le_fifth x hx]

private lemma remainder_6 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - exp (-x) := by
  apply nonneg_from_derivative
    (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - exp (-x)) (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 + exp (-x))
    (by norm_num) ?_ (fun x hx => remainder_five x hx) x hx
  intro x
  convert ((((((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (((hasDerivAt_id x).pow 5).div_const 120)).add (((hasDerivAt_id x).pow 6).div_const 720)).sub ((hasDerivAt_neg x).exp)) using 1 <;> simp [id] <;> ring

private lemma remainder_7 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 + exp (-x) := by
  apply nonneg_from_derivative
    (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 + exp (-x)) (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - exp (-x))
    (by norm_num) ?_ (fun x hx => remainder_6 x hx) x hx
  intro x
  convert (((((((((hasDerivAt_const x (-1 : ℝ)).add (hasDerivAt_id x)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 6)).sub (((hasDerivAt_id x).pow 4).div_const 24)).add (((hasDerivAt_id x).pow 5).div_const 120)).sub (((hasDerivAt_id x).pow 6).div_const 720)).add (((hasDerivAt_id x).pow 7).div_const 5040)).add ((hasDerivAt_neg x).exp)) using 1 <;> simp [id] <;> ring

private lemma remainder_8 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - exp (-x) := by
  apply nonneg_from_derivative
    (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - exp (-x)) (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 + exp (-x))
    (by norm_num) ?_ (fun x hx => remainder_7 x hx) x hx
  intro x
  convert ((((((((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (((hasDerivAt_id x).pow 5).div_const 120)).add (((hasDerivAt_id x).pow 6).div_const 720)).sub (((hasDerivAt_id x).pow 7).div_const 5040)).add (((hasDerivAt_id x).pow 8).div_const 40320)).sub ((hasDerivAt_neg x).exp)) using 1 <;> simp [id] <;> ring

private lemma remainder_9 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 - x ^ 8 / 40320 + x ^ 9 / 362880 + exp (-x) := by
  apply nonneg_from_derivative
    (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 - x ^ 8 / 40320 + x ^ 9 / 362880 + exp (-x)) (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - exp (-x))
    (by norm_num) ?_ (fun x hx => remainder_8 x hx) x hx
  intro x
  convert (((((((((((hasDerivAt_const x (-1 : ℝ)).add (hasDerivAt_id x)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 6)).sub (((hasDerivAt_id x).pow 4).div_const 24)).add (((hasDerivAt_id x).pow 5).div_const 120)).sub (((hasDerivAt_id x).pow 6).div_const 720)).add (((hasDerivAt_id x).pow 7).div_const 5040)).sub (((hasDerivAt_id x).pow 8).div_const 40320)).add (((hasDerivAt_id x).pow 9).div_const 362880)).add ((hasDerivAt_neg x).exp)) using 1 <;> simp [id] <;> ring

private lemma remainder_10 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - x ^ 9 / 362880 + x ^ 10 / 3628800 - exp (-x) := by
  apply nonneg_from_derivative
    (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - x ^ 9 / 362880 + x ^ 10 / 3628800 - exp (-x)) (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 - x ^ 8 / 40320 + x ^ 9 / 362880 + exp (-x))
    (by norm_num) ?_ (fun x hx => remainder_9 x hx) x hx
  intro x
  convert ((((((((((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (((hasDerivAt_id x).pow 5).div_const 120)).add (((hasDerivAt_id x).pow 6).div_const 720)).sub (((hasDerivAt_id x).pow 7).div_const 5040)).add (((hasDerivAt_id x).pow 8).div_const 40320)).sub (((hasDerivAt_id x).pow 9).div_const 362880)).add (((hasDerivAt_id x).pow 10).div_const 3628800)).sub ((hasDerivAt_neg x).exp)) using 1 <;> simp [id] <;> ring

private lemma remainder_11 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 - x ^ 8 / 40320 + x ^ 9 / 362880 - x ^ 10 / 3628800 + x ^ 11 / 39916800 + exp (-x) := by
  apply nonneg_from_derivative
    (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 - x ^ 8 / 40320 + x ^ 9 / 362880 - x ^ 10 / 3628800 + x ^ 11 / 39916800 + exp (-x)) (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 120 + x ^ 6 / 720 - x ^ 7 / 5040 + x ^ 8 / 40320 - x ^ 9 / 362880 + x ^ 10 / 3628800 - exp (-x))
    (by norm_num) ?_ (fun x hx => remainder_10 x hx) x hx
  intro x
  convert (((((((((((((hasDerivAt_const x (-1 : ℝ)).add (hasDerivAt_id x)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 6)).sub (((hasDerivAt_id x).pow 4).div_const 24)).add (((hasDerivAt_id x).pow 5).div_const 120)).sub (((hasDerivAt_id x).pow 6).div_const 720)).add (((hasDerivAt_id x).pow 7).div_const 5040)).sub (((hasDerivAt_id x).pow 8).div_const 40320)).add (((hasDerivAt_id x).pow 9).div_const 362880)).sub (((hasDerivAt_id x).pow 10).div_const 3628800)).add (((hasDerivAt_id x).pow 11).div_const 39916800)).add ((hasDerivAt_neg x).exp)) using 1 <;> simp [id] <;> ring

lemma one_sub_exp_neg_le_eleventh (x : ℝ) (hx : 0 ≤ x) :
    1 - exp (-x) ≤ x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 / 720 + x ^ 7 / 5040 - x ^ 8 / 40320 + x ^ 9 / 362880 - x ^ 10 / 3628800 + x ^ 11 / 39916800 := by
  linarith only [remainder_11 x hx]

lemma scaled_prime_log_moment_any (A : ℝ) (hA : 0 ≤ A) (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) (n : ℕ) :
    |(∑ p ∈ (R + 1).primesBelow, (A * log (p : ℝ) / log (R : ℝ)) ^ (n + 1) / p) -
      A ^ (n + 1) / ((n : ℝ) + 1)| ≤
      2 * A ^ (n + 1) * WeightedMertens.sharpMomentError / log (R : ℝ) := by
  let L : ℝ := log (R : ℝ)
  have hL0 : L ≠ 0 := hL.ne'
  have hs (j : ℕ) :
      (∑ p ∈ (R + 1).primesBelow, (A * log (p : ℝ) / L) ^ j / p) =
      (A / L) ^ j * ∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ j / p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [show A * log (p : ℝ) / L = (A / L) * log (p : ℝ) by ring, mul_pow]
    ring
  change |(∑ p ∈ (R + 1).primesBelow, (A * log (p : ℝ) / L) ^ (n + 1) / p) -
      A ^ (n + 1) / ((n : ℝ) + 1)| ≤
      2 * A ^ (n + 1) * WeightedMertens.sharpMomentError / L
  rw [hs]
  rcases n with _ | n
  · have hh := mul_le_mul_of_nonneg_left (WeightedMertens.abs_primeSum_sub_log R hR)
      (show 0 ≤ A / L by positivity)
    have he : (A / L) * WeightedMertens.primeSum R - A =
        (A / L) * (WeightedMertens.primeSum R - L) := by field_simp <;> ring
    simp only [zero_add, Nat.cast_zero, pow_one, div_one]
    change |(A / L) * WeightedMertens.primeSum R - A| ≤ _
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ A / L)]
    apply hh.trans
    have hc : WeightedMertens.boundConstant ≤ 2 * WeightedMertens.sharpMomentError := by
      unfold WeightedMertens.sharpMomentError
      linarith [WeightedMertens.boundConstant_pos]
    have hh' := mul_le_mul_of_nonneg_left hc (show 0 ≤ A / L by positivity)
    convert hh' using 1 <;> norm_num <;> ring
  · have hh := mul_le_mul_of_nonneg_left (WeightedMertens.prime_log_moment R hR n)
      (show 0 ≤ (A / L) ^ (n + 2) by positivity)
    have he : (A / L) ^ (n + 2) *
        ((∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ (n + 2) / p) -
          L ^ (n + 2) / ((n : ℝ) + 2)) =
        (A / L) ^ (n + 2) * (∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ (n + 2) / p) -
          A ^ (n + 2) / ((n : ℝ) + 2) := by
      rw [mul_sub, div_pow]
      congr 1
      field_simp
    have he' : (A / L) ^ (n + 2) * (2 * WeightedMertens.sharpMomentError * L ^ (n + 1)) =
        2 * A ^ (n + 2) * WeightedMertens.sharpMomentError / L := by
      rw [div_pow]
      field_simp
      ring
    rw [← abs_of_nonneg (show 0 ≤ (A / L) ^ (n + 2) by positivity), ← abs_mul] at hh
    rw [abs_of_nonneg (show 0 ≤ (A / L) ^ (n + 2) by positivity)] at hh
    change |(A / L) ^ (n + 2) * (_ - L ^ (n + 2) / ((n : ℝ) + 2))| ≤
      (A / L) ^ (n + 2) * (2 * WeightedMertens.sharpMomentError * L ^ (n + 1)) at hh
    rw [he, he'] at hh
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, one_add_one_eq_two] using hh


lemma prime_exp_four_difference_sum_upper (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) :
    (∑ p ∈ (R + 1).primesBelow, (1 - exp (-(4 * log (p : ℝ) / log (R : ℝ)))) / p) ≤
      1064111336 / 540280125 + 108 * WeightedMertens.sharpMomentError / log (R : ℝ) := by
  let L : ℝ := log (R : ℝ)
  let M (j : ℕ) : ℝ := ∑ p ∈ (R + 1).primesBelow, (4 * log (p : ℝ) / L) ^ j / p
  have hm (n : ℕ) : |M (n + 1) - (4 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)| ≤
      2 * (4 : ℝ) ^ (n + 1) * WeightedMertens.sharpMomentError / L :=
    scaled_prime_log_moment_any 4 (by norm_num) R hR hL n
  have h1 := (abs_le.mp (hm 0)).2
  have h2 := (abs_le.mp (hm 1)).1
  have h3 := (abs_le.mp (hm 2)).2
  have h4 := (abs_le.mp (hm 3)).1
  have h5 := (abs_le.mp (hm 4)).2
  have h6 := (abs_le.mp (hm 5)).1
  have h7 := (abs_le.mp (hm 6)).2
  have h8 := (abs_le.mp (hm 7)).1
  have h9 := (abs_le.mp (hm 8)).2
  have h10 := (abs_le.mp (hm 9)).1
  have h11 := (abs_le.mp (hm 10)).2
  norm_num only [Nat.cast_ofNat, Nat.cast_zero, zero_add, Nat.reduceAdd, pow_succ, pow_zero, mul_one] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have hsum : (∑ p ∈ (R + 1).primesBelow, (1 - exp (-(4 * log (p : ℝ) / L))) / p) ≤
      M 1 - M 2 / 2 + M 3 / 6 - M 4 / 24 + M 5 / 120 - M 6 / 720 + M 7 / 5040 - M 8 / 40320 + M 9 / 362880 - M 10 / 3628800 + M 11 / 39916800 := by
    calc
      _ ≤ ∑ p ∈ (R + 1).primesBelow, ((4 * log (p : ℝ) / L) - (4 * log (p : ℝ) / L) ^ 2 / 2 + (4 * log (p : ℝ) / L) ^ 3 / 6 - (4 * log (p : ℝ) / L) ^ 4 / 24 + (4 * log (p : ℝ) / L) ^ 5 / 120 - (4 * log (p : ℝ) / L) ^ 6 / 720 + (4 * log (p : ℝ) / L) ^ 7 / 5040 - (4 * log (p : ℝ) / L) ^ 8 / 40320 + (4 * log (p : ℝ) / L) ^ 9 / 362880 - (4 * log (p : ℝ) / L) ^ 10 / 3628800 + (4 * log (p : ℝ) / L) ^ 11 / 39916800) / p := by
        apply sum_le_sum
        intro p hp
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
        exact one_sub_exp_neg_le_eleventh _
          (div_nonneg (mul_nonneg (by norm_num) (log_natCast_nonneg p)) hL.le)
      _ = _ := by
        have he (p : ℕ) : ((4 * log (p : ℝ) / L) - (4 * log (p : ℝ) / L) ^ 2 / 2 + (4 * log (p : ℝ) / L) ^ 3 / 6 - (4 * log (p : ℝ) / L) ^ 4 / 24 + (4 * log (p : ℝ) / L) ^ 5 / 120 - (4 * log (p : ℝ) / L) ^ 6 / 720 + (4 * log (p : ℝ) / L) ^ 7 / 5040 - (4 * log (p : ℝ) / L) ^ 8 / 40320 + (4 * log (p : ℝ) / L) ^ 9 / 362880 - (4 * log (p : ℝ) / L) ^ 10 / 3628800 + (4 * log (p : ℝ) / L) ^ 11 / 39916800) / p = (4 * log (p : ℝ) / L) ^ 1 / p - ((4 * log (p : ℝ) / L) ^ 2 / p) / 2 + ((4 * log (p : ℝ) / L) ^ 3 / p) / 6 - ((4 * log (p : ℝ) / L) ^ 4 / p) / 24 + ((4 * log (p : ℝ) / L) ^ 5 / p) / 120 - ((4 * log (p : ℝ) / L) ^ 6 / p) / 720 + ((4 * log (p : ℝ) / L) ^ 7 / p) / 5040 - ((4 * log (p : ℝ) / L) ^ 8 / p) / 40320 + ((4 * log (p : ℝ) / L) ^ 9 / p) / 362880 - ((4 * log (p : ℝ) / L) ^ 10 / p) / 3628800 + ((4 * log (p : ℝ) / L) ^ 11 / p) / 39916800 := by ring
        simp only [he, sum_add_distrib, sum_sub_distrib, ← sum_div]
        rfl
  have hE : 0 ≤ WeightedMertens.sharpMomentError / L :=
    div_nonneg WeightedMertens.sharpMomentError_pos.le hL.le
  change (∑ p ∈ (R + 1).primesBelow, (1 - exp (-(4 * log (p : ℝ) / L))) / p) ≤
    1064111336 / 540280125 + 108 * WeightedMertens.sharpMomentError / L
  simp only [mul_div_assoc] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hsum ⊢
  linarith

lemma prime_exp_four_pred_difference_sum_upper (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) :
    (∑ p ∈ (R + 1).primesBelow,
      (1 - exp (-(4 / log (R : ℝ)) * log (p : ℝ))) / ((p : ℝ) - 1)) ≤
      1064111336 / 540280125 + 112 * WeightedMertens.sharpMomentError / log (R : ℝ) := by
  let L : ℝ := log (R : ℝ)
  have hpt (p : ℕ) (hp : p ∈ (R + 1).primesBelow) :
      (1 - exp (-(4 / L) * log (p : ℝ))) / ((p : ℝ) - 1) ≤
      (1 - exp (-(4 * log (p : ℝ) / L))) / p +
        (4 / L) * (log (p : ℝ) / ((p : ℝ) * (p - 1))) := by
    have hpp : (1 : ℝ) < p := by exact_mod_cast (WeightedMertens.mem_primes.mp hp).1.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hpd : 0 < (p : ℝ) - 1 := by linarith
    have he : -(4 / L) * log (p : ℝ) = -(4 * log (p : ℝ) / L) := by ring
    rw [he]
    have hb : 1 - exp (-(4 * log (p : ℝ) / L)) ≤ 4 * log (p : ℝ) / L := by
      linarith only [Real.add_one_le_exp (-(4 * log (p : ℝ) / L))]
    have hh := div_le_div_of_nonneg_right hb (show 0 ≤ (p : ℝ) * (p - 1) by positivity)
    have hid : (1 - exp (-(4 * log (p : ℝ) / L))) / ((p : ℝ) - 1) =
        (1 - exp (-(4 * log (p : ℝ) / L))) / p +
        (1 - exp (-(4 * log (p : ℝ) / L))) / ((p : ℝ) * (p - 1)) := by
      field_simp
      ring
    rw [hid]
    convert add_le_add_left hh ((1 - exp (-(4 * log (p : ℝ) / L))) / p) using 1 <;> ring
  have hh := sum_le_sum hpt
  rw [sum_add_distrib, ← mul_sum] at hh
  change (∑ p ∈ (R + 1).primesBelow,
      (1 - exp (-(4 / L) * log (p : ℝ))) / ((p : ℝ) - 1)) ≤
      (∑ p ∈ (R + 1).primesBelow, (1 - exp (-(4 * log (p : ℝ) / L))) / p) +
        (4 / L) * WeightedMertens.errorSum R at hh
  have he := mul_le_mul_of_nonneg_left (WeightedMertens.errorSum_le R)
    (show 0 ≤ 4 / L by positivity)
  have hc : WeightedMertens.errorConstant ≤ WeightedMertens.sharpMomentError := by
    unfold WeightedMertens.sharpMomentError WeightedMertens.boundConstant
    have h4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
    linarith
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 / L by positivity)
  have hmain := prime_exp_four_difference_sum_upper R hR hL
  change (∑ p ∈ (R + 1).primesBelow,
      (1 - exp (-(4 / L) * log (p : ℝ))) / ((p : ℝ) - 1)) ≤
      1064111336 / 540280125 + 112 * WeightedMertens.sharpMomentError / L
  dsimp only [L] at hh he hc' ⊢
  linear_combination hh + he + hc' + hmain

/-- An explicit Euler-product bound obtained by comparison with a p-series.
The error in the exponent tends to zero; no PNT or sharp Mertens-product
asymptotic is used. -/
theorem eulerMass_initial_upper_four_explicit (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) :
    eulerMass (R + 1).primesBelow ≤ (1 + log (R : ℝ) / 4) *
      exp (1064111336 / 540280125 + 112 * WeightedMertens.sharpMomentError / log (R : ℝ)) := by
  have h := eulerMass_power_comparison (R + 1).primesBelow
    (fun p hp => (WeightedMertens.mem_primes.mp hp).1) (4 / log (R : ℝ)) (by positivity)
  have hi : 1 / (4 / log (R : ℝ)) = log (R : ℝ) / 4 := by field_simp
  rw [hi] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (prime_exp_four_pred_difference_sum_upper R hR hL)) (by positivity))

theorem eventually_eulerMass_initial_le_nine_fifths_log :
    ∀ᶠ R : ℕ in atTop, eulerMass (R + 1).primesBelow ≤ (9 / 5 : ℝ) * log (R : ℝ) := by
  have hlog : Tendsto (fun R : ℕ => log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun R : ℕ => (log (R : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlog
  have hlim : Tendsto (fun R : ℕ =>
      ((log (R : ℝ))⁻¹ + 1 / 4) *
        exp (1064111336 / 540280125 + 112 * WeightedMertens.sharpMomentError * (log (R : ℝ))⁻¹))
      atTop (𝓝 ((1 / 4 : ℝ) * exp (1064111336 / 540280125))) := by
    convert (hinv.add_const (1 / 4)).mul
      (Real.continuous_exp.tendsto _ |>.comp
        (tendsto_const_nhds.add (hinv.const_mul (112 * WeightedMertens.sharpMomentError)))) using 1
    norm_num
  have hrate : (1 / 4 : ℝ) * exp (1064111336 / 540280125) < 9 / 5 := by
    have he : exp (1064111336 / 540280125 : ℝ) < 36 / 5 := by
      rw [← exp_log (by norm_num : (0 : ℝ) < 36 / 5)]
      apply exp_lt_exp.mpr
      have hl : log (36 / 5 : ℝ) = 3 * log 2 + log (9 / 10 : ℝ) := by
        rw [show (36 / 5 : ℝ) = 2 ^ (3 : ℕ) * (9 / 10 : ℝ) by norm_num,
          log_mul (by norm_num : (2 : ℝ) ^ (3 : ℕ) ≠ 0) (by norm_num), log_pow]
        norm_num
      have hh := sum_range_sub_log_div_le (x := (-1 / 19 : ℝ)) (by norm_num) 2
      norm_num [sum_range_succ] at hh
      have hlow : -(53 / 500 : ℝ) ≤ log (9 / 10 : ℝ) := by linarith only [(abs_le.mp hh).1]
      rw [hl]
      linarith only [hlow, Real.log_two_gt_d9]
    linarith
  have hb := hlim.eventually_lt_const hrate
  filter_upwards [hb, eventually_ge_atTop 2] with R hR hR2
  have hL : 0 < log (R : ℝ) := log_pos (by exact_mod_cast (show 1 < R by omega))
  have hupper := eulerMass_initial_upper_four_explicit R (by omega) hL
  have he : ((log (R : ℝ))⁻¹ + 1 / 4) *
      exp (1064111336 / 540280125 + 112 * WeightedMertens.sharpMomentError * (log (R : ℝ))⁻¹) * log (R : ℝ) =
      (1 + log (R : ℝ) / 4) *
        exp (1064111336 / 540280125 + 112 * WeightedMertens.sharpMomentError / log (R : ℝ)) := by
    rw [div_eq_mul_inv (112 * WeightedMertens.sharpMomentError)]
    field_simp
  have hh := mul_lt_mul_of_pos_right hR hL
  rw [he] at hh
  exact hupper.trans hh.le

#print axioms one_sub_exp_neg_le_eleventh
#print axioms scaled_prime_log_moment_any
#print axioms eventually_eulerMass_initial_le_nine_fifths_log
end Erdos970.FiniteSelberg
