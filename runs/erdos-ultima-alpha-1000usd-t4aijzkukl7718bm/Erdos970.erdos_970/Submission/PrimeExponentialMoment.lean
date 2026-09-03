import Submission.NormalizerRankin

/-! A bounded positive exponential moment for the squarefree divisor
measure. This is a normalizer estimate, not a Laplace bound for interval
survivors and not a quadratic Jacobsthal theorem. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter

private lemma nonneg_of_derivative_on_two (f g : ℝ → ℝ)
    (h0 : f 0 = 0) (hd : ∀ x, HasDerivAt f (g x) x)
    (hg : ∀ x, 0 ≤ x → x ≤ 2 → 0 ≤ g x) (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ f x := by
  have hm : MonotoneOn f (Set.Icc 0 2) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 2)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hg x (interior_subset hx).1 (interior_subset hx).2)
  have hh := hm (by norm_num : (0 : ℝ) ∈ Set.Icc 0 2) ⟨hx, hx2⟩ hx
  simpa only [h0] using hh

private lemma positive_exp_remainder_0 (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 9 - exp x := by
  have h1 := mul_self_le_mul_self (exp_pos 1).le exp_one_lt_three.le
  have he : exp (2 : ℝ) = exp 1 * exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
  have hh := (exp_le_exp.mpr hx2).trans (by simpa only [he] using h1)
  linarith

private lemma positive_exp_remainder_1 (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 1 + 9 * (x) - exp x := by
  apply nonneg_of_derivative_on_two
    (fun x => 1 + 9 * (x) - exp x) (fun x => 9 - exp x)
    (by norm_num) ?_ (fun x hx hx2 => positive_exp_remainder_0 x hx hx2) x hx hx2
  intro x
  convert ((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).const_mul 9)).sub (hasDerivAt_exp x) using 1 <;> simp [id] <;> ring

private lemma positive_exp_remainder_2 (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 1 + x + 9 * (x ^ 2 / 2) - exp x := by
  apply nonneg_of_derivative_on_two
    (fun x => 1 + x + 9 * (x ^ 2 / 2) - exp x) (fun x => 1 + 9 * (x) - exp x)
    (by norm_num) ?_ (fun x hx hx2 => positive_exp_remainder_1 x hx hx2) x hx hx2
  intro x
  convert (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add ((((hasDerivAt_id x).pow 2).div_const 2).const_mul 9)).sub (hasDerivAt_exp x) using 1 <;> simp [id] <;> ring

private lemma positive_exp_remainder_3 (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 1 + x + x ^ 2 / 2 + 9 * (x ^ 3 / 6) - exp x := by
  apply nonneg_of_derivative_on_two
    (fun x => 1 + x + x ^ 2 / 2 + 9 * (x ^ 3 / 6) - exp x) (fun x => 1 + x + 9 * (x ^ 2 / 2) - exp x)
    (by norm_num) ?_ (fun x hx hx2 => positive_exp_remainder_2 x hx hx2) x hx hx2
  intro x
  convert ((((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)).add ((((hasDerivAt_id x).pow 3).div_const 6).const_mul 9)).sub (hasDerivAt_exp x) using 1 <;> simp [id] <;> ring

private lemma positive_exp_remainder_4 (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + 9 * (x ^ 4 / 24) - exp x := by
  apply nonneg_of_derivative_on_two
    (fun x => 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + 9 * (x ^ 4 / 24) - exp x) (fun x => 1 + x + x ^ 2 / 2 + 9 * (x ^ 3 / 6) - exp x)
    (by norm_num) ?_ (fun x hx hx2 => positive_exp_remainder_3 x hx hx2) x hx hx2
  intro x
  convert (((((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 6)).add ((((hasDerivAt_id x).pow 4).div_const 24).const_mul 9)).sub (hasDerivAt_exp x) using 1 <;> simp [id] <;> ring

private lemma positive_exp_remainder_5 (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + 9 * (x ^ 5 / 120) - exp x := by
  apply nonneg_of_derivative_on_two
    (fun x => 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + 9 * (x ^ 5 / 120) - exp x) (fun x => 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + 9 * (x ^ 4 / 24) - exp x)
    (by norm_num) ?_ (fun x hx hx2 => positive_exp_remainder_4 x hx hx2) x hx hx2
  intro x
  convert ((((((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 4).div_const 24)).add ((((hasDerivAt_id x).pow 5).div_const 120).const_mul 9)).sub (hasDerivAt_exp x) using 1 <;> simp [id] <;> ring

lemma exp_sub_one_le_fifth_on_two (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    exp x - 1 ≤ x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + 9 * x ^ 5 / 120 := by
  linarith only [positive_exp_remainder_5 x hx hx2]

lemma prime_positive_exp_sum_upper (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) :
    (∑ p ∈ (R + 1).primesBelow, (exp (2 * log (p : ℝ) / log (R : ℝ)) - 1) / p) ≤
      1841 / 450 + 17 * WeightedMertens.sharpMomentError / log (R : ℝ) := by
  let L : ℝ := log (R : ℝ)
  let M (j : ℕ) : ℝ := ∑ p ∈ (R + 1).primesBelow, (2 * log (p : ℝ) / L) ^ j / p
  have hm (n : ℕ) : |M (n + 1) - (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)| ≤
      (2 : ℝ) ^ (n + 2) * WeightedMertens.sharpMomentError / L :=
    scaled_prime_log_moment R hR hL n
  have h1 := (abs_le.mp (hm 0)).2
  have h2 := (abs_le.mp (hm 1)).2
  have h3 := (abs_le.mp (hm 2)).2
  have h4 := (abs_le.mp (hm 3)).2
  have h5 := (abs_le.mp (hm 4)).2
  norm_num only [Nat.cast_ofNat, zero_add, zero_pow, pow_succ] at h1 h2 h3 h4 h5
  have hsum : (∑ p ∈ (R + 1).primesBelow, (exp (2 * log (p : ℝ) / L) - 1) / p) ≤
      M 1 + M 2 / 2 + M 3 / 6 + M 4 / 24 + 9 * M 5 / 120 := by
    calc
      _ ≤ ∑ p ∈ (R + 1).primesBelow,
          ((2 * log (p : ℝ) / L) + (2 * log (p : ℝ) / L) ^ 2 / 2 +
            (2 * log (p : ℝ) / L) ^ 3 / 6 + (2 * log (p : ℝ) / L) ^ 4 / 24 +
              9 * (2 * log (p : ℝ) / L) ^ 5 / 120) / p := by
        apply sum_le_sum
        intro p hp
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
        apply exp_sub_one_le_fifth_on_two _
          (div_nonneg (mul_nonneg (by norm_num) (log_natCast_nonneg p)) hL.le)
        apply (div_le_iff₀ hL).mpr
        have hh := log_le_log
          (show (0 : ℝ) < p by exact_mod_cast (WeightedMertens.mem_primes.mp hp).1.pos)
          (show (p : ℝ) ≤ R by exact_mod_cast (WeightedMertens.mem_primes.mp hp).2)
        linarith
      _ = _ := by
        have he (p : ℕ) :
            ((2 * log (p : ℝ) / L) + (2 * log (p : ℝ) / L) ^ 2 / 2 +
              (2 * log (p : ℝ) / L) ^ 3 / 6 + (2 * log (p : ℝ) / L) ^ 4 / 24 +
                9 * (2 * log (p : ℝ) / L) ^ 5 / 120) / p =
            (2 * log (p : ℝ) / L) ^ 1 / p + ((2 * log (p : ℝ) / L) ^ 2 / p) / 2 +
              ((2 * log (p : ℝ) / L) ^ 3 / p) / 6 + ((2 * log (p : ℝ) / L) ^ 4 / p) / 24 +
                9 * ((2 * log (p : ℝ) / L) ^ 5 / p) / 120 := by ring
        simp only [he, sum_add_distrib, ← sum_div, ← mul_sum]
        rfl
  have hE : 0 ≤ WeightedMertens.sharpMomentError / L :=
    div_nonneg WeightedMertens.sharpMomentError_pos.le hL.le
  change (∑ p ∈ (R + 1).primesBelow, (exp (2 * log (p : ℝ) / L) - 1) / p) ≤
    1841 / 450 + 17 * WeightedMertens.sharpMomentError / L
  simp only [mul_div_assoc] at h1 h2 h3 h4 h5 hsum ⊢
  linarith

lemma prime_positive_exp_sum_le_nine_halves (R : ℕ)
    (hL : 50 * WeightedMertens.sharpMomentError ≤ log (R : ℝ)) :
    (∑ p ∈ (R + 1).primesBelow, (exp ((2 / log (R : ℝ)) * log (p : ℝ)) - 1) / p) ≤ 9 / 2 := by
  have hM := WeightedMertens.sharpMomentError_pos
  have hLp : 0 < log (R : ℝ) := by linarith
  have hR : 0 < R := by
    by_contra h
    have hz : R = 0 := by omega
    simp only [hz, Nat.cast_zero, log_zero] at hLp
    exact lt_irrefl _ hLp
  have hh := prime_positive_exp_sum_upper R hR hLp
  have hdiv : 17 * WeightedMertens.sharpMomentError / log (R : ℝ) ≤ 17 / 50 := by
    apply (div_le_iff₀ hLp).mpr
    linarith
  have he (p : ℕ) : (2 / log (R : ℝ)) * log (p : ℝ) =
      2 * log (p : ℝ) / log (R : ℝ) := by ring
  simp_rw [he]
  linarith

/-- A fully explicit normalizer tail bound past a fixed prime cutoff. -/
theorem initial_normalizer_rankin_tail (R N : ℕ) (hN : 0 < N)
    (hL : 50 * WeightedMertens.sharpMomentError ≤ log (R : ℝ)) (u : ℝ)
    (hlog : log (N : ℝ) = u * log (R : ℝ)) :
    eulerMass (R + 1).primesBelow - primeNormalizer (R + 1).primesBelow N ≤
      eulerMass (R + 1).primesBelow * exp (9 / 2 - 2 * u) := by
  have hLp : 0 < log (R : ℝ) := by linarith [WeightedMertens.sharpMomentError_pos]
  have hh := eulerMass_sub_normalizer_rankin (R + 1).primesBelow
    (fun p hp => (WeightedMertens.mem_primes.mp hp).1) N hN
    (2 / log (R : ℝ)) (by positivity)
  have he : (2 / log (R : ℝ)) * log (N : ℝ) = 2 * u := by
    rw [hlog]
    field_simp
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (sub_le_sub_right (prime_positive_exp_sum_le_nine_halves R hL) _))
  unfold eulerMass
  apply prod_nonneg
  intro p hp
  have hpp : (1 : ℝ) < p := by exact_mod_cast (WeightedMertens.mem_primes.mp hp).1.one_lt
  have hdiv : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpp
  exact inv_nonneg.mpr (by linarith)

lemma rankin_exponential_le_quarter (u : ℝ) :
    exp (9 / 2 - 2 * u) ≤ (1 / 4 : ℝ) * exp (-2 * (u - 3)) := by
  have he : (4 : ℝ) ≤ exp (3 / 2 : ℝ) := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 4
    norm_num [sum_range_succ] at hh
    linarith
  have hinv : exp (-(3 / 2 : ℝ)) ≤ 1 / 4 := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  have hid : 9 / 2 - 2 * u = -(3 / 2 : ℝ) + -2 * (u - 3) := by ring
  rw [hid, exp_add]
  exact mul_le_mul_of_nonneg_right hinv (exp_pos _).le

#print axioms exp_sub_one_le_fifth_on_two
#print axioms prime_positive_exp_sum_upper
#print axioms initial_normalizer_rankin_tail
#print axioms rankin_exponential_le_quarter
end Erdos970.FiniteSelberg
