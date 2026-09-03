import Submission.PrimeAllLogMoments
import Submission.SmoothReciprocalMass

/-! An elementary upper bound for the reciprocal Euler product. These are
auxiliary analytic estimates, not a settlement of the Jacobsthal conjecture. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open scoped Topology

lemma real_pseries_upper (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ 1 + 1 / (s - 1) := by
  have hs0 : 0 < s - 1 := by linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hzero : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (by linarith)
  apply hsum.tsum_le_of_sum_range_le
  intro n
  rcases n with _ | n
  · simp only [range_zero, sum_empty]
    positivity
  rw [sum_range_succ']
  simp only [Nat.cast_zero, hzero, add_zero]
  rcases n with _ | n
  · simp only [range_zero, sum_empty]
    positivity
  rw [sum_range_succ']
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, Real.one_rpow]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc 1 (1 + (n : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_exponent_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hi := hanti.sum_le_integral
  have hnot : (0 : ℝ) ∉ Set.uIcc 1 (1 + (n : ℝ)) := by
    rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) ≤ 1 + (n : ℝ))]
    simp
  rw [integral_rpow (Or.inr ⟨by linarith, hnot⟩), Real.one_rpow] at hi
  have hpow : 0 ≤ (1 + (n : ℝ)) ^ (-s + 1) := Real.rpow_nonneg (by positivity) _
  have hbound : ((1 + (n : ℝ)) ^ (-s + 1) - 1) / (-s + 1) ≤ 1 / (s - 1) := by
    have he : -s + 1 = -(s - 1) := by ring
    rw [he] at hpow
    rw [he, div_neg]
    apply (le_div_iff₀ (by linarith : 0 < s - 1)).mpr
    field_simp
    linarith
  have he : (∑ i ∈ range n, (↑i + 1 + 1 : ℝ) ^ (-s)) =
      ∑ i ∈ range n, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    apply sum_congr rfl
    intro i hi
    push_cast
    congr 1
    ring
  rw [he]
  linarith

noncomputable def negativePowerHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

lemma powered_eulerMass_le_pseries (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s : ℝ) (hs : 1 < s) :
    (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) ≤ 1 + 1 / (s - 1) := by
  have hp (p : ℕ) (hpp : p.Prime) : ‖negativePowerHom s p‖ < 1 := by
    change ‖(p : ℝ) ^ (-s)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := negativePowerHom s) (fun {p} h => hp p h) P).2
  simp only [filter_true_of_mem hP, negativePowerHom, MonoidHom.coe_mk, OneHom.coe_mk] at hh
  have hn : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hc := Summable.tsum_le_tsum_of_inj
    (f := fun n : Nat.factoredNumbers P => (n.val : ℝ) ^ (-s))
    (g := fun n : ℕ => (n : ℝ) ^ (-s)) Subtype.val Subtype.val_injective
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ => le_rfl) hh.summable hn
  rw [hh.tsum_eq] at hc
  exact hc.trans (real_pseries_upper s hs)

lemma eulerMass_power_comparison (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (ht : 0 < t) :
    eulerMass P ≤ (1 + 1 / t) *
      exp (∑ p ∈ P, (1 - exp (-t * log (p : ℝ))) / ((p : ℝ) - 1)) := by
  have hfactor (p : ℕ) (hpp : p ∈ P) :
      (1 - 1 / (p : ℝ))⁻¹ ≤ (1 - (p : ℝ) ^ (-(1 + t)))⁻¹ *
        exp ((1 - exp (-t * log (p : ℝ))) / ((p : ℝ) - 1)) := by
    have hp : (1 : ℝ) < p := by exact_mod_cast (hP p hpp).one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hx : 0 < 1 - 1 / (p : ℝ) := by
      have hh := (div_lt_one hp0).mpr hp
      linarith
    have hy : 0 < 1 - (p : ℝ) ^ (-(1 + t)) := by
      have hh := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith : -(1 + t) < 0)
      linarith
    have he : (p : ℝ) ^ (-(1 + t)) = exp (-t * log (p : ℝ)) / p := by
      rw [show -(1 + t) = -t + (-1) by ring,
        Real.rpow_add hp0, Real.rpow_neg_one, Real.rpow_def_of_pos hp0]
      congr 1
      congr 1
      ring
    have hid : (1 - (p : ℝ) ^ (-(1 + t))) / (1 - 1 / (p : ℝ)) =
        1 + (1 - exp (-t * log (p : ℝ))) / ((p : ℝ) - 1) := by
      rw [he]
      field_simp [hp0.ne', (sub_pos.mpr hp).ne']
      <;> ring
    apply (mul_le_mul_iff_right₀ hy).mp
    have hz := Real.add_one_le_exp ((1 - exp (-t * log (p : ℝ))) / ((p : ℝ) - 1))
    rw [add_comm, ← hid] at hz
    simpa only [← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul, div_eq_mul_inv] using hz
  have hh := prod_le_prod (fun p hp => by
      have hpp : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      have hd : 0 < 1 - 1 / (p : ℝ) := by
        have hh := (div_lt_one (by linarith : (0 : ℝ) < p)).mpr hpp
        linarith
      positivity) hfactor
  rw [prod_mul_distrib, ← exp_sum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (by simpa using powered_eulerMass_le_pseries P hP (1 + t) (by linarith))
    (exp_pos _).le)


private lemma nonneg_of_derivative_nonneg (f g : ℝ → ℝ)
    (h0 : f 0 = 0) (hd : ∀ x, HasDerivAt f (g x) x)
    (hg : ∀ x, 0 ≤ x → 0 ≤ g x) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hg x (interior_subset hx))
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  simpa only [h0] using hh

private lemma exp_neg_remainder_one (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ -1 + x + exp (-x) := by
  linarith only [Real.add_one_le_exp (-x)]

private lemma exp_neg_remainder_2 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - x + x ^ 2 / 2 - exp (-x) := by
  apply nonneg_of_derivative_nonneg
    (fun x => 1 - x + x ^ 2 / 2 - exp (-x)) (fun x => -1 + x + exp (-x))
    (by norm_num) ?_ (fun x hx => exp_neg_remainder_one x hx) x hx
  intro x
  convert ((((hasDerivAt_const x (1 : ℝ))).sub ((hasDerivAt_id x))).add (((hasDerivAt_id x).pow 2).div_const 2)).sub ((hasDerivAt_neg x).exp) using 1 <;> simp [id] <;> ring

private lemma exp_neg_remainder_3 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ -1 + x - x ^ 2 / 2 + x ^ 3 / 6 + exp (-x) := by
  apply nonneg_of_derivative_nonneg
    (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 + exp (-x)) (fun x => 1 - x + x ^ 2 / 2 - exp (-x))
    (by norm_num) ?_ (fun x hx => exp_neg_remainder_2 x hx) x hx
  intro x
  convert (((((hasDerivAt_const x (-1 : ℝ))).add ((hasDerivAt_id x))).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 6)).add ((hasDerivAt_neg x).exp) using 1 <;> simp [id] <;> ring

private lemma exp_neg_remainder_4 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - exp (-x) := by
  apply nonneg_of_derivative_nonneg
    (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - exp (-x)) (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 + exp (-x))
    (by norm_num) ?_ (fun x hx => exp_neg_remainder_3 x hx) x hx
  intro x
  convert ((((((hasDerivAt_const x (1 : ℝ))).sub ((hasDerivAt_id x))).add (((hasDerivAt_id x).pow 2).div_const 2)).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub ((hasDerivAt_neg x).exp) using 1 <;> simp [id] <;> ring

private lemma exp_neg_remainder_5 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 + exp (-x) := by
  apply nonneg_of_derivative_nonneg
    (fun x => -1 + x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 + exp (-x)) (fun x => 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - exp (-x))
    (by norm_num) ?_ (fun x hx => exp_neg_remainder_4 x hx) x hx
  intro x
  convert (((((((hasDerivAt_const x (-1 : ℝ))).add ((hasDerivAt_id x))).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 6)).sub (((hasDerivAt_id x).pow 4).div_const 24)).add (((hasDerivAt_id x).pow 5).div_const 120)).add ((hasDerivAt_neg x).exp) using 1 <;> simp [id] <;> ring

lemma one_sub_exp_neg_le_fifth (x : ℝ) (hx : 0 ≤ x) :
    1 - exp (-x) ≤ x - x ^ 2 / 2 + x ^ 3 / 6 - x ^ 4 / 24 + x ^ 5 / 120 := by
  linarith only [exp_neg_remainder_5 x hx]


lemma scaled_prime_log_moment (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) (n : ℕ) :
    |(∑ p ∈ (R + 1).primesBelow, (2 * log (p : ℝ) / log (R : ℝ)) ^ (n + 1) / p) -
      (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)| ≤
      (2 : ℝ) ^ (n + 2) * WeightedMertens.sharpMomentError / log (R : ℝ) := by
  let L : ℝ := log (R : ℝ)
  have hL0 : L ≠ 0 := hL.ne'
  have hs (j : ℕ) :
      (∑ p ∈ (R + 1).primesBelow, (2 * log (p : ℝ) / L) ^ j / p) =
      (2 / L) ^ j * ∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ j / p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [show 2 * log (p : ℝ) / L = (2 / L) * log (p : ℝ) by ring, mul_pow]
    ring
  change |(∑ p ∈ (R + 1).primesBelow, (2 * log (p : ℝ) / L) ^ (n + 1) / p) -
      (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)| ≤
      (2 : ℝ) ^ (n + 2) * WeightedMertens.sharpMomentError / L
  rw [hs]
  rcases n with _ | n
  · have hh := mul_le_mul_of_nonneg_left (WeightedMertens.abs_primeSum_sub_log R hR)
      (show 0 ≤ 2 / L by positivity)
    have he : (2 / L) * WeightedMertens.primeSum R - 2 =
        (2 / L) * (WeightedMertens.primeSum R - L) := by field_simp <;> ring
    simp only [zero_add, Nat.cast_zero, pow_one, div_one]
    change |(2 / L) * WeightedMertens.primeSum R - 2| ≤ _
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / L)]
    apply hh.trans
    have hc : WeightedMertens.boundConstant ≤ 2 * WeightedMertens.sharpMomentError := by
      unfold WeightedMertens.sharpMomentError
      linarith [WeightedMertens.boundConstant_pos]
    have hh' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 / L by positivity)
    convert hh' using 1 <;> norm_num <;> ring
  · have hh := mul_le_mul_of_nonneg_left (WeightedMertens.prime_log_moment R hR n)
      (show 0 ≤ (2 / L) ^ (n + 2) by positivity)
    have he : (2 / L) ^ (n + 2) *
        ((∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ (n + 2) / p) -
          L ^ (n + 2) / ((n : ℝ) + 2)) =
        (2 / L) ^ (n + 2) * (∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ (n + 2) / p) -
          (2 : ℝ) ^ (n + 2) / ((n : ℝ) + 2) := by
      rw [mul_sub, div_pow]
      congr 1
      field_simp
    have he' : (2 / L) ^ (n + 2) * (2 * WeightedMertens.sharpMomentError * L ^ (n + 1)) =
        (2 : ℝ) ^ (n + 3) * WeightedMertens.sharpMomentError / L := by
      rw [div_pow]
      field_simp
      ring
    rw [← abs_of_nonneg (show 0 ≤ (2 / L) ^ (n + 2) by positivity), ← abs_mul] at hh
    rw [abs_of_nonneg (show 0 ≤ (2 / L) ^ (n + 2) by positivity)] at hh
    change |(2 / L) ^ (n + 2) * (_ - L ^ (n + 2) / ((n : ℝ) + 2))| ≤
      (2 / L) ^ (n + 2) * (2 * WeightedMertens.sharpMomentError * L ^ (n + 1)) at hh
    rw [he, he'] at hh
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, one_add_one_eq_two] using hh

lemma prime_exp_difference_sum_upper (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) :
    (∑ p ∈ (R + 1).primesBelow, (1 - exp (-(2 * log (p : ℝ) / log (R : ℝ)))) / p) ≤
      599 / 450 + 13 * WeightedMertens.sharpMomentError / log (R : ℝ) := by
  let L : ℝ := log (R : ℝ)
  let M (j : ℕ) : ℝ := ∑ p ∈ (R + 1).primesBelow, (2 * log (p : ℝ) / L) ^ j / p
  have hm (n : ℕ) : |M (n + 1) - (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)| ≤
      (2 : ℝ) ^ (n + 2) * WeightedMertens.sharpMomentError / L :=
    scaled_prime_log_moment R hR hL n
  have h1 := (abs_le.mp (hm 0)).2
  have h2 := (abs_le.mp (hm 1)).1
  have h3 := (abs_le.mp (hm 2)).2
  have h4 := (abs_le.mp (hm 3)).1
  have h5 := (abs_le.mp (hm 4)).2
  norm_num only [Nat.cast_ofNat, zero_add, zero_pow, pow_succ] at h1 h2 h3 h4 h5
  have hsum : (∑ p ∈ (R + 1).primesBelow,
      (1 - exp (-(2 * log (p : ℝ) / L))) / p) ≤
      M 1 - M 2 / 2 + M 3 / 6 - M 4 / 24 + M 5 / 120 := by
    calc
      _ ≤ ∑ p ∈ (R + 1).primesBelow,
          ((2 * log (p : ℝ) / L) - (2 * log (p : ℝ) / L) ^ 2 / 2 +
            (2 * log (p : ℝ) / L) ^ 3 / 6 - (2 * log (p : ℝ) / L) ^ 4 / 24 +
              (2 * log (p : ℝ) / L) ^ 5 / 120) / p := by
        apply sum_le_sum
        intro p hp
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
        exact one_sub_exp_neg_le_fifth _
          (div_nonneg (mul_nonneg (by norm_num) (log_natCast_nonneg p)) hL.le)
      _ = _ := by
        have he (p : ℕ) :
            ((2 * log (p : ℝ) / L) - (2 * log (p : ℝ) / L) ^ 2 / 2 +
              (2 * log (p : ℝ) / L) ^ 3 / 6 - (2 * log (p : ℝ) / L) ^ 4 / 24 +
                (2 * log (p : ℝ) / L) ^ 5 / 120) / p =
            (2 * log (p : ℝ) / L) ^ 1 / p - ((2 * log (p : ℝ) / L) ^ 2 / p) / 2 +
              ((2 * log (p : ℝ) / L) ^ 3 / p) / 6 - ((2 * log (p : ℝ) / L) ^ 4 / p) / 24 +
                ((2 * log (p : ℝ) / L) ^ 5 / p) / 120 := by ring
        simp only [he, sum_add_distrib, sum_sub_distrib, ← sum_div]
        rfl
  have hE : 0 ≤ WeightedMertens.sharpMomentError / L :=
    div_nonneg WeightedMertens.sharpMomentError_pos.le hL.le
  change (∑ p ∈ (R + 1).primesBelow, (1 - exp (-(2 * log (p : ℝ) / L))) / p) ≤
    599 / 450 + 13 * WeightedMertens.sharpMomentError / L
  simp only [mul_div_assoc] at h1 h2 h3 h4 h5 hsum ⊢
  linarith


lemma prime_exp_pred_difference_sum_upper (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) :
    (∑ p ∈ (R + 1).primesBelow,
      (1 - exp (-(2 / log (R : ℝ)) * log (p : ℝ))) / ((p : ℝ) - 1)) ≤
      599 / 450 + 15 * WeightedMertens.sharpMomentError / log (R : ℝ) := by
  let L : ℝ := log (R : ℝ)
  have hpt (p : ℕ) (hp : p ∈ (R + 1).primesBelow) :
      (1 - exp (-(2 / L) * log (p : ℝ))) / ((p : ℝ) - 1) ≤
      (1 - exp (-(2 * log (p : ℝ) / L))) / p +
        (2 / L) * (log (p : ℝ) / ((p : ℝ) * (p - 1))) := by
    have hpp : (1 : ℝ) < p := by exact_mod_cast (WeightedMertens.mem_primes.mp hp).1.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hpd : 0 < (p : ℝ) - 1 := by linarith
    have he : -(2 / L) * log (p : ℝ) = -(2 * log (p : ℝ) / L) := by ring
    rw [he]
    have hb : 1 - exp (-(2 * log (p : ℝ) / L)) ≤ 2 * log (p : ℝ) / L := by
      linarith only [Real.add_one_le_exp (-(2 * log (p : ℝ) / L))]
    have hh := div_le_div_of_nonneg_right hb (show 0 ≤ (p : ℝ) * (p - 1) by positivity)
    have hid : (1 - exp (-(2 * log (p : ℝ) / L))) / ((p : ℝ) - 1) =
        (1 - exp (-(2 * log (p : ℝ) / L))) / p +
        (1 - exp (-(2 * log (p : ℝ) / L))) / ((p : ℝ) * (p - 1)) := by
      field_simp
      ring
    rw [hid]
    convert add_le_add_left hh ((1 - exp (-(2 * log (p : ℝ) / L))) / p) using 1 <;> ring
  have hh := sum_le_sum hpt
  rw [sum_add_distrib, ← mul_sum] at hh
  change (∑ p ∈ (R + 1).primesBelow,
      (1 - exp (-(2 / L) * log (p : ℝ))) / ((p : ℝ) - 1)) ≤
      (∑ p ∈ (R + 1).primesBelow, (1 - exp (-(2 * log (p : ℝ) / L))) / p) +
        (2 / L) * WeightedMertens.errorSum R at hh
  have he := mul_le_mul_of_nonneg_left (WeightedMertens.errorSum_le R)
    (show 0 ≤ 2 / L by positivity)
  have hc : WeightedMertens.errorConstant ≤ WeightedMertens.sharpMomentError := by
    unfold WeightedMertens.sharpMomentError WeightedMertens.boundConstant
    have h4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
    linarith
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 / L by positivity)
  have hmain := prime_exp_difference_sum_upper R hR hL
  change (∑ p ∈ (R + 1).primesBelow,
      (1 - exp (-(2 / L) * log (p : ℝ))) / ((p : ℝ) - 1)) ≤
      599 / 450 + 15 * WeightedMertens.sharpMomentError / L
  dsimp only [L] at hh he hc' ⊢
  linear_combination hh + he + hc' + hmain

/-- An explicit Euler-product bound obtained by comparison with a p-series.
The error in the exponent tends to zero; no PNT or sharp Mertens-product
asymptotic is used. -/
theorem eulerMass_initial_upper_explicit (R : ℕ) (hR : 0 < R) (hL : 0 < log (R : ℝ)) :
    eulerMass (R + 1).primesBelow ≤ (1 + log (R : ℝ) / 2) *
      exp (599 / 450 + 15 * WeightedMertens.sharpMomentError / log (R : ℝ)) := by
  have h := eulerMass_power_comparison (R + 1).primesBelow
    (fun p hp => (WeightedMertens.mem_primes.mp hp).1) (2 / log (R : ℝ)) (by positivity)
  have hi : 1 / (2 / log (R : ℝ)) = log (R : ℝ) / 2 := by field_simp
  rw [hi] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (prime_exp_pred_difference_sum_upper R hR hL)) (by positivity))

/-- Eventual coefficient 1.9, with no hidden error depending on the prime set. -/
theorem eventually_eulerMass_initial_le_nineteen_tenths_log :
    ∀ᶠ R : ℕ in atTop, eulerMass (R + 1).primesBelow ≤ (19 / 10 : ℝ) * log (R : ℝ) := by
  have hlog : Tendsto (fun R : ℕ => log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun R : ℕ => (log (R : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hlim : Tendsto (fun R : ℕ =>
      ((log (R : ℝ))⁻¹ + 1 / 2) *
        exp (599 / 450 + 15 * WeightedMertens.sharpMomentError * (log (R : ℝ))⁻¹))
      atTop (𝓝 ((1 / 2 : ℝ) * exp (599 / 450))) := by
    convert (hinv.add_const (1 / 2)).mul
      (Real.continuous_exp.tendsto _ |>.comp
        (tendsto_const_nhds.add (hinv.const_mul (15 * WeightedMertens.sharpMomentError)))) using 1
    norm_num
  have hrate : (1 / 2 : ℝ) * exp (599 / 450) < 19 / 10 := by
    have he : exp (599 / 450 : ℝ) < 19 / 5 := by
      rw [← exp_log (by norm_num : (0 : ℝ) < 19 / 5)]
      apply exp_lt_exp.mpr
      have hl : log (19 / 5 : ℝ) = 2 * log 2 + log (19 / 20 : ℝ) := by
        rw [show (19 / 5 : ℝ) = 2 ^ (2 : ℕ) * (19 / 20 : ℝ) by norm_num,
          log_mul (by norm_num : (2 : ℝ) ^ (2 : ℕ) ≠ 0) (by norm_num), log_pow]
        norm_num
      rw [hl]
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19 / 20)
      norm_num at hh
      linarith only [Real.log_two_gt_d9, hh]
    linarith
  have hb := hlim.eventually_lt_const hrate
  filter_upwards [hb, eventually_ge_atTop 2] with R hR hR2
  have hL : 0 < log (R : ℝ) := log_pos (by exact_mod_cast (show 1 < R by omega))
  have hupper := eulerMass_initial_upper_explicit R (by omega) hL
  have he : ((log (R : ℝ))⁻¹ + 1 / 2) *
      exp (599 / 450 + 15 * WeightedMertens.sharpMomentError * (log (R : ℝ))⁻¹) * log (R : ℝ) =
      (1 + log (R : ℝ) / 2) *
        exp (599 / 450 + 15 * WeightedMertens.sharpMomentError / log (R : ℝ)) := by
    rw [div_eq_mul_inv (15 * WeightedMertens.sharpMomentError)]
    field_simp
  have hh := mul_lt_mul_of_pos_right hR hL
  rw [he] at hh
  exact hupper.trans hh.le

/-- A weaker round coefficient, convenient in subsequent estimates. -/
theorem eventually_eulerMass_initial_le_two_log :
    ∀ᶠ R : ℕ in atTop, eulerMass (R + 1).primesBelow ≤ 2 * log (R : ℝ) := by
  filter_upwards [eventually_eulerMass_initial_le_nineteen_tenths_log] with R hR
  exact hR.trans (mul_le_mul_of_nonneg_right (by norm_num : (19 / 10 : ℝ) ≤ 2)
    (log_natCast_nonneg R))

#print axioms eulerMass_power_comparison
#print axioms one_sub_exp_neg_le_fifth
#print axioms eulerMass_initial_upper_explicit
#print axioms eventually_eulerMass_initial_le_nineteen_tenths_log
#print axioms eventually_eulerMass_initial_le_two_log
end Erdos970.FiniteSelberg
