import Submission.WeakSoftEndpointReduction
import Submission.QuadraticCountMomentObstruction

/-! A bounded stochastic shift in the endpoint-conditioned count would imply
an impermissibly strong two-sided concentration statement. This file concerns
an auxiliary coupling proposal, NOT the negation of Erdős 970. -/
namespace Erdos970.GapAverages.EndpointShift
open Finset Real Filter
open scoped Topology
set_option maxHeartbeats 1800000

/-- The signed exponential consequence of a stochastic comparison with shift B.
The sign retains both the lower- and upper-tail comparisons. -/
def UniformSignedShift (B : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, ∀ s : ℝ,
    (exp s-1) * (endpointLaplace P (-s) m -
      density P * exp (B*s) * countLaplace P (-s) m) ≤ 0

lemma exp_upper_quadratic (x : ℝ) (hx : |x| ≤ 1) :
    exp x ≤ 1+x+x^2 := by
  have hh := (abs_le.mp (Real.exp_bound hx (n := 2) (by norm_num))).2
  norm_num [sum_range_succ, sq_abs] at hh
  nlinarith [sq_nonneg x]

lemma laplace_of_signed_shift (B : ℝ) (h : UniformSignedShift B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (m : ℕ) :
    countLaplace P (-s) m ≤ exp ((m : ℝ)*density P*
      (exp ((B+1)*s)-exp (B*s))) := by
  let a := density P*(exp ((B+1)*s)-exp (B*s))
  have hid : (exp s-1)*(density P*exp (B*s)) = a := by
    dsimp only [a]
    rw [show (B+1)*s = s+B*s by ring, exp_add]
    ring
  induction m with
  | zero => simp [countLaplace_zero P hP]
  | succ m ih =>
    have hs := h P hP m s
    have hstep : countLaplace P (-s) (m+1) ≤ (1+a)*countLaplace P (-s) m := by
      rw [countLaplace_succ, neg_neg]
      have he : (exp s-1) * (endpointLaplace P (-s) m -
          density P * exp (B*s) * countLaplace P (-s) m) =
          (exp s-1)*endpointLaplace P (-s) m-a*countLaplace P (-s) m := by
        rw [mul_sub, ← mul_assoc, hid]
      rw [he] at hs
      nlinarith only [hs]
    calc
      countLaplace P (-s) (m+1) ≤ (1+a)*countLaplace P (-s) m := hstep
      _ ≤ exp a*countLaplace P (-s) m := mul_le_mul_of_nonneg_right
        (by linarith only [add_one_le_exp a]) (countLaplace_nonneg P (-s) m)
      _ ≤ exp a*exp ((m : ℝ)*density P*(exp ((B+1)*s)-exp (B*s))) :=
        mul_le_mul_of_nonneg_left ih (exp_pos _).le
      _ = exp (((m+1 : ℕ) : ℝ)*density P*(exp ((B+1)*s)-exp (B*s))) := by
        rw [← exp_add]
        congr 1
        dsimp only [a]
        push_cast
        ring

/-- A bounded shift forces a two-sided Gaussian local exponential estimate. -/
lemma centered_mgf_of_signed_shift (B : ℝ) (h : UniformSignedShift B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℝ)
    (hs : |(B+1)*s| ≤ 1) (m : ℕ) :
    phaseMean P (fun r => exp (s*(intervalCount P m r-(m : ℝ)*density P))) ≤
      exp ((B+1)^2*(m : ℝ)*s^2) := by
  have he (r : Phase P) : exp (s*(intervalCount P m r-(m : ℝ)*density P)) =
      exp (-s*((m : ℝ)*density P))*exp (-(-s)*intervalCount P m r) := by
    rw [← exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [phaseMean_mul]
  change exp (-s*((m : ℝ)*density P))*countLaplace P (-s) m ≤ _
  have hg : exp ((B+1)*s)-exp (B*s)-s ≤ ((B+1)*s)^2 := by
    have hu := exp_upper_quadratic ((B+1)*s) hs
    have hl := add_one_le_exp (B*s)
    nlinarith only [hu,hl]
  have hδ := density_le_one P hP
  have hδ0 := (density_pos P hP).le
  have hprod := mul_le_mul_of_nonneg_left hg (mul_nonneg (Nat.cast_nonneg m) hδ0)
  have hscale := mul_le_mul_of_nonneg_left hδ
    (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg ((B+1)*s)))
  calc
    _ ≤ exp (-s*((m : ℝ)*density P))*
        exp ((m : ℝ)*density P*(exp ((B+1)*s)-exp (B*s))) :=
      mul_le_mul_of_nonneg_left (laplace_of_signed_shift B h P hP s m) (exp_pos _).le
    _ ≤ exp ((B+1)^2*(m : ℝ)*s^2) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith only [hprod,hscale]

lemma count_discrepancy_of_signed_shift (B : ℝ) (h : UniformSignedShift B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (s H : ℝ)
    (hs : 0 < s) (hsmall : |(B+1)*s| ≤ 1)
    (hprod : (∏ p ∈ P, (p : ℝ)) ≤ exp H) (r : Phase P) :
    |intervalCount P m r-(m : ℝ)*density P| ≤ (H+(B+1)^2*m*s^2)/s := by
  have hbound (u : ℝ) (hu : |(B+1)*u| ≤ 1) :
      u*(intervalCount P m r-(m : ℝ)*density P) ≤ H+(B+1)^2*m*u^2 := by
    have hv := value_le_phaseMean_mul_product P hP
      (fun r => exp (u*(intervalCount P m r-(m : ℝ)*density P)))
      (fun _ => (exp_pos _).le) r
    have hh := mul_le_mul hprod (centered_mgf_of_signed_shift B h P hP u hu m)
      (by unfold phaseMean; positivity) (exp_pos H).le
    have hx := hv.trans hh
    rw [← exp_add] at hx
    exact exp_le_exp.mp hx
  have hp := hbound s hsmall
  have hn := hbound (-s) (by simpa only [mul_neg, abs_neg] using hsmall)
  apply (le_div_iff₀ hs).mpr
  have habs : |s*(intervalCount P m r-(m : ℝ)*density P)| ≤
      H+(B+1)^2*m*s^2 := abs_le.mpr ⟨by nlinarith only [hn], hp⟩
  simpa only [abs_mul, abs_of_pos hs, mul_comm] using habs

lemma short_counts_of_shift (B : ℝ) (h : UniformSignedShift B)
    (t : ℕ) (ht : 1 ≤ t) (hB : |B+1| ≤ (t : ℝ)^3)
    (m : ℕ) (hm : m ≤ 4096*t^12) :
    |roughCount (64*t^6).primesBelow m-
      (m : ℝ)*density (64*t^6).primesBelow| ≤
      (64*log 4+4096*(B+1)^2)*(t : ℝ)^11 := by
  let P := (64*t^6).primesBelow
  have hP : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hsmall : |(B+1)*(1/(t : ℝ)^3)| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1/(t : ℝ)^3)]
    exact (mul_le_mul_of_nonneg_right hB (by positivity)).trans_eq (by field_simp)
  have hprod : (∏ p ∈ P, (p : ℝ)) ≤ exp ((64*log 4)*(t : ℝ)^6) := by
    have hh := primesBelow_product_le_four (64*t^6)
    have he : (4 : ℝ)^(64*t^6) = exp ((64*log 4)*(t : ℝ)^6) := by
      rw [show (64*log (4 : ℝ))*(t : ℝ)^6 = (64*t^6 : ℕ)*log 4 by push_cast; ring,
        exp_nat_mul, exp_log (by norm_num)]
    exact hh.trans_eq he
  have hh := count_discrepancy_of_signed_shift B h P hP m
    (1/(t : ℝ)^3) ((64*log 4)*(t : ℝ)^6) (by positivity) hsmall hprod (zeroPhase P hP)
  rw [intervalCount_zeroPhase] at hh
  have hmR : (m : ℝ) ≤ 4096*(t : ℝ)^12 := by exact_mod_cast hm
  have hb : ((64*log 4)*(t : ℝ)^6+(B+1)^2*m*(1/(t : ℝ)^3)^2)/(1/(t : ℝ)^3) ≤
      (64*log 4+4096*(B+1)^2)*(t : ℝ)^9 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1/(t : ℝ)^3)).mpr
    have hc := mul_le_mul_of_nonneg_left hmR
      (show 0 ≤ (B+1)^2*(1/(t : ℝ)^3)^2 by positivity)
    field_simp at hc ⊢
    nlinarith only [hc]
  have hA : 0 ≤ 64*log (4 : ℝ)+4096*(B+1)^2 := by positivity
  exact (hh.trans hb).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by exact_mod_cast ht) (show 9 ≤ 11 by omega)) hA)

lemma prime_recurrence_of_signed_shift (B : ℝ) (h : UniformSignedShift B)
    (t : ℕ) (ht : 2 ≤ t) (hB : |B+1| ≤ (t : ℝ)^3) :
    4096*((t^12).primeCounting' : ℝ)-(4096*t^12).primeCounting' ≤
      (4097*(64*log 4+4096*(B+1)^2)+262080)*(t : ℝ)^11 := by
  have ht0 : 0 < t := by omega
  have ht1 : 1 ≤ t := by omega
  let y := 64*t^6
  let P := y.primesBelow
  let A := 64*log (4 : ℝ)+4096*(B+1)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcount (m : ℕ) (hml : t^12 ≤ m) (hmh : m ≤ 4096*t^12) :
      |roughCount P m-(m : ℝ)*density P| ≤ A*(t : ℝ)^11 := by
    exact short_counts_of_shift B h t ht1 hB m hmh
  have hshort := hcount (t^12) le_rfl (by omega)
  have hlong := hcount (4096*t^12) (by omega) le_rfl
  have hy3 : 2 < y := by
    have hh := Nat.one_le_pow 6 t ht0
    dsimp [y]
    omega
  have hyn : y ≤ t^12 := by
    have hh := Nat.pow_le_pow_left ht 6
    norm_num at hh
    have hid : t^12 = (t^6)^2 := by ring
    rw [hid]
    dsimp [y]
    nlinarith
  have hsq : y^2 = 4096*t^12 := by dsimp [y]; ring
  have he1 := roughCount_primesBelow_eq y (t^12) hy3 hyn (by rw [hsq]; omega)
  have he2 := roughCount_primesBelow_eq y (4096*t^12) hy3 (by omega) (by rw [hsq])
  change roughCount P _ = _ at he1 he2
  rw [he1] at hshort
  rw [he2] at hlong
  have hpi : (y.primeCounting' : ℝ) ≤ 64*(t : ℝ)^11 := by
    have hh : y.primeCounting' ≤ y := Nat.count_le _
    have hp := Nat.pow_le_pow_right ht0 (show 6 ≤ 11 by omega)
    exact_mod_cast hh.trans (Nat.mul_le_mul_left 64 hp)
  have hu := (abs_le.mp hshort).2
  have hl := (abs_le.mp hlong).1
  push_cast at hu hl
  change 4096*((t^12).primeCounting' : ℝ)-(4096*t^12).primeCounting' ≤
    (4097*A+262080)*(t : ℝ)^11
  nlinarith only [hu,hl,hpi]

/-- No fixed signed exponential shift is valid uniformly in the prime set
and interval length. The proof uses elementary prime counting, not numerics. -/
theorem not_uniformSignedShift (B : ℝ) : ¬UniformSignedShift B := by
  intro h
  apply PrimeCountingDyadic.not_eventually_bounded_4096_difference
    (4097*(64*log 4+4096*(B+1)^2)+262080)
  have htop : Tendsto (fun j : ℕ => ((2^j : ℕ) : ℝ)^3) atTop atTop :=
    (tendsto_pow_atTop (by omega : 3 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by omega : (1 : ℕ) < 2)))
  filter_upwards [htop.eventually_ge_atTop |B+1|, eventually_ge_atTop 1] with j hj hj1
  have ht : 2 ≤ 2^j := by
    have hh := Nat.pow_le_pow_right (show 0 < 2 by omega) hj1
    norm_num at hh
    exact hh
  have hh := prime_recurrence_of_signed_shift B h (2^j) ht hj
  have hn : (2^j : ℕ)^12 = 4096^j := by
    rw [← pow_mul, Nat.mul_comm j 12, pow_mul]
    norm_num
  have hm : 4096*(2^j : ℕ)^12 = 4096^(j+1) := by rw [hn,pow_succ]; ring
  have he : (((2^j : ℕ) : ℝ))^11 = 2048^j := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm j 11, pow_mul]
    norm_num
  rw [hm,hn,he] at hh
  exact hh

/-- Usual stochastic domination of the endpoint-conditioned interval count
by the unconditioned interval count plus B, expressed without division. -/
def UniformStochasticShift (B : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ,
    ∀ f : ℝ → ℝ, Monotone f →
      phaseMean P (fun r => point P m r*f (intervalCount P m r)) ≤
        density P*phaseMean P (fun r => f (intervalCount P m r+B))

lemma signed_shift_of_stochastic (B : ℝ) (h : UniformStochasticShift B) :
    UniformSignedShift B := by
  intro P hP m s
  have hf : Monotone (fun n : ℝ => (exp s-1)*exp (s*n)) := by
    intro x y hxy
    by_cases hs : 0 ≤ s
    · have hc : 0 ≤ exp s-1 := by
        have hh := exp_le_exp.mpr hs
        simpa only [exp_zero] using sub_nonneg.mpr hh
      exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hxy hs)) hc
    · have hs' : s ≤ 0 := le_of_not_ge hs
      have hc : exp s-1 ≤ 0 := by
        have hh := exp_le_exp.mpr hs'
        simpa only [exp_zero] using sub_nonpos.mpr hh
      exact mul_le_mul_of_nonpos_left (exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hxy hs')) hc
  have hh := h P hP m (fun n => (exp s-1)*exp (s*n)) hf
  have hleft : phaseMean P (fun r => point P m r*((exp s-1)*exp (s*intervalCount P m r))) =
      (exp s-1)*endpointLaplace P (-s) m := by
    rw [endpointLaplace, ← phaseMean_mul]
    congr 1
    funext r
    simp only [neg_neg]
    ring
  have hright : phaseMean P (fun r => (exp s-1)*exp (s*(intervalCount P m r+B))) =
      ((exp s-1)*exp (B*s))*countLaplace P (-s) m := by
    rw [countLaplace, ← phaseMean_mul]
    congr 1
    funext r
    rw [mul_add, exp_add]
    simp only [neg_neg]
    rw [mul_comm B s]
    ring
  rw [hleft,hright] at hh
  nlinarith only [hh]

/-- In particular, replacing the failed exact domination by a shift of one,
or by any other absolute constant, does not repair the uniform proposal.
This is NOT a disproof of the quadratic Jacobsthal conjecture. -/
theorem not_uniformStochasticShift (B : ℝ) : ¬UniformStochasticShift B := by
  intro h
  exact not_uniformSignedShift B (signed_shift_of_stochastic B h)

#print axioms centered_mgf_of_signed_shift
#print axioms short_counts_of_shift
#print axioms not_uniformSignedShift
#print axioms not_uniformStochasticShift
end Erdos970.GapAverages.EndpointShift
