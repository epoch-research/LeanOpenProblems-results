import Submission.BuchstabProfileInterval

/-! A global coefficient-one quadrature bound for exponentially dominated
monotone profiles. All primes, including the smallest, are included. The
arithmetic remainder is O(1/L), with no terminal-cutoff or mesh dependence.
This is still a profile-measure theorem, not a recursive-error estimate. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg ContinuousBuchstab MeasureTheory Set
set_option maxHeartbeats 2000000

lemma quadratic_half_geometric_sum (N : ℕ) :
    (∑ j ∈ range N, ((j : ℝ)+2)^2*(1/2 : ℝ)^j) =
      22-(2*(N : ℝ)^2+12*N+22)*(1/2 : ℝ)^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [sum_range_succ,ih,pow_succ]
      push_cast
      ring

lemma quadratic_exp_sum_le (N : ℕ) :
    (∑ j ∈ range N, ((j : ℝ)+2)^2*exp (-(j : ℝ))) ≤ 22 := by
  have he1 : exp (-1) ≤ (1/2 : ℝ) := by
    have he : (2 : ℝ) ≤ exp 1 := by linarith only [add_one_le_exp (1 : ℝ)]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he
    simpa only [one_div,exp_neg] using hh
  have hj (j : ℕ) : exp (-(j : ℝ)) ≤ (1/2 : ℝ)^j := by
    have hh := pow_le_pow_left₀ (exp_pos (-1)).le he1 j
    rw [← exp_nat_mul] at hh
    simpa only [mul_neg_one] using hh
  have hs := sum_le_sum (s := range N) (fun j _ => mul_le_mul_of_nonneg_left (hj j) (sq_nonneg ((j : ℝ)+2)))
  rw [quadratic_half_geometric_sum] at hs
  have hn : 0 ≤ (2*(N : ℝ)^2+12*N+22)*(1/2 : ℝ)^N := by positivity
  linarith only [hs,hn]

lemma unit_profile_remainder_le (B H s L : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hs : 1 ≤ s) (hL : 0 < L) (j : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hxH : x ≤ H*exp (-(s-1+j))) :
    (2*B/((s/(s+j+1))*L))*(1+1/(s/(s+j+1)))*x ≤
      (4*B*H*exp (1-s)/L)*(((j : ℝ)+2)^2*exp (-(j : ℝ))) := by
  have hs0 : 0 < s := by linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hden : 0 < s+j+1 := by linarith
  let r : ℝ := (s+j+1)/s
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr : r ≤ (j : ℝ)+2 := by
    apply (div_le_iff₀ hs0).mpr
    have hh := mul_nonneg (show 0 ≤ s-1 by linarith) (show (0 : ℝ) ≤ j+1 by positivity)
    nlinarith only [hh]
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hj2 : (j : ℝ)+2 ≤ ((j : ℝ)+2)^2 := by nlinarith only [hj]
  have hshape : r*(1+r) ≤ 2*((j : ℝ)+2)^2 := by nlinarith only [hr,hr2,hj2]
  have hid : (2*B/((s/(s+j+1))*L))*(1+1/(s/(s+j+1)))*x =
      (2*B/L)*(r*(1+r))*x := by
    dsimp [r]
    field_simp [hs0.ne',hden.ne',hL.ne']
    <;> ring
  rw [hid]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hshape (by positivity : 0 ≤ 2*B/L)) hx
  have hx' := mul_le_mul_of_nonneg_left hxH
    (show 0 ≤ (2*B/L)*(2*((j : ℝ)+2)^2) by positivity)
  have hexp : exp (-(s-1+j))=exp (1-s)*exp (-(j : ℝ)) := by
    rw [← exp_add]
    congr 1
    ring
  apply hh.trans
  apply hx'.trans_eq
  rw [hexp]
  ring

/-- Global arithmetic profile transfer with coefficient one in front of the
continuous tail. The bound applies simultaneously to all positive L and all
s≥1. Its constant depends only on the additive Euler remainder and the
exponential envelope, not on a mesh, cutoff, prime prefix, or profile depth. -/
theorem prime_profile_global_upper (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (s L H : ℝ) (hs : 1 ≤ s) (hL : 0 < L) (hH : 0 ≤ H)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici (s-1)))
    (hf0 : ∀ x, s-1 ≤ x → 0 ≤ f x) (hfi : IntegrableOn f (Ioi (s-1)))
    (hfexp : ∀ x, s-1 ≤ x → f x ≤ H*exp (-x)) :
    initialEulerMass (expFloor 1 L)*
      (∑ p ∈ (expFloor 1 L+1).primesBelow,
        ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*L/log (p : ℝ)-1)) ≤
      tailIntegral f (s-1)/s+88*(A+C+1)*H*exp (1-s)/L := by
  have hs0 : 0 < s := by linarith
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  obtain ⟨J,hJ⟩ := exists_nat_gt (s*L/log 2)
  let v : ℕ → ℝ := fun j => s-1+j
  let F : ℕ → ℝ := fun p =>
    ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*L/log (p : ℝ)-1)
  let K : ℝ := 4*(A+C+1)*H*exp (1-s)/L
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hv : Monotone v := by
    intro i j hij
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp only [v]
    linarith only [hijR]
  have hv0 : v 0=s-1 := by simp [v]
  have hvlo (j : ℕ) : s-1 ≤ v j := by dsimp [v]; exact le_add_of_nonneg_right (Nat.cast_nonneg j)
  have hvstep (j : ℕ) : v j < v (j+1) := by dsimp [v]; push_cast; linarith
  have hvnonneg (j : ℕ) : 0 ≤ v j := by linarith only [hvlo j,hs]
  have hend : profileCut (s*L) (v J)=1 := by
    unfold profileCut
    apply (Nat.floor_eq_iff (exp_pos _).le).mpr
    have hden : 0 < v J+1 := by linarith only [hvnonneg J]
    have hlt : s*L/(v J+1) < log 2 := by
      apply (div_lt_iff₀ hden).mpr
      have hh := (div_lt_iff₀ hlog2).mp hJ
      dsimp only [v]
      have hp := mul_pos hs0 hlog2
      nlinarith only [hh,hp]
    constructor
    · simpa only [Nat.cast_one] using one_le_exp (div_nonneg (mul_pos hs0 hL).le hden.le)
    · simpa only [Nat.cast_one,show (1 : ℝ)+1=2 by norm_num,exp_log (by norm_num : (0 : ℝ) < 2)] using
        exp_lt_exp.mpr hlt
  have hstart : profileCut (s*L) (v 0)=expFloor 1 L := by
    rw [hv0,profileCut_scaled,sub_add_cancel,div_self hs0.ne']
  have hset : (Finset.Ioc 1 (expFloor 1 L)).filter Nat.Prime=(expFloor 1 L+1).primesBelow := by
    ext p
    simp only [mem_filter,Finset.mem_Ioc,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp1,hpR⟩,hpp⟩
      exact ⟨by omega,hpp⟩
    · rintro ⟨hpR,hpp⟩
      exact ⟨⟨hpp.one_lt,by omega⟩,hpp⟩
  have hpart := profileBins_sum (s*L) (mul_pos hs0 hL).le v hv (hvnonneg 0) J F
  rw [hend,hstart,hset] at hpart
  have hband (j : ℕ) : initialEulerMass (expFloor 1 L)*
      (∑ p ∈ profileBin (s*L) (v j) (v (j+1)), F p) ≤
        (∫ x in v j..v (j+1), f x)/s+K*(((j : ℝ)+2)^2*exp (-(j : ℝ))) := by
    have hf' : AntitoneOn f (Ici (v j)) := hf.mono (Ici_subset_Ici.mpr (hvlo j))
    have hf0' : ∀ x, v j ≤ x → 0 ≤ f x := fun x hx => hf0 x ((hvlo j).trans hx)
    have hh := prime_profile_interval_upper C A hC hA hrem s (v j) (v (j+1)) L hs0
      (hvnonneg j) (hvstep j) hL f hf' hf0'
    have hcost := unit_profile_remainder_le (A+C+1) H s L (by positivity) hH hs hL j
      (f (v j)) (hf0 _ (hvlo j)) (hfexp _ (hvlo j))
    have hcost' : (2*(A+C+1)/((s/(v (j+1)+1))*L))*(1+1/(s/(v (j+1)+1)))*f (v j) ≤
        K*(((j : ℝ)+2)^2*exp (-(j : ℝ))) := by
      convert hcost using 1 <;> dsimp [v,K] <;> push_cast <;> ring
    have hh' : initialEulerMass (expFloor 1 L)*
        (∑ p ∈ profileBin (s*L) (v j) (v (j+1)), F p) ≤
        (∫ x in v j..v (j+1), f x)/s+
          (2*(A+C+1)/((s/(v (j+1)+1))*L))*(1+1/(s/(v (j+1)+1)))*f (v j) := by
      simpa only [profileBin,profileCut_scaled,F] using hh
    exact hh'.trans (add_le_add le_rfl hcost')
  have hint (j : ℕ) : IntervalIntegrable f volume (v j) (v (j+1)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hvstep j).le).mpr
    exact hfi.mono_set (fun x hx => lt_of_le_of_lt (hvlo j) hx.1)
  have hmain : (∑ j ∈ range J, (∫ x in v j..v (j+1), f x)/s) ≤ tailIntegral f (s-1)/s := by
    rw [← sum_div,intervalIntegral.sum_integral_adjacent_intervals (fun j _ => hint j),hv0]
    apply div_le_div_of_nonneg_right _ hs0.le
    rw [intervalIntegral.integral_of_le (hvlo J)]
    apply setIntegral_mono_set hfi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hf0 x hx.le
    · exact Filter.Eventually.of_forall (fun x hx => hx.1)
  have hsum := sum_le_sum (s := range J) (fun j _ => hband j)
  rw [← mul_sum,hpart,sum_add_distrib,← mul_sum] at hsum
  have herr := mul_le_mul_of_nonneg_left (quadratic_exp_sum_le J) hK
  change initialEulerMass (expFloor 1 L)*
      (∑ p ∈ (expFloor 1 L+1).primesBelow, F p) ≤ _
  have hh := hsum.trans (add_le_add hmain herr)
  convert hh using 1 <;> dsimp [K] <;> ring

#print axioms quadratic_exp_sum_le
#print axioms prime_profile_global_upper
end Erdos970.RecursiveSieve.Buchstab
