import Submission.PrimeAllLogMoments

/-! A quantitative finite-prime transfer for differentiable logarithmic
profiles. The leading integral has coefficient one; the error is controlled
by total variation. No Jacobsthal endpoint is asserted. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory Set
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι]

/-- Quantitative Stieltjes transfer, including the endpoint atom. -/
theorem cumulative_differentiable_profile_error (w a : ι → ℝ) (L E : ℝ)
    (hL : 0 ≤ L) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ L)
    (htotal : |(∑ i, w i)-L| ≤ E)
    (hF : ∀ t ∈ Icc 0 L, |cumulativeMass w a t-t| ≤ E)
    (f g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 L)
    (hder : ∀ x ∈ Icc 0 L, HasDerivAt f (g x) x) :
    |(∑ i, w i*f (a i))-(∫ t in 0..L, f t)| ≤
      E*(|f L|+(∫ t in 0..L, |g t|)) := by
  have hf (x : ℝ) (hx : 0 ≤ x) :
      (if x ≤ L then f L-f x else 0) =
        if x ≤ L then (∫ t in x..L, g t) else 0 := by
    by_cases hxl : x ≤ L
    · rw [if_pos hxl,if_pos hxl]
      have hs : uIcc x L ⊆ uIcc 0 L := by
        rw [uIcc_of_le hxl,uIcc_of_le hL]
        exact Icc_subset_Icc hx le_rfl
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hg.mono_set hs)
      intro t ht
      apply hder
      have hh := hs ht
      rwa [uIcc_of_le hL] at hh
    · simp only [if_neg hxl]
  have hid := weighted_profile_integral w a (fun i => (ha i).1) L hL g
    (fun x => if x ≤ L then f L-f x else 0) hg hf
  simp_rw [if_pos (ha _).2,mul_sub] at hid
  rw [sum_sub_distrib] at hid
  have hs : (∑ i, w i*f L)=f L*(∑ i,w i) := by rw [← sum_mul,mul_comm]
  rw [hs] at hid
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ => 1) (v := f) (v' := g)
    (a := 0) (b := L) (fun t _ => hasDerivAt_id t)
    (fun t ht => hder t (by rwa [uIcc_of_le hL] at ht))
    (continuous_const.intervalIntegrable _ _) hg
  simp only [zero_mul,sub_zero,one_mul] at hb
  have hb' : (∫ t in 0..L, g t*t)=L*f L-(∫ t in 0..L,f t) := by
    simpa only [mul_comm] using hb
  have herr := cumulative_integral_error w a L E hL g hg hF
  rw [← hid,hb'] at herr
  have heq : (∑ i,w i*f (a i))-(∫ t in 0..L,f t) =
      f L*((∑ i,w i)-L)-
        (f L*(∑ i,w i)-(∑ i,w i*f (a i))-(L*f L-(∫ t in 0..L,f t))) := by ring
  rw [heq]
  apply (abs_sub _ _).trans
  have hprod := mul_le_mul_of_nonneg_left htotal (abs_nonneg (f L))
  rw [abs_mul]
  nlinarith only [hprod,herr]

end Erdos970.FiniteSelberg

namespace Erdos970.WeightedMertens
open Finset Real MeasureTheory Set Erdos970.FiniteSelberg
set_option maxHeartbeats 1800000

noncomputable def smoothProfileError : ℝ := sharpMomentError+1
lemma smoothProfileError_pos : 0 < smoothProfileError := by
  unfold smoothProfileError
  linarith [sharpMomentError_pos]

/-- Arithmetic prime sums have a coefficient-one leading integral for every
C1 profile on [1/2,log R]. The remainder is a fixed multiple of variation. -/
theorem prime_smooth_profile_error (R : ℕ) (hR : 2 ≤ R) (f g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume (1/2) (log (R : ℝ)))
    (hder : ∀ x ∈ Icc (1/2) (log (R : ℝ)), HasDerivAt f (g x) x) :
    |(∑ p ∈ (R+1).primesBelow, (log (p : ℝ)/(p : ℝ))*f (log (p : ℝ)))-
        (∫ t in (1/2)..log (R : ℝ), f t)| ≤
      smoothProfileError*(|f (log (R : ℝ))|+
        (∫ t in (1/2)..log (R : ℝ), |g t|)) := by
  let P := (R+1).primesBelow
  let L := log (R : ℝ)-1/2
  let w : P → ℝ := fun p => log (p.val : ℝ)/p.val
  let a : P → ℝ := fun p => log (p.val : ℝ)-1/2
  have hR0 : 0 < R := by omega
  have hl2 : (1/2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hLR : (1/2 : ℝ) ≤ log (R : ℝ) := hl2.trans
    (log_le_log (by norm_num) (by exact_mod_cast hR))
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have ha (p : P) : 0 ≤ a p ∧ a p ≤ L := by
    obtain ⟨hp,hpR⟩ := mem_primes.mp p.property
    have hlogp := hl2.trans (log_le_log (by norm_num) (show (2 : ℝ) ≤ p.val by exact_mod_cast hp.two_le))
    have hlogR := log_le_log (by exact_mod_cast hp.pos : (0 : ℝ) < p.val)
      (by exact_mod_cast hpR : (p.val : ℝ) ≤ R)
    dsimp [a,L]
    constructor <;> linarith
  have ht : |(∑ p : P,w p)-L| ≤ smoothProfileError := by
    have hh := abs_primeSum_sub_log R hR0
    have he : (∑ p : P,w p)=primeSum R := sum_coe_sort P (fun p : ℕ => log (p : ℝ)/p)
    rw [he]
    have hb := abs_add_le (primeSum R-log (R : ℝ)) (1/2 : ℝ)
    dsimp [L,smoothProfileError,sharpMomentError]
    norm_num at hb
    have heq : primeSum R-(log (R : ℝ)-1/2)=primeSum R-log (R : ℝ)+1/2 := by ring
    rw [heq]
    linarith only [hb,hh]
  have hcum (t : ℝ) : cumulativeMass w a t=initialPrimeCumulative R (t+1/2) := by
    rw [← initialPrimeCumulative_eq]
    unfold cumulativeMass
    apply sum_congr rfl
    intro p hp
    have he : a p < t ↔ log (p.val : ℝ) < t+1/2 := by
      dsimp [a]
      constructor <;> intro h <;> linarith
    simp only [he,w]
  have hF (t : ℝ) (ht : t ∈ Icc 0 L) :
      |cumulativeMass w a t-t| ≤ smoothProfileError := by
    rw [hcum]
    have hh := initialPrimeCumulative_error R hR0 (t+1/2) (by linarith [ht.1])
      (by dsimp [L] at ht; linarith [ht.2])
    have hb := abs_add_le (initialPrimeCumulative R (t+1/2)-(t+1/2)) (1/2 : ℝ)
    norm_num at hb
    have he : initialPrimeCumulative R (t+1/2)-t =
        (initialPrimeCumulative R (t+1/2)-(t+1/2))+1/2 := by ring
    rw [he]
    unfold smoothProfileError
    linarith only [hh,hb]
  have hg' : IntervalIntegrable (fun t : ℝ => g (t+1/2)) volume 0 L := by
    have hh := hg.comp_add_right (1/2)
    convert hh using 1 <;> dsimp [L] <;> ring
  have hd' (t : ℝ) (ht : t ∈ Icc 0 L) :
      HasDerivAt (fun x : ℝ => f (x+1/2)) (g (t+1/2)) t := by
    have ht' : t+1/2 ∈ Icc (1/2) (log (R : ℝ)) := by
      dsimp [L] at ht
      constructor <;> linarith [ht.1,ht.2]
    simpa only [mul_one] using (hder (t+1/2) ht').comp t ((hasDerivAt_id t).add_const (1/2))
  have hh := cumulative_differentiable_profile_error w a L smoothProfileError hL ha ht hF
    (fun t => f (t+1/2)) (fun t => g (t+1/2)) hg' hd'
  have he : L+1/2=log (R : ℝ) := by dsimp [L]; ring
  simp only [a,sub_add_cancel,intervalIntegral.integral_comp_add_right,zero_add,he] at hh
  have hs : (∑ p : P,w p*f (log (p.val : ℝ))) =
      ∑ p ∈ P,(log (p : ℝ)/(p : ℝ))*f (log (p : ℝ)) :=
    by simpa only [w] using sum_coe_sort P (fun p : ℕ => (log (p : ℝ)/(p : ℝ))*f (log (p : ℝ)))
  rw [hs] at hh
  have habs := intervalIntegral.integral_comp_add_right (a := 0) (b := L) (fun t => |g t|) (1/2)
  simp only [zero_add,he] at habs
  rw [habs] at hh
  exact hh


/-- A nonnegative increasing profile pays only twice its endpoint value in
the arithmetic transfer remainder. -/
theorem prime_monotone_profile_upper (R : ℕ) (hR : 2 ≤ R) (f g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume (1/2) (log (R : ℝ)))
    (hder : ∀ x ∈ Icc (1/2) (log (R : ℝ)), HasDerivAt f (g x) x)
    (hf : ∀ x ∈ Icc (1/2) (log (R : ℝ)), 0 ≤ f x)
    (hg0 : ∀ x ∈ Icc (1/2) (log (R : ℝ)), 0 ≤ g x) :
    (∑ p ∈ (R+1).primesBelow, (log (p : ℝ)/(p : ℝ))*f (log (p : ℝ))) ≤
      (∫ t in (1/2)..log (R : ℝ),f t)+2*smoothProfileError*f (log (R : ℝ)) := by
  have hl : (1/2 : ℝ) ≤ log (R : ℝ) :=
    (by linarith [log_two_gt_d9] : (1/2 : ℝ) ≤ log 2).trans
      (log_le_log (by norm_num) (by exact_mod_cast hR))
  have he : (∫ t in (1/2)..log (R : ℝ), |g t|) =
      f (log (R : ℝ))-f (1/2) := by
    have hi : (∫ t in (1/2)..log (R : ℝ), |g t|) =
        ∫ t in (1/2)..log (R : ℝ),g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hl] at ht
      exact abs_of_nonneg (hg0 t ht)
    rw [hi]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hder t (by rwa [uIcc_of_le hl] at ht)) hg
  have hh := (abs_le.mp (prime_smooth_profile_error R hR f g hg hder)).2
  rw [he,abs_of_nonneg (hf _ ⟨hl,le_rfl⟩)] at hh
  have hn := mul_nonneg smoothProfileError_pos.le (hf _ ⟨le_rfl,hl⟩)
  nlinarith only [hh,hn]


#print axioms prime_smooth_profile_error
#print axioms Erdos970.FiniteSelberg.cumulative_differentiable_profile_error
end Erdos970.WeightedMertens
