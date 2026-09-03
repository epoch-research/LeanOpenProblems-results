import Submission.EulerMassUnrestrictedQuadrature
import Submission.BuchstabQuantitativeProfile

/-! Bounded-interval monotone quadrature for the exact prime-density measure.
No lower size restriction is imposed on the prime-sector cutoff. -/
namespace Erdos970.ContinuousBuchstab
open Real Set MeasureTheory
set_option maxHeartbeats 1300000

lemma antitone_rectangle_bound_finite (f : ℝ → ℝ) (a h : ℝ) (N : ℕ) (hh : 0 < h)
    (hf : AntitoneOn f (Ici a)) (hp : ∀ x : ℝ, a ≤ x → 0 ≤ f x) :
    (∑ j ∈ Finset.range N, h*f (a+h*j)) ≤
      (∫ x in a..a+h*N, f x)+h*f a := by
  have hmono : AntitoneOn (fun x : ℝ => f (a+h*x)) (Icc 0 (0+(N : ℝ))) := by
    intro x hx y hy hxy
    apply hf
    · change a ≤ a+h*x
      nlinarith only [hh,hx.1]
    · change a ≤ a+h*y
      nlinarith only [hh,hy.1]
    · nlinarith only [hh,hxy]
  have hright := hmono.sum_le_integral
  simp only [zero_add] at hright
  rw [intervalIntegral.integral_comp_add_mul f hh.ne' a,mul_zero,add_zero,smul_eq_mul] at hright
  have hr := mul_le_mul_of_nonneg_left hright hh.le
  rw [mul_inv_cancel_left₀ hh.ne'] at hr
  have ht := Finset.sum_range_sub' (fun j : ℕ => f (a+h*j)) N
  rw [Finset.sum_sub_distrib] at ht
  simp only [Nat.cast_zero,mul_zero,add_zero] at ht
  have hm := mul_le_mul_of_nonneg_left (hp (a+h*N) (by
    have hN := Nat.cast_nonneg (α := ℝ) N
    nlinarith only [hh,hN])) hh.le
  have htel := congrArg (fun z : ℝ => h*z) ht
  rw [← Finset.mul_sum]
  nlinarith only [hr,htel,hm]

lemma exists_rectangular_finite_upper (f : ℝ → ℝ) (a b ε : ℝ) (hab : a < b) (hε : 0 < ε)
    (hf : AntitoneOn f (Ici a)) (hp : ∀ x : ℝ, a ≤ x → 0 ≤ f x) :
    ∃ N : ℕ, 0 < N ∧
      (∑ j ∈ Finset.range N, ((b-a)/(N : ℝ))*f (a+((b-a)/(N : ℝ))*j)) <
        (∫ x in a..b, f x)+ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 ((b-a)*f a/ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hh : 0 < (b-a)/(N : ℝ) := div_pos (sub_pos.mpr hab) hN0
  have he : ((b-a)/(N : ℝ))*f a < ε := by
    have hlt := (le_max_right _ _).trans_lt hN
    have hm := (div_lt_iff₀ hε).mp hlt
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hN0).mpr
    nlinarith only [hm]
  have hbound := antitone_rectangle_bound_finite f a ((b-a)/(N : ℝ)) N hh hf hp
  have hend : a+(b-a)/(N : ℝ)*N=b := by field_simp; ring
  rw [hend] at hbound
  exact ⟨N,by exact_mod_cast hN0,by linarith only [hbound,he]⟩

end Erdos970.ContinuousBuchstab

namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg ContinuousBuchstab MeasureTheory Set
set_option maxHeartbeats 1600000

/-- Coefficient-one profile integral on any finite child-level interval.
The cumulative error is charged by profile variation, so an arbitrarily fine
mesh introduces no additional factor. -/
theorem prime_profile_interval_upper (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (s a z L : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (haz : a < z) (hL : 0 < L)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici a)) (hf0 : ∀ x, a ≤ x → 0 ≤ f x) :
    initialEulerMass (expFloor 1 L)*
      (∑ p ∈ (Finset.Ioc (expFloor (s/(z+1)) L) (expFloor (s/(a+1)) L)).filter Nat.Prime,
        ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*L/log (p : ℝ)-1)) ≤
      (∫ x in a..z, f x)/s+
        (2*(A+C+1)/((s/(z+1))*L))*(1+1/(s/(z+1)))*f a := by
  have hscale : 0 < s/(z+1) := div_pos hs (by linarith)
  let F : ℕ → ℝ := fun p =>
    ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*L/log (p : ℝ)-1)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨N,hN,hrect⟩ := exists_rectangular_finite_upper f a z (ε*s) haz (mul_pos hε hs) hf hf0
  let h : ℝ := (z-a)/(N : ℝ)
  let v : ℕ → ℝ := fun j => a+h*j
  let t : ℕ → ℝ := fun j => s/(v j+1)
  let b : ℕ → ℝ := fun j => f (v j)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < h := div_pos (sub_pos.mpr haz) hNr
  have hv : Monotone v := by
    intro i j hij
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp only [v]
    nlinarith only [hh,hijR]
  have hv0 : v 0=a := by simp [v]
  have hvN : v N=z := by dsimp [v,h]; field_simp; ring
  have hvlow (j : ℕ) : a ≤ v j := by simpa only [hv0] using hv (Nat.zero_le j)
  have hvnonneg (j : ℕ) : 0 ≤ v j := ha.trans (hvlow j)
  have ht : ∀ i, i ≤ N → s/(z+1) ≤ t i := by
    intro i hi
    have hh := hv hi
    rw [hvN] at hh
    exact div_le_div_of_nonneg_left hs.le (by linarith [hvnonneg i]) (by linarith)
  have htanti : ∀ i, i < N → t (i+1) ≤ t i := by
    intro i hi
    exact div_le_div_of_nonneg_left hs.le (by linarith [hvnonneg i])
      (by linarith [hv (Nat.le_succ i)])
  have hb : ∀ i, 0 ≤ b i := fun i => hf0 _ (hvlow i)
  have hbanti : Antitone b := fun i j hij => hf (hvlow i) (hvlow j) (hv hij)
  have hbin : ∀ i ∈ range N, ∀ p ∈ profileBin (s*L) (v i) (v (i+1)),
      F p ≤ b i*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
    intro i hi p hp
    have hc := profileBin_child_coordinate (s*L) (v i) (v (i+1)) (hvnonneg i) p hp
    have hprof := hf (hvlow i) ((hvlow i).trans hc) hc
    have hw : 0 ≤ (1/(p : ℝ))*(1/eulerMass p.primesBelow) := by
      have he := (eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2)).le
      positivity
    have hm := mul_le_mul_of_nonneg_left hprof hw
    simpa only [F,b,mul_comm] using hm
  have hbin' : ∀ i ∈ range N, ∀ p ∈
      (Finset.Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime,
      F p ≤ b i*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
    simpa only [profileBin,profileCut_scaled,t] using hbin
  have hquad := firstHit_monotone_majorant_unrestricted C A hC hA hrem (s/(z+1)) 1 L hscale
    (by norm_num) hL N t b ht htanti hb hbanti F hbin'
  have hquad' : initialEulerMass (expFloor 1 L)*
      (∑ i ∈ range N, ∑ p ∈ profileBin (s*L) (v i) (v (i+1)), F p) ≤
      (∑ i ∈ range N, b i*(1/t (i+1)-1/t i))+
        (2*(A+C+1)/((s/(z+1))*L))*(1+1/(s/(z+1)))*b 0 := by
    simpa only [profileBin,profileCut_scaled,t] using hquad
  have hpart := profileBins_sum (s*L) (mul_pos hs hL).le v hv (hvnonneg 0) N F
  rw [hv0,hvN,profileCut_scaled,profileCut_scaled] at hpart
  rw [hpart] at hquad'
  have hsum : (∑ i ∈ range N, b i*(1/t (i+1)-1/t i)) =
      (∑ i ∈ range N, h*f (v i))/s := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    dsimp only [t,b]
    rw [profile_sector_mass s _ _ hs (hvnonneg i) (hv (Nat.le_succ i))]
    have hstep : v (i+1)-v i=h := by dsimp [v]; push_cast; ring
    rw [hstep]
    ring
  have hbzero : b 0=f a := by dsimp [b]; rw [hv0]
  rw [hsum,hbzero] at hquad'
  have hrect' : (∑ i ∈ range N, h*f (v i)) < (∫ x in a..z, f x)+ε*s := hrect
  have hdiv := div_lt_div_of_pos_right hrect' hs
  rw [add_div,mul_div_cancel_right₀ _ hs.ne'] at hdiv
  change initialEulerMass (expFloor 1 L)*
      (∑ p ∈ (Finset.Ioc (expFloor (s/(z+1)) L) (expFloor (s/(a+1)) L)).filter Nat.Prime, F p) < _
  linarith only [hquad',hdiv]

#print axioms exists_rectangular_finite_upper
#print axioms prime_profile_interval_upper
end Erdos970.RecursiveSieve.Buchstab
