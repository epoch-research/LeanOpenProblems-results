import Submission.SmoothPredecessorLogBias

/-!
# Bias at moduli no larger than the predecessor smoothness cutoff

This disproves an unconditioned relative mean for the actual supplied
smooth-prime family even when its modulus cutoff equals its smoothness
cutoff, strictly below sqrt(N). It does not disprove Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma log_dyadic_nat (a m : ℕ) :
    Real.log ((2^(a*m) : ℕ) : ℝ) = (a : ℝ)*m*Real.log 2 := by
  rw [Nat.cast_pow,Nat.cast_two,Real.log_pow,Nat.cast_mul]

lemma dyadic_log_small_input_error (T m : ℕ) (hT : 2 ≤ T)
    (hpoly : (3*T^2)*((m : ℝ)+1)^2 ≤ (2 : ℝ)^m)
    (F : ℝ) (hF : ((2^(T*m) : ℕ) : ℝ) ≤ (2 : ℝ)^m*F) :
    Real.log ((2^((T-2)*m) : ℕ) : ℝ)*Real.log ((2^(T*m) : ℕ) : ℝ)*
      (((2^((T-2)*m) : ℕ) : ℝ)+2*((2^(T*m) : ℕ) : ℝ)/(2^(2*m) : ℕ)) ≤ F := by
  let L : ℝ := ((2^((T-2)*m) : ℕ) : ℝ)
  let N : ℝ := ((2^(T*m) : ℕ) : ℝ)
  let W : ℝ := ((2^(2*m) : ℕ) : ℝ)
  let Z : ℝ := (2 : ℝ)^m
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hW : W = Z^2 := by
    dsimp [W,Z]
    push_cast
    rw [← pow_mul,mul_comm m 2]
  have hNL : N = W*L := by
    dsimp [N,W,L]
    rw [← Nat.cast_mul,← pow_add]
    congr 2
    nlinarith only [Nat.sub_add_cancel hT]
  have hNW : N/W = L := by
    rw [hNL,mul_div_cancel_left₀ _ (by rw [hW]; positivity)]
  have hLF : Z*L ≤ F := by
    apply (mul_le_mul_iff_right₀ hZ).mp
    calc
      Z*(Z*L) = N := by rw [hNL,hW]; ring
      _ ≤ Z*F := hF
  have hlogN : Real.log N ≤ (T : ℝ)*m := by
    change Real.log ((2^(T*m) : ℕ) : ℝ) ≤ _
    rw [log_dyadic_nat]
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2))
      (show 0 ≤ (T : ℝ)*m by positivity)
    norm_num at hh
    exact hh
  have hlogL : Real.log L ≤ (T : ℝ)*m := by
    apply le_trans _ hlogN
    apply log_nat_mono
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right m (Nat.sub_le T 2))
  have hprod := mul_le_mul hlogL hlogN
    (Real.log_natCast_nonneg (2^(T*m))) (show 0 ≤ (T : ℝ)*m by positivity)
  have hm2 : (m : ℝ)^2 ≤ ((m : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hcoef : 3*Real.log L*Real.log N ≤ Z := by
    have hh := mul_le_mul_of_nonneg_left hm2 (show 0 ≤ 3*(T : ℝ)^2 by positivity)
    change (3*(T : ℝ)^2)*((m : ℝ)+1)^2 ≤ Z at hpoly
    nlinarith only [hprod,hh,hpoly]
  change Real.log L*Real.log N*(L+2*N/W) ≤ F
  have he : L+2*N/W = 3*L := by rw [mul_div_assoc,hNW]; ring
  rw [he]
  calc
    Real.log L*Real.log N*(3*L) = (3*Real.log L*Real.log N)*L := by ring
    _ ≤ Z*L := mul_le_mul_of_nonneg_right hcoef (by dsimp [L]; positivity)
    _ ≤ F := hLF

/-- Any sufficiently massive smooth-supported weight has a relative error
at least one, already at moduli below its own smoothness cutoff. -/
theorem eventually_smooth_low_modulus_bias (T B : ℕ) (hB : 6 ≤ B) (hT : 2*B+3 ≤ T) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) →
      (∀ n ∈ Icc 1 (2^(T*m)), f n ≠ 0 → 2 ≤ n ∧ n-1 ∈ Nat.smoothNumbers (2^(B*m))) →
      ((2^(T*m) : ℕ) : ℝ) ≤ (2 : ℝ)^m*restrictedMass f (2^(T*m)) →
      restrictedMass f (2^(T*m)) ≤ primeOnlyRestrictedError f (2^(B*m)) (2^(T*m)) := by
  obtain ⟨C,hC,HC⟩ := exists_truncatedLogMainTerm_sharp_bound
  obtain ⟨M,hM⟩ := exists_nat_gt (2*(C+1))
  filter_upwards [eventually_ge_atTop (max 1 M),
    eventually_nat_poly_le_two_pow 1 (3*T^2) 2] with m hm hpoly
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hMm : M ≤ m := (le_max_right _ _).trans hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hCsmall : C+1 ≤ (m : ℝ)*Real.log 2 := by
    have hMb : (M : ℝ) ≤ m := by exact_mod_cast hMm
    have hh := mul_le_mul_of_nonneg_left
      (show (1/2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) hmR.le
    linarith only [hM,hMb,hh]
  have hloggap : 2*Real.log ((2^(B*m) : ℕ) : ℝ)+C+1 ≤
      Real.log ((2^((T-2)*m) : ℕ) : ℝ) := by
    rw [log_dyadic_nat,log_dyadic_nat]
    have hcoef : (2*(B : ℝ)+1) ≤ (T-2 : ℕ) := by exact_mod_cast (show 2*B+1 ≤ T-2 by omega)
    have hh := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ (m : ℝ)*Real.log 2 by positivity)
    nlinarith only [hh,hCsmall]
  have hY : 1 ≤ (2 : ℕ)^(B*m) := one_le_pow₀ (by decide)
  have hW : 0 < 2^(2*m) := by positivity
  have hWY : (2^(2*m))^3 ≤ (2 : ℕ)^(B*m) := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [hB]
  have hlogY : 0 < Real.log ((2^(B*m) : ℕ) : ℝ) := by
    rw [log_dyadic_nat]
    exact mul_pos (mul_pos (by exact_mod_cast (show 0 < B by omega)) hmR)
      (Real.log_pos (by norm_num))
  intro f hf hΛ hs hmass
  have hbias := smooth_restricted_log_bias_of_sharp_main f hf hΛ
    (2^(T*m)) (2^(B*m)) (2^((T-2)*m)) (2^(2*m)) hW hWY hs C (HC _ hY)
  have hpolyR : (3*(T : ℝ)^2)*((m : ℝ)+1)^2 ≤ (2 : ℝ)^m := by
    exact_mod_cast (by simpa only [one_mul] using hpoly : (3*T^2)*(m+1)^2 ≤ 2^m)
  have herr := dyadic_log_small_input_error T m (by omega) hpolyR (restrictedMass f _) hmass
  have hF := restrictedMass_nonneg f hf (2^(T*m))
  have hgap := mul_le_mul_of_nonneg_right hloggap hF
  apply (mul_le_mul_iff_right₀ hlogY).mp
  nlinarith only [hbias,herr,hgap]

lemma supplied_smooth_cutoff_below_half (m : ℕ) (hm : 1 ≤ m) :
    (cofactorScale 44425 (2*m))^2 < cofactorScale 100005 (2*m) := by
  rw [cofactorScale_eq,cofactorScale_eq,← pow_mul]
  apply Nat.pow_lt_pow_right (by decide)
  nlinarith

/-- This is the actual, unconditionally supplied smooth-prime population.
No prime modulus above Y is used in the discrepancy lower bound. -/
theorem eventually_supplied_smooth_cutoff_bias :
    ∀ᶠ m : ℕ in atTop,
      let N := cofactorScale 100005 (2*m)
      let Y := cofactorScale 44425 (2*m)
      let f := smoothMangoldtWeight N Y
      0 < restrictedMass f N ∧ restrictedMass f N ≤ primeOnlyRestrictedError f Y N := by
  filter_upwards [eventually_smooth_low_modulus_bias (512*100005) (512*44425) (by decide) (by decide),
    eventually_supplied_smooth_mass] with m hmean hmass
  dsimp only
  have hN : cofactorScale 100005 (2*m) = 2^((512*100005)*m) := by
    rw [cofactorScale_eq]
    congr 1
    ring
  have hY : cofactorScale 44425 (2*m) = 2^((512*44425)*m) := by
    rw [cofactorScale_eq]
    congr 1
    ring
  rw [hN,hY] at hmass ⊢
  have hpos : 0 < restrictedMass
      (smoothMangoldtWeight (2^((512*100005)*m)) (2^((512*44425)*m))) (2^((512*100005)*m)) := by
    have hN0 : (0 : ℝ) < ((2^((512*100005)*m) : ℕ) : ℝ) := by positivity
    have hZ : (0 : ℝ) < (2 : ℝ)^m := by positivity
    nlinarith only [hmass,hN0,hZ]
  refine ⟨hpos,?_⟩
  exact hmean _ (mangoldtRestriction_nonneg _) (mangoldtRestriction_le _)
    (fun n _ hn => smoothMangoldtWeight_support _ _ n hn) hmass

theorem not_supplied_smooth_cutoff_relative_decay :
    ¬(∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      let N := cofactorScale 100005 (2*m)
      let Y := cofactorScale 44425 (2*m)
      let f := smoothMangoldtWeight N Y
      primeOnlyRestrictedError f Y N ≤ η*restrictedMass f N) := by
  intro H
  obtain ⟨m,hm⟩ := ((H (1/2) (by norm_num)).and eventually_supplied_smooth_cutoff_bias).exists
  dsimp only at hm
  linarith only [hm.1,hm.2.1,hm.2.2]

end Erdos821.AnalyticSieve
