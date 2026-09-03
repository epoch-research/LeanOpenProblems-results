import Submission.GreedyRelaxedSquareCertificate
import Submission.RefinedSquareLower

/-! An unrestricted square-Sidon lower bound from the relaxed growing-horizon certificate. -/
namespace Erdos773.RelaxedSquareLower
open Finset Filter GreedyHorizonFactors GreedyCodegreeSquareScales SquareCollisionCodegrees RefinedSquareLower
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
noncomputable section

def longHorizon (L : ℝ) : ℝ := (1/50:ℝ)*L^(1/3:ℝ)

lemma long_horizon_cube {L : ℝ} (hL : 0 ≤ L) : (longHorizon L)^3 = L/125000 := by
  unfold longHorizon
  rw [mul_pow,← Real.rpow_mul_natCast hL]
  norm_num; ring

lemma long_horizon_large {L : ℝ} (hL : 1000000000000000000000000 ≤ L) : 100000 ≤ longHorizon L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (show 0 ≤ longHorizon L by unfold longHorizon; positivity)
  rw [long_horizon_cube hL0]
  norm_num
  linarith only [hL]

lemma long_horizon_budget {X : ℝ} {n : ℕ} (hX : 0 < X)
    (hL : 1000000000000000000000000 ≤ Real.log X) (hvolume : X ≤ (n:ℝ)^301) :
    horizonBudget (longHorizon (Real.log X)) ≤ (n:ℝ)^25 := by
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  have hτ := long_horizon_large hL
  have hτ3 := long_horizon_cube hL0
  have hp := pow_le_pow_left₀ (by linarith only [hτ] : (0:ℝ) ≤ 1+longHorizon (Real.log X))
    (by linarith only [hτ] : 1+longHorizon (Real.log X) ≤ (100001/100000:ℝ)*longHorizon (Real.log X)) 3
  rw [mul_pow,hτ3] at hp
  have he : horizonBudget (longHorizon (Real.log X)) ≤ (Real.exp (Real.log X/301))^25 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hp,hL0]
  have hexp : Real.exp (Real.log X/301) = X^(1/301:ℝ) := by
    rw [Real.rpow_def_of_pos hX]
    congr 1
    ring
  rw [hexp] at he
  apply he.trans
  apply pow_le_pow_left₀ (Real.rpow_nonneg hX.le _) _ 25
  have hr := (Real.rpow_inv_le_iff_of_pos hX.le (Nat.cast_nonneg n) (by norm_num : (0:ℝ) < 301)).mpr
    (show X ≤ (n:ℝ)^(301:ℝ) by
      change X ≤ (n:ℝ)^((301:ℕ):ℝ)
      rw [Real.rpow_natCast]
      exact hvolume)
  norm_num only [inv_eq_one_div] at hr
  exact hr

lemma long_scale_lower {X L a M : ℝ} {n : ℕ} (hX : 0 < X) (hL : 0 < L)
    (hn : 0 < n) (ha : (3/4:ℝ)*X/L ≤ a)
    (hdegree : (n:ℝ)^300*L^2 ≤ (667/500:ℝ)*X)
    (hM : longHorizon L*a/((100/99:ℝ)*(n:ℝ)^100) ≤ M) :
    (1/75:ℝ)*X^(2/3:ℝ) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3 = X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hτ : 0 ≤ longHorizon L := by unfold longHorizon; positivity
  have hcube : ((n:ℝ)^100*L)^3 ≤ (667/500:ℝ)*X*L := by
    have hh := mul_le_mul_of_nonneg_right hdegree hL.le
    nlinarith only [hh]
  have hden : (400/297:ℝ)*(n:ℝ)^100*L ≤ (3/2:ℝ)*R := by
    have hh : (n:ℝ)^100*L ≤ (891/800:ℝ)*R := by
      apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (by positivity : 0 ≤ (891/800:ℝ)*R)
      rw [show ((891/800:ℝ)*R)^3 = (891/800:ℝ)^3*(X*L) by rw [mul_pow,hR3]]
      nlinarith only [hcube,mul_nonneg hX.le hL.le]
    linarith only [hh]
  have hsmall := div_le_div_of_nonneg_left (show 0 ≤ longHorizon L*X by positivity)
    (by positivity : 0 < (400/297:ℝ)*(n:ℝ)^100*L) hden
  have hsize := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hτ)
    (by positivity : 0 ≤ (100/99:ℝ)*(n:ℝ)^100)
  have he : longHorizon L*((3/4:ℝ)*X/L)/((100/99:ℝ)*(n:ℝ)^100) =
      longHorizon L*X/((400/297:ℝ)*(n:ℝ)^100*L) := by ring
  rw [he] at hsize
  have hid : longHorizon L*X/((3/2:ℝ)*R) = (1/75:ℝ)*X^(2/3:ℝ) := by
    have hx : 0 < X^(1/3:ℝ) := Real.rpow_pos_of_pos hX _
    have hl : 0 < L^(1/3:ℝ) := Real.rpow_pos_of_pos hL _
    have hxsum : X^(1/3:ℝ)*X^(2/3:ℝ) = X := by
      rw [← Real.rpow_add hX]
      norm_num
    dsimp [longHorizon,R]
    rw [Real.mul_rpow hX.le hL.le]
    field_simp
    nlinarith only [hxsum]
  rw [← hid]
  exact hsmall.trans (hsize.trans hM)



/-- An improved actual lower bound for the unrestricted maximum. The exponent
    is still two thirds and the coefficient is still below one. -/
theorem eventual_power_lower : ∀ᶠ N : ℕ in atTop,
    (1/75:ℝ)*(N:ℝ)^(2/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  obtain ⟨M,hcert⟩ := eventually_atTop.mp (GreedyRelaxedSquareCertificate.eventually_certificate 301)
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/602)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ) < 1)
  filter_upwards [ControlledSquareSampling.logarithmic_sampling (1/1000) (by norm_num),
    eventually_pair_codegree_bound (1/301) (by norm_num),hlog.eventually_ge_atTop 1000000000000000000000000,
    hsmall,eventually_ge_atTop 1,eventually_ge_atTop ((max M 1000001)^301)]
    with N hsample hcodeg hL hsmall hN hNM
  have hX : (0:ℝ) < N := by exact_mod_cast hN
  have hX1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hLpos : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs : Real.log (N:ℝ) ≤ (N:ℝ)^(1/602:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hLpos.le,
      abs_of_nonneg (Real.rpow_nonneg hX.le (1/602:ℝ)),one_mul] using hsmall
  have hlogSquare : (Real.log (N:ℝ))^2 ≤ (N:ℝ)^(1/301:ℝ) := by
    have hh := pow_le_pow_left₀ hLpos.le hs 2
    have he : ((N:ℝ)^(1/602:ℝ))^2 = (N:ℝ)^(1/301:ℝ) := by
      rw [← Real.rpow_mul_natCast hX.le]
      norm_num
    rwa [he] at hh
  let m := degreeRoot (N:ℝ) (Real.log N)
  have hvolume : (N:ℝ) ≤ (m:ℝ)^301 := volume301 hX1 hLpos hlogSquare
  have hvolumeNat : N ≤ m^301 := by exact_mod_cast hvolume
  have hmmax : max M 1000001 ≤ m :=
    (Nat.pow_le_pow_iff_left (by omega : (301:ℕ) ≠ 0)).mp (hNM.trans hvolumeNat)
  have hmM : M ≤ m := (le_max_left _ _).trans hmmax
  have hm1000001 : 1000001 ≤ m := (le_max_right _ _).trans hmmax
  have hmpos : 0 < m := by omega
  have hmone : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hupper := refined_root_upper hX.le hLpos hm1000001
  have hroot : (N:ℝ)^(1/301:ℝ) ≤ (m:ℝ) := by
    have hh := (Real.rpow_inv_le_iff_of_pos hX.le (Nat.cast_nonneg m) (by norm_num : (0:ℝ) < 301)).mpr
      (show (N:ℝ) ≤ (m:ℝ)^(301:ℝ) by
        change (N:ℝ) ≤ (m:ℝ)^((301:ℕ):ℝ)
        rw [Real.rpow_natCast]
        exact hvolume)
    simpa only [inv_eq_one_div] using hh
  have hm3 : (m:ℝ) ≤ (m:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hmone (by omega : 1 ≤ 3)
  obtain ⟨A,hAN,hAP,hsize,hAupper,hE⟩ := hsample
  norm_num at hsize hE
  have hK : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (pairEdges A a b).card ≤ m^3 := by
    intro a ha b hb hab
    have hmono : ((pairEdges A a b).card:ℝ) ≤ ((pairEdges (Icc 1 N) a b).card:ℝ) := by
      exact_mod_cast card_le_card (pairEdges_mono hAN a b)
    exact_mod_cast (hmono.trans (hcodeg a (hAN ha) b (hAN hb) hab)).trans (hroot.trans hm3)
  have hτ : 1 ≤ longHorizon (Real.log (N:ℝ)) := by linarith only [long_horizon_large hL]
  have hbudget := long_horizon_budget hX hL hvolume
  have hD : 0 < degreeScale (N:ℝ) (Real.log N) := by unfold degreeScale; positivity
  have hM := hcert m hmM (longHorizon (Real.log (N:ℝ))) hτ hbudget N A hAN hvolume hAP hK
    (degreeScale N (Real.log N)) hD (root_lower hX.le)
  exact long_scale_lower hX hLpos hmpos (trim_surplus hX hLpos hsize hE) hupper hM


#print axioms long_horizon_budget
#print axioms long_scale_lower
#print axioms eventual_power_lower
end
end Erdos773.RelaxedSquareLower
