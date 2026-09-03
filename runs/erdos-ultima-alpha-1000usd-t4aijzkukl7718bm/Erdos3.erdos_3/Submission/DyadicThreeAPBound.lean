import Submission.FiniteThreeAPBound

/-! Explicit dyadic density parameters for the finite three-term bound. -/
namespace Erdos3DyadicThreeAPBound
open Finset Erdos3FiniteThreeAPBound Erdos3LocalDensityStep Erdos3StableSupportedIncrement
  Erdos3BohrIncrementParameters Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 3500000

noncomputable def dyadicDensity (l : ℕ) : ℝ := 1/(2 : ℝ)^l
def momentParameter (l : ℕ) : ℕ := 2*(l+40)
def supportParameter (l : ℕ) : ℕ := 8*momentParameter l*(l+1)+1
def stableParameter (l : ℕ) : ℕ := 2^(supportParameter l+20)
def iterationSteps (l : ℕ) : ℕ := 1024*(l+1)
def finalRank (l : ℕ) : ℕ := iterationSteps l*rankBudget (supportParameter l)
def dyadicGroupBound (l : ℕ) : ℕ := 32*2^(2*l)*coverFactor (finalRank l) (stableParameter l)*
  iterationVolume (finalRank l) (stableParameter l) (supportParameter l) (iterationSteps l)

lemma dyadicDensity_pos (l : ℕ) : 0 < dyadicDensity l := by unfold dyadicDensity; positivity
lemma dyadicDensity_le_one (l : ℕ) : dyadicDensity l ≤ 1 := by
  unfold dyadicDensity
  exact (one_div_le_one_div_of_le (by norm_num) (one_le_pow₀ (by norm_num))).trans_eq (by norm_num)
lemma momentParameter_ge (l : ℕ) : 67 ≤ momentParameter l := by unfold momentParameter; omega
lemma momentParameter_even (l : ℕ) : Even (momentParameter l) := even_two_mul _
lemma supportParameter_pos (l : ℕ) : 0 < supportParameter l := by unfold supportParameter; positivity
lemma supportParameter_ge (l : ℕ) : l ≤ supportParameter l := by
  have hp := momentParameter_ge l
  unfold supportParameter
  nlinarith
lemma stableParameter_pos (l : ℕ) : 0 < stableParameter l := by unfold stableParameter; positivity
lemma dyadicDensity_div_two (l : ℕ) : dyadicDensity l/2 = 1/(2 : ℝ)^(l+1) := by
  unfold dyadicDensity
  rw [pow_succ, div_div]
lemma two_div_dyadicDensity (l : ℕ) : 2/dyadicDensity l = (2 : ℝ)^(l+1) := by
  unfold dyadicDensity
  rw [div_div_eq_mul_div, div_one, pow_succ]
  ring

lemma dyadic_mean_error (l : ℕ) : 1/(stableParameter l : ℝ) ≤ dyadicDensity l/2048 := by
  have hl : l+11 ≤ supportParameter l+20 := by have := supportParameter_ge l; omega
  have hh : (2 : ℝ)^(l+11) ≤ 2^(supportParameter l+20) := pow_le_pow_right₀ (by norm_num) hl
  calc
    _ = 1/(2 : ℝ)^(supportParameter l+20) := by simp only [stableParameter, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 1/(2 : ℝ)^(l+11) := one_div_le_one_div_of_le (by positivity) hh
    _ = _ := by
      unfold dyadicDensity
      rw [pow_add, div_div]
      norm_num only [show (2 : ℝ)^11 = 2048 by norm_num]

lemma dyadic_mass (l : ℕ) : (2/3 : ℝ)^(momentParameter l) ≤ dyadicDensity l/2 := by
  rw [momentParameter, pow_mul, dyadicDensity_div_two]
  calc
    _ ≤ (1/2 : ℝ)^(l+40) := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ ≤ (1/2 : ℝ)^(l+1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by rw [div_pow, one_pow]

lemma dyadic_center_error (l : ℕ) :
    (1/(stableParameter l : ℝ))*(4/dyadicDensity l+1) ≤ 1/256 := by
  have ha := dyadicDensity_pos l
  have ha1 := dyadicDensity_le_one l
  have hδ : (0 : ℝ) ≤ 1/(stableParameter l : ℝ) := by positivity
  have hfactor : 4/dyadicDensity l+1 ≤ 8/dyadicDensity l := by
    apply (le_div_iff₀ ha).mpr
    field_simp
    nlinarith
  calc
    _ ≤ (1/(stableParameter l : ℝ))*(8/dyadicDensity l) := mul_le_mul_of_nonneg_left hfactor hδ
    _ ≤ (dyadicDensity l/2048)*(8/dyadicDensity l) :=
      mul_le_mul_of_nonneg_right (dyadic_mean_error l) (by positivity)
    _ = _ := by field_simp; norm_num

lemma power_gap {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) {n : ℕ} (hn : 0 < n) :
    x-y ≤ x^n-y^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hy0 : 0 ≤ y := by linarith
  have hpow : y^k ≤ x^k := pow_le_pow_left₀ hy0 hxy k
  have hone : 1 ≤ x^k := one_le_pow₀ (hy.trans hxy)
  have h₁ := mul_nonneg hy0 (sub_nonneg.mpr hpow)
  have h₂ := mul_le_mul_of_nonneg_left hone (sub_nonneg.mpr hxy)
  rw [pow_succ, pow_succ]
  nlinarith

lemma dyadic_local_error_exact (l : ℕ) :
    (1/(stableParameter l : ℝ))*(2/dyadicDensity l)^(8*momentParameter l) = 1/2097152 := by
  rw [two_div_dyadicDensity]
  unfold stableParameter supportParameter
  push_cast
  rw [← pow_mul, show (l+1)*(8*momentParameter l) = 8*momentParameter l*(l+1) by ring]
  rw [show 8*momentParameter l*(l+1)+1+20 = 8*momentParameter l*(l+1)+21 by omega, pow_add]
  have h : (2 : ℝ)^(8*momentParameter l*(l+1)) ≠ 0 := by positivity
  norm_num

lemma dyadic_local_error (l : ℕ) :
    (1/(stableParameter l : ℝ))*(2/dyadicDensity l)^(8*momentParameter l) ≤
      (17/16 : ℝ)^(8*momentParameter l)-(67/64 : ℝ)^(8*momentParameter l) := by
  rw [dyadic_local_error_exact]
  have hh := power_gap (by norm_num : (1 : ℝ) ≤ 67/64) (by norm_num : (67/64 : ℝ) ≤ 17/16)
    (by have := momentParameter_ge l; omega : 0 < 8*momentParameter l)
  linarith only [hh]

lemma dyadic_support_budget (l : ℕ) :
    (2 : ℝ)^(2*supportParameter l)*(dyadicDensity l/2)^(2*(8*momentParameter l)) = 4 := by
  rw [dyadicDensity_div_two, div_pow, one_pow, ← pow_mul]
  have he : 2*supportParameter l = (l+1)*(2*(8*momentParameter l))+2 := by
    unfold supportParameter
    ring
  rw [he, pow_add]
  have h : (2 : ℝ)^((l+1)*(2*(8*momentParameter l))) ≠ 0 := by positivity
  field_simp
  norm_num

lemma dyadic_iteration_gain (l : ℕ) : 1 < (1025/1024 : ℝ)^(iterationSteps l)*dyadicDensity l := by
  have hb : (2 : ℝ) ≤ (1025/1024 : ℝ)^1024 := by
    have hh := one_add_mul_le_pow (a := (1/1024 : ℝ)) (by norm_num : (-2 : ℝ) ≤ 1/1024) 1024
    norm_num only [Nat.cast_ofNat] at hh
    convert hh using 1 <;> norm_num
  have hg : (2 : ℝ) ≤ (1025/1024 : ℝ)^(iterationSteps l)*dyadicDensity l := by
    calc
      _ = (2 : ℝ)^(l+1)*dyadicDensity l := by
        unfold dyadicDensity
        rw [pow_succ]
        field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (dyadicDensity_pos l).le
        unfold iterationSteps
        rw [pow_mul]
        exact pow_le_pow_left₀ (by norm_num) hb _
  linarith

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A completely explicit bound depending only on the dyadic density, for odd groups. -/
theorem threeAPFree_card_lt_dyadic_bound (h2 : Function.Bijective (fun x : G ↦ x+x))
    (A : Finset G) (hA : A.Nonempty) (hfree : ThreeAPFree (A : Set G))
    (l : ℕ) (hdensity : dyadicDensity l ≤ density A) : Fintype.card G < dyadicGroupBound l := by
  have hh := finite_threeAP_bound h2 A hA hfree (dyadicDensity_pos l) hdensity
    (stableParameter_pos l) (momentParameter_ge l) (momentParameter_even l) (supportParameter_pos l)
    (dyadic_mean_error l) (dyadic_mass l) (dyadic_center_error l) (dyadic_local_error l)
    (dyadic_support_budget l).ge (dyadic_iteration_gain l)
  have hpow : (0 : ℝ) < (2 : ℝ)^l := by positivity
  have he : dyadicDensity l^2 = 1/(2 : ℝ)^(2*l) := by
    unfold dyadicDensity
    rw [div_pow, one_pow, ← pow_mul, mul_comm l 2]
  rw [he] at hh
  have hreal : (Fintype.card G : ℝ) < (dyadicGroupBound l : ℝ) := by
    unfold dyadicGroupBound finalRank
    push_cast
    have hp : (0 : ℝ) < (2 : ℝ)^(2*l) := by positivity
    have hh' := (div_lt_iff₀ hp).mp (show (Fintype.card G : ℝ)/(2 : ℝ)^(2*l) < _ by
      simpa only [one_div_mul_eq_div] using hh)
    nlinarith only [hh']
  exact_mod_cast hreal

#print axioms threeAPFree_card_lt_dyadic_bound
end Erdos3DyadicThreeAPBound
