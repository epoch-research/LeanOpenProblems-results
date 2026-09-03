import Submission.SparseFourierModelTransfer
import Submission.HigherUniformityPerturbation

/-! Bounded integer-frequency characters of rounded phases approximate exact
integer products of the original phases. This transfers masked U2 without
claiming that rounding preserves polynomiality. The original integer product
is genuinely locally quadratic. -/
namespace Erdos3BoundedFrequencyPhaseApproximation
open Finset Erdos3FiniteFrequencyCoordinates Erdos3FiniteCircleGrid
  Erdos3FiniteUniformity Erdos3StableMaskedUniformity Erdos3CorrelationSifting
  Erdos3HigherUniformityPerturbation Erdos3LocalQuadraticInverse
  Erdos3LocalCircleFactorCounting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000

lemma unit_zpow_distance {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (k : ℤ) :
    ‖a^k-b^k‖ ≤ (k.natAbs : ℝ)*‖a-b‖ := by
  cases k with
  | ofNat n => simpa only [zpow_natCast,Int.natAbs_natCast] using unit_power_distance ha hb n
  | negSucc n =>
    have ha' : conj (a^(n+1)) = (a^(n+1))⁻¹ :=
      eq_inv_of_mul_eq_one_right (mul_conj_eq_one (by rw [norm_pow,ha,one_pow]))
    have hb' : conj (b^(n+1)) = (b^(n+1))⁻¹ :=
      eq_inv_of_mul_eq_one_right (mul_conj_eq_one (by rw [norm_pow,hb,one_pow]))
    rw [zpow_negSucc,zpow_negSucc,← ha',← hb',← map_sub,Complex.norm_conj]
    simpa only [Int.natAbs_negSucc] using unit_power_distance ha hb (n+1)

lemma unit_prod_distance {J : Type*} (s : Finset J) (v w : J → ℂ)
    (hv : ∀ i ∈ s, ‖v i‖ = 1) (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ‖(∏ i ∈ s, v i)-(∏ i ∈ s, w i)‖ ≤ ∑ i ∈ s, ‖v i-w i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi,prod_insert hi,sum_insert hi]
    have hws : ‖∏ j ∈ s, w j‖ = 1 := by
      rw [norm_prod]
      exact prod_eq_one (fun j hj ↦ hw j (mem_insert_of_mem hj))
    exact (unit_mul_distance (hv i (mem_insert_self _ _)) hws).trans
      (add_le_add le_rfl (ih (fun j hj ↦ hv j (mem_insert_of_mem hj))
        (fun j hj ↦ hw j (mem_insert_of_mem hj))))

variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]

noncomputable def integerPhase (k : I → ℤ) (v : I → ℂ) : ℂ := ∏ i : I, (v i)^(k i)

lemma integerPhase_norm (k : I → ℤ) (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    ‖integerPhase k v‖ = 1 := by
  simp only [integerPhase,norm_prod,norm_zpow,hv,one_zpow,prod_const_one]

/-- Bounded frequencies have a rounding error tending to zero with N. -/
theorem integerCharacter_rounding_error (k : I → ℤ) {R : ℕ}
    (hk : ∀ i, |k i| ≤ R) (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    ‖integerCharacter k (fun i ↦ roundPhase N (v i))-integerPhase k v‖ ≤
      8*(Fintype.card I : ℝ)*(R : ℝ)/(N : ℝ) := by
  rw [integerCharacter_apply]
  have hnorm (i : I) : ‖(ZMod.stdAddChar (roundPhase N (v i)))^(k i)‖ = 1 := by
    rw [norm_zpow,(ZMod.stdAddChar (N := N)).norm_apply,one_zpow]
  have hnorm' (i : I) : ‖(v i)^(k i)‖ = 1 := by rw [norm_zpow,hv,one_zpow]
  apply (unit_prod_distance univ _ _ (fun i _ ↦ hnorm i) (fun i _ ↦ hnorm' i)).trans
  have hpoint (i : I) : ‖(ZMod.stdAddChar (roundPhase N (v i)))^(k i)-(v i)^(k i)‖ ≤
      (R : ℝ)*(8/(N : ℝ)) := by
    have hkR : ((k i).natAbs : ℝ) ≤ R := by
      have ht := hk i
      rw [← Int.natCast_natAbs] at ht
      exact_mod_cast ht
    apply (unit_zpow_distance ((ZMod.stdAddChar (N := N)).norm_apply _) (hv i) (k i)).trans
    exact mul_le_mul hkR (roundPhase_error (v i) (hv i)) (norm_nonneg _) (Nat.cast_nonneg R)
  calc
    _ ≤ ∑ _i : I, (R : ℝ)*(8/(N : ℝ)) := sum_le_sum (fun i _ ↦ hpoint i)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma masked_phase_meanDistance (W : Finset G) (f g : G → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (herr : ∀ x, ‖f x-g x‖ ≤ δ) : meanDistance (mask W f) (mask W g) ≤ density W*δ := by
  have hpoint (x : G) : ‖mask W f x-mask W g x‖ ≤ indicator W x*δ := by
    by_cases hx : x ∈ W
    · simpa only [mask,indicator,if_pos hx,one_mul] using herr x
    · simp only [mask,indicator,if_neg hx,sub_self,norm_zero,zero_mul,le_refl]
  calc
    _ ≤ 𝔼 x : G, indicator W x*δ := expect_le_expect (fun x _ ↦ hpoint x)
    _ = _ := by rw [← expect_mul,expect_indicator]

/-- U2 of a rounded bounded-frequency character differs from the U2 of its
exact original phase by an explicit vanishing error. -/
theorem rounded_integer_U2_error (W : Finset G) (Q : I → G → ℂ)
    (hQ : ∀ i x, ‖Q i x‖ = 1) (k : I → ℤ) {R : ℕ} (hk : ∀ i, |k i| ≤ R) :
    |uniformityPower 1 (mask W (fun x ↦ integerCharacter (N := N) k (fun i ↦ roundPhase N (Q i x))))-
      uniformityPower 1 (mask W (fun x ↦ integerPhase k (fun i ↦ Q i x)))| ≤
      32*density W*(Fintype.card I : ℝ)*(R : ℝ)/(N : ℝ) := by
  have hp := uniformity_lipschitz 1
    (mask W (fun x ↦ integerCharacter (N := N) k (fun i ↦ roundPhase N (Q i x))))
    (mask W (fun x ↦ integerPhase k (fun i ↦ Q i x)))
    (fun x ↦ mask_norm_le W _ (fun x ↦ ((integerCharacter (N := N) k).norm_apply _).le) x)
    (fun x ↦ mask_norm_le W _ (fun x ↦ (integerPhase_norm k _ (fun i ↦ hQ i x)).le) x)
  have hd := masked_phase_meanDistance W
    (fun x ↦ integerCharacter (N := N) k (fun i ↦ roundPhase N (Q i x)))
    (fun x ↦ integerPhase k (fun i ↦ Q i x)) (by positivity)
    (fun x ↦ integerCharacter_rounding_error k hk (fun i ↦ Q i x) (fun i ↦ hQ i x))
  apply hp.trans
  have h := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4)
  convert h using 1 <;> norm_num <;> ring

lemma derivative_integerPhase (k : I → ℤ) (Q : I → G → ℂ) (h : G) :
    derivative (fun x ↦ integerPhase k (fun i ↦ Q i x)) h =
      fun x ↦ integerPhase k (fun i ↦ derivative (Q i) h x) := by
  funext x
  simp only [integerPhase,derivative,map_prod,map_zpow₀,← prod_mul_distrib,← mul_zpow]

/-- The unrounded phase combination is genuinely locally quadratic, including
negative integer powers. -/
theorem integerPhase_locally_quadratic {W : Set G} (k : I → ℤ) (Q : I → G → ℂ)
    (hpoly : ∀ i, IsLocallyQuadratic W (Q i)) :
    IsLocallyQuadratic W (fun x ↦ integerPhase k (fun i ↦ Q i x)) := by
  intro x h l m hx hxh hxl hxlh hxm hxmh hxml hxmlh
  rw [derivative_integerPhase,derivative_integerPhase,derivative_integerPhase]
  simp only [integerPhase,hpoly _ x h l m hx hxh hxl hxlh hxm hxmh hxml hxmlh,
    one_zpow,prod_const_one]

#print axioms integerCharacter_rounding_error
#print axioms rounded_integer_U2_error
#print axioms integerPhase_locally_quadratic
end Erdos3BoundedFrequencyPhaseApproximation
