import Submission.UniformityCounting

/-! Two-function counting and interval-relative masked counting. The reference
function need not be constant on the whole ambient group. -/
namespace Erdos3MaskedUniformityCounting
open Finset Erdos3UniformityCounting Erdos3LinearFormsUniformity Erdos3FiniteUniformity
  Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {F : Type*} [Field F] [Fintype F]

/-- Telescoping compares any two bounded functions when their difference has
small uniformity. No ambient-constant reference function is required. -/
theorem counting_difference (n : ℕ) (v : Fin (n+2) → F) (hv : Function.Injective v)
    (f g : F → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hfg : ∀ x, ‖f x-g x‖ ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower n (fun x ↦ f x-g x) ≤ η^(2^(n+1))) :
    ‖linearAverage v (fun _ ↦ f)-linearAverage v (fun _ ↦ g)‖ ≤ (n+2 : ℕ)*η := by
  let H : ℕ → ℂ := fun j ↦ linearAverage v (blend f g j)
  have hstep (j : ℕ) (hj : j < n+2) : ‖H (j+1)-H j‖ ≤ η := by
    let i : Fin (n+2) := ⟨j,hj⟩
    let f' := replace (blend f g j) i (fun x ↦ f x-g x)
    have hf' (s : Fin (n+2)) (x : F) : ‖f' s x‖ ≤ 1 := by
      dsimp [f',replace,blend]
      split_ifs <;> first | exact hfg x | exact hf x | exact hg x
    have hh := distinct_slopes_bound n v hv f' hf' i
    have he : f' i = fun x ↦ f x-g x := by funext x; simp only [f',replace,if_true]
    rw [he] at hh
    have hnorm := le_of_pow_le_pow_left₀ (by positivity : 2^(n+1) ≠ 0) hη (hh.trans hU)
    simpa only [H,blend_step v f g hj,f',i] using hnorm
  have hzero : H 0 = linearAverage v (fun _ ↦ g) := by dsimp [H]; rw [blend_zero]
  have hfull : H (n+2) = linearAverage v (fun _ ↦ f) := by dsimp [H]; rw [blend_full]
  rw [← hfull,← hzero,← sum_range_sub H (n+2)]
  calc
    _ ≤ ∑ j ∈ range (n+2), ‖H (j+1)-H j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (n+2), η := sum_le_sum (fun j hj ↦ hstep j (mem_range.mp hj))
    _ = _ := by simp

lemma linearAverage_scalar {k : ℕ} (v : Fin k → F) (f : F → ℂ) (α : ℂ) :
    linearAverage v (fun _ x ↦ α*f x) = α^k*linearAverage v (fun _ ↦ f) := by
  simp only [linearAverage,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,mul_expect]

lemma masked_indicator_bound (A B : Finset F) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (x : F) :
    |indicator A x-α*indicator B x| ≤ 1 := by
  have hf := indicator_norm_bounds A x
  have hg := indicator_norm_bounds B x
  have hmul : 0 ≤ α*indicator B x ∧ α*indicator B x ≤ 1 :=
    ⟨mul_nonneg hα hg.1,(mul_le_mul hα1 hg.2 hg.1 (by norm_num)).trans_eq (by norm_num)⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Counting relative to the mask B, not relative to the whole group. -/
theorem masked_counting_lemma (n : ℕ) (v : Fin (n+2) → F) (hv : Function.Injective v)
    (A B : Finset F) {α η : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hη : 0 ≤ η)
    (hU : uniformityPower n (fun x ↦ ((indicator A x-α*indicator B x : ℝ) : ℂ)) ≤ η^(2^(n+1))) :
    ‖linearAverage v (fun _ x ↦ (indicator A x : ℂ))-
      (α : ℂ)^(n+2)*linearAverage v (fun _ x ↦ (indicator B x : ℂ))‖ ≤ (n+2 : ℕ)*η := by
  have hA (x : F) : ‖(indicator A x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (indicator_norm_bounds A x).1]
      using (indicator_norm_bounds A x).2
  have hB (x : F) : ‖((α*indicator B x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hα (indicator_norm_bounds B x).1)]
    exact (mul_le_mul hα1 (indicator_norm_bounds B x).2 (indicator_norm_bounds B x).1 (by norm_num)).trans_eq (by norm_num)
  have hh := counting_difference n v hv (fun x ↦ (indicator A x : ℂ))
    (fun x ↦ ((α*indicator B x : ℝ) : ℂ)) hA hB
    (fun x ↦ by simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using masked_indicator_bound A B hα hα1 x)
    hη (by simpa only [Complex.ofReal_sub] using hU)
  simpa only [Complex.ofReal_mul,linearAverage_scalar] using hh

/-- A mask containing many patterns forces large relative uniformity when
A contains only diagonal patterns and the diagonal contribution is small. -/
theorem masked_pattern_uniformity_lower (n : ℕ) (v : Fin (n+2) → F)
    (hv : Function.Injective v) (A B : Finset F) {α β : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hbase : β ≤ (linearAverage v (fun _ x ↦ (indicator B x : ℂ))).re)
    (hsmall : density A/(Fintype.card F : ℝ) ≤ α^(n+2)*β/4)
    (hdiag : ∀ x d : F, (∀ i : Fin (n+2), x+v i*d ∈ A) → d = 0) :
    (α^(n+2)*β/(2*(n+2 : ℕ)))^(2^(n+1)) <
      uniformityPower n (fun x ↦ ((indicator A x-α*indicator B x : ℝ) : ℂ)) := by
  apply lt_of_not_ge
  intro hU
  have hc := masked_counting_lemma n v hv A B hα.le hα1 (by positivity) hU
  rw [indicator_diagonal_average (by omega : 0 < n+2) v A hdiag] at hc
  have hre := (Complex.abs_re_le_norm
    ((density A : ℂ)/(Fintype.card F : ℂ)-(α : ℂ)^(n+2)*linearAverage v (fun _ x ↦ (indicator B x : ℂ)))).trans hc
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_div,← Complex.ofReal_pow,
    Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hre
  have hhalf : ((n+2 : ℕ) : ℝ)*(α^(n+2)*β/(2*(n+2 : ℕ))) = α^(n+2)*β/2 := by
    have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hhalf] at hre
  have hb := mul_le_mul_of_nonneg_left hbase (pow_nonneg hα.le (n+2))
  have hp : 0 < α^(n+2)*β := mul_pos (pow_pos hα _) hβ
  linarith [(abs_le.mp hre).1]

#print axioms counting_difference
#print axioms masked_pattern_uniformity_lower
end Erdos3MaskedUniformityCounting
