import Submission.LinearFormsUniformity
import Submission.CorrelationSifting

/-! A counting lemma for nonnegative bounded functions along distinct slopes. -/
namespace Erdos3UniformityCounting
open Finset Erdos3LinearFormsUniformity Erdos3FiniteUniformity Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3500000
variable {F : Type*} [Field F] [Fintype F]

noncomputable def replace {k : ℕ} (f : Fin k → F → ℂ) (i : Fin k) (g : F → ℂ) : Fin k → F → ℂ :=
  fun j ↦ if j = i then g else f j

lemma linearAverage_replace_sub {k : ℕ} (v : Fin (k+1) → F) (f g : Fin (k+1) → F → ℂ)
    (i : Fin (k+1)) (hoff : ∀ j, j ≠ i → f j = g j) :
    linearAverage v f-linearAverage v g =
      linearAverage v (replace g i (fun x ↦ f i x-g i x)) := by
  unfold linearAverage
  rw [← expect_sub_distrib]
  apply expect_congr rfl
  intro x _
  rw [← expect_sub_distrib]
  apply expect_congr rfl
  intro d _
  rw [Fin.prod_univ_succAbove (fun j ↦ f j (x+v j*d)) i,
    Fin.prod_univ_succAbove (fun j ↦ g j (x+v j*d)) i,
    Fin.prod_univ_succAbove (fun j ↦ replace g i (fun x ↦ f i x-g i x) j (x+v j*d)) i]
  have he (j : Fin k) : f (i.succAbove j) = g (i.succAbove j) := hoff _ (Fin.succAbove_ne i j)
  simp only [replace,if_true,if_neg (Fin.succAbove_ne i _),he]
  ring

noncomputable def blend {k : ℕ} (f g : F → ℂ) (j : ℕ) : Fin k → F → ℂ :=
  fun i ↦ if (i : ℕ) < j then f else g

lemma blend_zero {k : ℕ} (f g : F → ℂ) : blend (k := k) f g 0 = fun _ ↦ g := by
  funext i
  simp [blend]
lemma blend_full {k : ℕ} (f g : F → ℂ) : blend (k := k) f g k = fun _ ↦ f := by
  funext i
  simp only [blend,if_pos i.isLt]

lemma blend_step {k : ℕ} (v : Fin (k+1) → F) (f g : F → ℂ) {j : ℕ} (hj : j < k+1) :
    linearAverage v (blend f g (j+1))-linearAverage v (blend f g j) =
      linearAverage v (replace (blend f g j) ⟨j,hj⟩ (fun x ↦ f x-g x)) := by
  have he := linearAverage_replace_sub v (blend f g (j+1)) (blend f g j) ⟨j,hj⟩ (by
    intro i hi
    have hne : (i : ℕ) ≠ j := by intro hh; apply hi; exact Fin.ext hh
    have hh : (i : ℕ) < j+1 ↔ (i : ℕ) < j := by omega
    simp only [blend,hh])
  simpa only [blend,show j < j+1 by omega,if_true,lt_self_iff_false,if_false] using he

/-- A bounded centered function with small U^(n+1) gives the expected count
for any n+2 distinct slopes. -/
theorem counting_lemma (n : ℕ) (v : Fin (n+2) → F) (hv : Function.Injective v)
    (f : F → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {α η : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hη : 0 ≤ η)
    (hU : uniformityPower n (fun x ↦ ((f x-α : ℝ) : ℂ)) ≤ η^(2^(n+1))) :
    ‖linearAverage v (fun _ x ↦ (f x : ℂ))-(α : ℂ)^(n+2)‖ ≤ (n+2 : ℕ)*η := by
  let fC : F → ℂ := fun x ↦ (f x : ℂ)
  let gC : F → ℂ := fun _ ↦ (α : ℂ)
  let H : ℕ → ℂ := fun j ↦ linearAverage v (blend fC gC j)
  have hcf (x : F) : ‖fC x‖ ≤ 1 := by
    simpa only [fC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hf x).1] using (hf x).2
  have hcg (x : F) : ‖gC x‖ ≤ 1 := by
    simpa only [gC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hα] using hα1
  have hcdiff (x : F) : ‖fC x-gC x‖ ≤ 1 := by
    rw [show fC x-gC x = ((f x-α : ℝ) : ℂ) by simp [fC,gC]]
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hf x).1],by linarith [(hf x).2]⟩
  have hstep (j : ℕ) (hj : j < n+2) : ‖H (j+1)-H j‖ ≤ η := by
    let i : Fin (n+2) := ⟨j,hj⟩
    let f' := replace (blend fC gC j) i (fun x ↦ fC x-gC x)
    have hf' (s : Fin (n+2)) (x : F) : ‖f' s x‖ ≤ 1 := by
      dsimp [f',replace,blend]
      split_ifs <;> first | exact hcdiff x | exact hcf x | exact hcg x
    have hh := distinct_slopes_bound n v hv f' hf' i
    have he : f' i = fun x ↦ ((f x-α : ℝ) : ℂ) := by
      funext x
      simp only [f',replace,if_true,fC,gC,Complex.ofReal_sub]
    rw [he] at hh
    have hpow := hh.trans hU
    have hnorm := le_of_pow_le_pow_left₀ (by positivity : 2^(n+1) ≠ 0) hη hpow
    simpa only [H,blend_step v fC gC hj,f',i] using hnorm
  have hzero : H 0 = (α : ℂ)^(n+2) := by
    dsimp [H]
    rw [blend_zero]
    simp only [linearAverage,gC,prod_const,card_univ,Fintype.card_fin,Fintype.expect_const]
  have hfull : H (n+2) = linearAverage v (fun _ x ↦ (f x : ℂ)) := by
    dsimp [H]
    rw [blend_full]
  rw [← hfull,← hzero,← sum_range_sub H (n+2)]
  calc
    _ ≤ ∑ j ∈ range (n+2), ‖H (j+1)-H j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (n+2), η := sum_le_sum (fun j hj ↦ hstep j (mem_range.mp hj))
    _ = _ := by simp

lemma indicator_norm_bounds (A : Finset F) (x : F) : 0 ≤ indicator A x ∧ indicator A x ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

/-- If all configurations of a nonempty family of slopes are diagonal, the
configuration average is exactly density(A)/|F|. -/
lemma indicator_diagonal_average {k : ℕ} (hk : 0 < k)
    (v : Fin k → F) (A : Finset F)
    (hdiag : ∀ x d : F, (∀ i : Fin k, x+v i*d ∈ A) → d = 0) :
    linearAverage v (fun _ x ↦ (indicator A x : ℂ)) =
      (density A : ℂ)/(Fintype.card F : ℂ) := by
  have he (x d : F) : (∏ i : Fin k, (indicator A (x+v i*d) : ℂ)) =
      if d = 0 then (indicator A x : ℂ) else 0 := by
    by_cases hd : d = 0
    · subst d
      by_cases hx : x ∈ A <;> simp [indicator,hx,hk.ne']
    · have hex : ∃ i : Fin k, x+v i*d ∉ A := by
        by_contra! hn
        exact hd (hdiag x d hn)
      obtain ⟨i,hi⟩ := hex
      rw [if_neg hd]
      apply prod_eq_zero (mem_univ i)
      simp [indicator,hi]
  unfold linearAverage
  simp_rw [he]
  have hd (x : F) : (𝔼 d : F, if d = 0 then (indicator A x : ℂ) else 0) =
      (indicator A x : ℂ)/(Fintype.card F : ℂ) := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  simp_rw [hd]
  rw [← expect_div]
  congr 1
  have hc : ((𝔼 x : F, indicator A x : ℝ) : ℂ) = 𝔼 x : F, (indicator A x : ℂ) :=
    map_expect ((algebraMap ℝ ℂ).toRatAlgHom.toLinearMap.restrictScalars ℚ≥0) _ univ
  rw [← hc,expect_indicator]

/-- Small relative higher-order uniformity forces a nontrivial configuration.
For consecutive distinct slopes this is an AP counting criterion. -/
theorem exists_pattern_of_uniformity_small (n : ℕ) (v : Fin (n+2) → F)
    (hv : Function.Injective v) (A : Finset F) (hA : A.Nonempty)
    (hsize : 4 ≤ (density A)^(n+1)*(Fintype.card F : ℝ))
    (hU : uniformityPower n (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)) ≤
      ((density A)^(n+2)/(2*(n+2 : ℕ)))^(2^(n+1))) :
    ∃ x d : F, d ≠ 0 ∧ ∀ i : Fin (n+2), x+v i*d ∈ A := by
  have hα := density_pos A hA
  have hα1 : density A ≤ 1 := by
    unfold density
    apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card F)).mpr
    exact_mod_cast card_le_univ A
  have hcount := counting_lemma n v hv (indicator A) (indicator_norm_bounds A) hα.le hα1
    (by positivity : 0 ≤ (density A)^(n+2)/(2*(n+2 : ℕ))) hU
  by_contra! hno
  have hdiag : ∀ x d : F, (∀ i : Fin (n+2), x+v i*d ∈ A) → d = 0 := by
    intro x d hm
    by_contra hd
    obtain ⟨i,hi⟩ := hno x d hd
    exact hi (hm i)
  rw [indicator_diagonal_average (by omega : 0 < n+2) v A hdiag] at hcount
  have he : (density A : ℂ)/(Fintype.card F : ℂ)-(density A : ℂ)^(n+2) =
      ((density A/(Fintype.card F : ℝ)-(density A)^(n+2) : ℝ) : ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs] at hcount
  have hG : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < n+2 := by positivity
  have hhalf : ((n+2 : ℕ) : ℝ)*((density A)^(n+2)/(2*(n+2 : ℕ))) = (density A)^(n+2)/2 := by
    push_cast
    field_simp
  rw [hhalf] at hcount
  have hdiagSmall : density A/(Fintype.card F : ℝ) ≤ (density A)^(n+2)/4 := by
    apply (div_le_iff₀ hG).mpr
    rw [show n+2 = (n+1)+1 by omega,pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hsize hα.le]
  have hp : 0 < (density A)^(n+2) := pow_pos hα _
  linarith [(abs_le.mp hcount).1]

/-- Consequently, a large pattern-free set must have a substantial centered
higher-order uniformity power. Obtaining a sufficiently efficient structural
increment from this alternative is not proved here. -/
theorem pattern_free_uniformity_lower (n : ℕ) (v : Fin (n+2) → F)
    (hv : Function.Injective v) (A : Finset F) (hA : A.Nonempty)
    (hsize : 4 ≤ (density A)^(n+1)*(Fintype.card F : ℝ))
    (hdiag : ∀ x d : F, (∀ i : Fin (n+2), x+v i*d ∈ A) → d = 0) :
    ((density A)^(n+2)/(2*(n+2 : ℕ)))^(2^(n+1)) <
      uniformityPower n (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)) := by
  apply lt_of_not_ge
  intro hU
  obtain ⟨x,d,hd,hpat⟩ := exists_pattern_of_uniformity_small n v hv A hA hsize hU
  exact hd (hdiag x d hpat)

#print axioms pattern_free_uniformity_lower

#print axioms counting_lemma
#print axioms exists_pattern_of_uniformity_small
end Erdos3UniformityCounting
