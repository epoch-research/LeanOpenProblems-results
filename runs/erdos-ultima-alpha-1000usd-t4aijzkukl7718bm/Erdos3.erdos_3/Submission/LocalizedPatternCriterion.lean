import Submission.StableLocalQuadraticFactor

/-! A precise bridge from global uniformity and local stable-window factor
counts to actual nontrivial configurations. Both error sources and the exact
diagonal term are present. This is a conditional counting criterion, not an
equidistribution theorem for the local phases. -/
namespace Erdos3LocalizedPatternCriterion
open Finset Erdos3StableWindowCounting Erdos3DifferenceStepCounting
  Erdos3FiniteUniformity Erdos3CorrelationSifting Erdos3UniformityCounting
  Erdos3RelativeStableBohr Erdos3FiniteBohr Erdos3BohrCovering
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {F : Type*} [Field F] [Fintype F]

noncomputable def differenceRealAverage {k : ℕ} (B : Finset F) (v : Fin k → F)
    (f : F → ℝ) : ℝ := 𝔼 b : B, 𝔼 c : B, 𝔼 x : F,
      ∏ i : Fin k, f (x+v i*((c : F)-b))

lemma differenceRealAverage_coe {k : ℕ} (B : Finset F) (v : Fin k → F) (f : F → ℝ) :
    (differenceRealAverage B v f : ℂ) = differenceAverage B v (fun _ x ↦ (f x : ℂ)) := by
  simp only [differenceRealAverage,differenceAverage,Complex.ofReal_expect,Complex.ofReal_prod]

lemma differenceRealAverage_product {k : ℕ} (B : Finset F) (v : Fin k → F) (f : F → ℝ) :
    differenceRealAverage B v f =
      𝔼 p : B × B, 𝔼 x : F, ∏ i : Fin k, f (x+v i*((p.2 : F)-p.1)) := by
  symm
  exact expect_product _ _ _

lemma real_difference_counting_bound (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (hv : Function.Injective v) (f g : F → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower (n+1) (fun x ↦ ((f x-g x : ℝ) : ℂ)) ≤ η^(2^(n+2))) :
    |differenceRealAverage B v f-differenceRealAverage B v g| ≤
      ((n+3 : ℕ)*η)/density B := by
  have hfc (x : F) : ‖(f x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hf x).1] using (hf x).2
  have hgc (x : F) : ‖(g x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x).1] using (hg x).2
  have hfg (x : F) : ‖(f x : ℂ)-(g x : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hf x).1,(hg x).2],by linarith [(hf x).2,(hg x).1]⟩
  have h := difference_counting_bound n B hB v hv (fun x ↦ (f x : ℂ))
    (fun x ↦ (g x : ℂ)) hfc hgc hfg hη (by simpa only [Complex.ofReal_sub] using hU)
  rw [← differenceRealAverage_coe,← differenceRealAverage_coe,← Complex.ofReal_sub] at h
  simpa only [Complex.norm_real,Real.norm_eq_abs] using h

/-- The global uniformity error costs 1/density(B); the local factor error
costs no inverse density. The two estimates concern different approximations. -/
theorem localized_counting_bridge (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (hv : Function.Injective v)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (f g : F → ℝ) (h : F → F → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hh : ∀ a x, 0 ≤ h a x ∧ h a x ≤ 1)
    {ε η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hU : uniformityPower (n+1) (fun x ↦ ((f x-g x : ℝ) : ℂ)) ≤ η^(2^(n+2)))
    (herr : ∀ a, (𝔼 t : bohr C r, (g (a+t)-h a t)^2) ≤ ε)
    (hbudget : ε+1/(z : ℝ) ≤ κ^2) :
    |differenceRealAverage B v f-
      (𝔼 a : F, windowPatternAverage (bohr C r)
        (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (h a))| ≤
      (n+3 : ℕ)*(η/density B+κ) := by
  letI : Nonempty B := hB.to_subtype
  have h₁ := real_difference_counting_bound n B hB v hv f g hf hg hη hU
  have h₂ := averaged_local_factor_counting_difference C hr hz hstable
    (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (fun p i ↦ hs p.1 p.2 i)
    g h hg hh hκ herr hbudget
  rw [← differenceRealAverage_product] at h₂
  simp only [Fintype.card_fin] at h₂
  calc
    _ ≤ |differenceRealAverage B v f-differenceRealAverage B v g|+
        |differenceRealAverage B v g-(𝔼 a : F, windowPatternAverage (bohr C r)
          (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (h a))| := abs_sub_le _ _ _
    _ ≤ ((n+3 : ℕ)*η)/density B+(n+3 : ℕ)*κ := add_le_add h₁ h₂
    _ = _ := by ring

/-- With difference steps c-b, the exact diagonal contribution is density(A)/|B|,
not density(A)/|F|. -/
lemma difference_diagonal_average {k : ℕ} (hk : 0 < k)
    (B : Finset F) (hB : B.Nonempty) (v : Fin k → F) (A : Finset F)
    (hdiag : ∀ x d : F, (∀ i : Fin k, x+v i*d ∈ A) → d = 0) :
    differenceRealAverage B v (indicator A) = density A/(B.card : ℝ) := by
  letI : Nonempty B := hB.to_subtype
  have he (b c : B) (x : F) : (∏ i : Fin k, indicator A (x+v i*((c : F)-b))) =
      if c = b then indicator A x else 0 := by
    by_cases hcb : c = b
    · subst c
      by_cases hx : x ∈ A <;> simp [indicator,hx,hk.ne']
    · have hex : ∃ i : Fin k, x+v i*((c : F)-b) ∉ A := by
        by_contra! h
        have hz := hdiag x ((c : F)-b) h
        exact hcb (Subtype.ext (sub_eq_zero.mp hz))
      obtain ⟨i,hi⟩ := hex
      rw [if_neg hcb]
      apply prod_eq_zero (mem_univ i)
      simp only [indicator,if_neg hi]
  unfold differenceRealAverage
  simp only [he]
  have hx (b c : B) : (𝔼 x : F, if c = b then indicator A x else 0) =
      if c = b then density A else 0 := by
    by_cases hcb : c = b <;> simp only [hcb,if_true,if_false,expect_indicator,Fintype.expect_const]
  simp only [hx]
  have hc (b : B) : (𝔼 c : B, if c = b then density A else 0) = density A/(B.card : ℝ) := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  simp only [hc,Fintype.expect_const]

/-- A sufficiently large actual local factor count, after both errors and the
diagonal are paid, forces a nontrivial configuration in A. -/
theorem exists_pattern_of_local_count (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (hv : Function.Injective v) (A : Finset F)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (g : F → ℝ) (h : F → F → ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hh : ∀ a x, 0 ≤ h a x ∧ h a x ≤ 1)
    {ε η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hU : uniformityPower (n+1) (fun x ↦ ((indicator A x-g x : ℝ) : ℂ)) ≤ η^(2^(n+2)))
    (herr : ∀ a, (𝔼 t : bohr C r, (g (a+t)-h a t)^2) ≤ ε)
    (hbudget : ε+1/(z : ℝ) ≤ κ^2)
    (hcount : (n+3 : ℕ)*(η/density B+κ)+density A/(B.card : ℝ) <
      𝔼 a : F, windowPatternAverage (bohr C r)
        (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (h a)) :
    ∃ x d : F, d ≠ 0 ∧ ∀ i : Fin (n+3), x+v i*d ∈ A := by
  have hbridge := localized_counting_bridge n B hB v hv C hr hz hstable hs
    (indicator A) g h (indicator_norm_bounds A) hg hh hη hκ hU herr hbudget
  by_contra! hno
  have hdiag : ∀ x d : F, (∀ i : Fin (n+3), x+v i*d ∈ A) → d = 0 := by
    intro x d hm
    by_contra hd
    obtain ⟨i,hi⟩ := hno x d hd
    exact hi (hm i)
  rw [difference_diagonal_average (by omega) B hB v A hdiag] at hbridge
  linarith [(abs_le.mp hbridge).1]

#print axioms localized_counting_bridge
#print axioms difference_diagonal_average
#print axioms exists_pattern_of_local_count
end Erdos3LocalizedPatternCriterion
