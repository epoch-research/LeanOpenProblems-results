import Submission.ChebyshevCompositeGain

/-!
# The modulus level required by the current retention budget

These are limitations of the sufficient conditions used in the structured
second sieve, not upper bounds on the actual inverse-totient multiplicities.
In particular they are not a disproof of Erdős 821.
-/

namespace Erdos821

/-- Normalized logarithmic parameters: prescribed modulus, smoothness cutoff,
remaining cofactor, and sieve length.  This records the current sufficient
coefficient budget only. -/
def RetentionBudget (δ β κ j : ℝ) : Prop :=
  0 ≤ β ∧ 0 ≤ j ∧ j ≤ β ∧ δ+β+κ = 1 ∧
    (8320/675 : ℝ)*κ ≤ (27/32 : ℝ)*j^2

lemma RetentionBudget.cofactor_le {δ β κ j : ℝ} (h : RetentionBudget δ β κ j) :
    κ ≤ (3645/53248 : ℝ)*β^2 := by
  obtain ⟨hβ,hj,hjβ,hsum,hcoef⟩ := h
  have hsq := pow_le_pow_left₀ hj hjβ 2
  nlinarith only [hcoef,hsq]

/-- Small target smoothness forces the prescribed modulus toward the full
prime scale, rather than keeping it below square root. -/
theorem RetentionBudget.modulus_level_required {δ β κ j : ℝ}
    (h : RetentionBudget δ β κ j) :
    1-β-(3645/53248 : ℝ)*β^2 ≤ δ := by
  have hk := h.cofactor_le
  have hsum := h.2.2.2.1
  linarith

/-- In particular, the existing rejection coefficient would need a modulus
level greater than 0.659 to reach cube-root smoothness. -/
theorem RetentionBudget.cube_root_requires_large_modulus {δ β κ j : ℝ}
    (h : RetentionBudget δ β κ j) (hβ : β ≤ 1/3) :
    (105281/159744 : ℝ) ≤ δ := by
  have hsq : β^2 ≤ (1/3 : ℝ)^2 := pow_le_pow_left₀ h.1 hβ 2
  have hd := h.modulus_level_required
  nlinarith only [hβ,hsq,hd]

/-- The present below-half retention conditions cannot even attain
smoothness ratio 0.4839. This says nothing about other methods. -/
theorem RetentionBudget.below_half_cutoff {δ β κ j : ℝ}
    (h : RetentionBudget δ β κ j) (hδ : δ ≤ 1/2) :
    (4839/10000 : ℝ) < β := by
  by_contra hn
  have hβ : β ≤ (4839/10000 : ℝ) := le_of_not_gt hn
  have hsq : β^2 ≤ (4839/10000 : ℝ)^2 := pow_le_pow_left₀ h.1 hβ 2
  have hd := h.modulus_level_required
  nlinarith only [hδ,hβ,hsq,hd]

lemma RetentionBudget.cube_root_not_below_half {δ β κ j : ℝ}
    (h : RetentionBudget δ β κ j) (hβ : β ≤ 1/3) : ¬δ ≤ 1/2 := by
  have hδ := h.cube_root_requires_large_modulus hβ
  linarith

/-- This specializes the normalized obstruction to the actual improved
Chebyshev parameter conditions, rather than the older 17/32 budget. -/
lemma chebyshev_parameters_retention_budget (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2) :
    RetentionBudget ((r : ℝ)/t) ((b : ℝ)/t) ((h : ℝ)/t) (((b : ℝ)-1)/t) := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have heqR : (r : ℝ)+b+h=t := by exact_mod_cast heq
  refine ⟨by positivity,div_nonneg (by linarith) ht.le,?_,?_,?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) ht.le
  · rw [← add_div,← add_div,heqR,div_self ht.ne']
  · have h := div_le_div_of_nonneg_right hc (sq_nonneg (t : ℝ))
    convert h using 1 <;> field_simp

lemma chebyshev_parameters_cutoff_bound (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2) :
    4839*t < 10000*b := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hr : (r : ℝ)/t ≤ 1/2 := by
    apply (div_le_iff₀ ht).mpr
    have hrtR : 2*(r : ℝ)+1 ≤ t := by exact_mod_cast hrt
    linarith
  have hcut := (chebyshev_parameters_retention_budget r t b h heq hrt hb hc).below_half_cutoff hr
  have hcross := (lt_div_iff₀ ht).mp hcut
  have hR : (4839 : ℝ)*t < 10000*b := by linarith only [hcross]
  exact_mod_cast hR

/-- Thresholds furnished by this precise sufficient-condition family stay
below 0.5161, including after the stronger Mangoldt input. -/
theorem chebyshev_parameters_exponent_bound (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2) :
    1-(b : ℝ)/t < (5161/10000 : ℝ) := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hcR : (4839 : ℝ)*t < 10000*b := by
    exact_mod_cast chebyshev_parameters_cutoff_bound r t b h heq hrt hb hc
  have hdiv : (4839/10000 : ℝ) < (b : ℝ)/t :=
    (lt_div_iff₀ ht).mpr (by linarith only [hcR])
  linarith only [hdiv]

/-- A cofinal sequence of smoothness cutoffs would require cofinal modulus
levels in this budget, not repeated use of a fixed below-half estimate. -/
theorem RetentionBudget.modulus_level_tends_to_one
    (δ β κ j : ℕ → ℝ) (h : ∀ n, RetentionBudget (δ n) (β n) (κ n) (j n))
    (hδ : ∀ n, δ n ≤ 1)
    (hβ : Filter.Tendsto β Filter.atTop (nhds 0)) :
    Filter.Tendsto δ Filter.atTop (nhds 1) := by
  have hlow : Filter.Tendsto (fun n => 1-β n-(3645/53248 : ℝ)*(β n)^2)
      Filter.atTop (nhds 1) := by
    have ht := (hβ.const_sub 1).sub ((hβ.pow 2).const_mul (3645/53248 : ℝ))
    simpa only [sub_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] using ht
  exact hlow.squeeze tendsto_const_nhds (fun n => (h n).modulus_level_required) hδ

end Erdos821
