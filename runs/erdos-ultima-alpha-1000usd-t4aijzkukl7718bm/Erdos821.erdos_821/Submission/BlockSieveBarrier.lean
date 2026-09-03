import Submission.BlockSieveBudget
import Submission.FlexibleSieveBudget

/-!
# Limits of the blockwise sufficient criterion

These are method limitations. They are neither upper bounds on g nor a
disproof of the Erdős conjecture.
-/
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

/-- A necessary normalized inequality for successful blockwise parameters. -/
def BlockRetentionBudget (δ β κ : ℝ) : Prop :=
  0 ≤ δ ∧ 0 ≤ β ∧ 0 ≤ κ ∧ δ+β+κ=1 ∧
    (8192/675 : ℝ)*κ ≤ chebyshevRatioConstant*β*(β+κ)

lemma BlockRetentionBudget.cofactor_le {δ β κ : ℝ}
    (h : BlockRetentionBudget δ β κ) :
    κ ≤ (248751/3276800 : ℝ)*β := by
  obtain ⟨hδ,hβ,hκ,hs,hc⟩ := h
  have hs1 : β+κ ≤ 1 := by linarith
  have hcu := mul_le_mul_of_nonneg_right chebyshevRatioConstant_lt_decimal.le
    (mul_nonneg hβ (add_nonneg hβ hκ))
  have hprod := mul_le_mul_of_nonneg_left hs1 hβ
  nlinarith only [hc,hcu,hprod]

lemma BlockRetentionBudget.modulus_level_required {δ β κ : ℝ}
    (h : BlockRetentionBudget δ β κ) :
    1-(3525551/3276800 : ℝ)*β ≤ δ := by
  have hk := h.cofactor_le
  have hs := h.2.2.2.1
  linarith only [hk,hs]

lemma BlockRetentionBudget.below_half_cutoff {δ β κ : ℝ}
    (h : BlockRetentionBudget δ β κ) (hδ : δ ≤ 1/2) :
    (48171/100000 : ℝ) < β := by
  obtain ⟨hδ0,hβ,hκ,hs,hc⟩ := h
  by_contra hn
  have hβB : β ≤ (48171/100000 : ℝ) := le_of_not_gt hn
  have hcu := mul_le_mul_of_nonneg_right chebyshevRatioConstant_lt_decimal.le
    (mul_nonneg hβ (add_nonneg hβ hκ))
  have hcross := mul_nonneg (sub_nonneg.mpr hβB) (add_nonneg hβ hκ)
  nlinarith only [hc,hcu,hcross,hβB,hδ,hs]

lemma block_parameters_retention_budget (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : blockMainLimit t b h < chebyshevRatioConstant) :
    BlockRetentionBudget ((r : ℝ)/t) ((b : ℝ)/t) ((h : ℝ)/t) := by
  have ht : (0 : ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hhR : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hden : 0 < (b : ℝ)*((b : ℝ)+h) := by positivity
  have hcoef : (8192/675 : ℝ)*(t : ℝ)*h <
      chebyshevRatioConstant*((b : ℝ)*((b : ℝ)+h)) := by
    apply (div_lt_iff₀ hden).mp
    apply lt_of_le_of_lt _ hc
    apply le_trans _ (telescoped_le_blockMainLimit t b h hb)
    apply div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by linarith : (0 : ℝ)<(b : ℝ)-1)
        (by linarith : (0 : ℝ)<(b : ℝ)+h-1))
    nlinarith only [hbR,hhR]
  have heqR : (r : ℝ)+b+h=t := by exact_mod_cast heq
  refine ⟨by positivity,by positivity,by positivity,?_,?_⟩
  · rw [← add_div,← add_div,heqR,div_self ht.ne']
  · have h := div_le_div_of_nonneg_right hcoef.le (sq_nonneg (t : ℝ))
    convert h using 1 <;> field_simp

/-- The block method exceeds the old 0.51767 method barrier, but its own
threshold is still below 0.51829. This says nothing against the conjecture. -/
theorem block_parameters_exponent_bound (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : blockMainLimit t b h < chebyshevRatioConstant) :
    1-(b : ℝ)/t < (51829/100000 : ℝ) := by
  have ht : (0 : ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hr : (r : ℝ)/t ≤ 1/2 := by
    apply (div_le_iff₀ ht).mpr
    have hrtR : 2*(r : ℝ)+1 ≤ t := by exact_mod_cast hrt
    linarith only [hrtR]
  have hcut := (block_parameters_retention_budget r t b h heq hrt hb hc).below_half_cutoff hr
  linarith only [hcut]

theorem BlockRetentionBudget.modulus_level_tends_to_one
    (δ β κ : ℕ → ℝ) (h : ∀ n, BlockRetentionBudget (δ n) (β n) (κ n))
    (hβ : Filter.Tendsto β Filter.atTop (nhds 0)) :
    Filter.Tendsto δ Filter.atTop (nhds 1) := by
  have hlow : Filter.Tendsto (fun n => 1-(3525551/3276800 : ℝ)*β n)
      Filter.atTop (nhds 1) := by
    simpa only [mul_zero,sub_zero] using (hβ.const_mul (3525551/3276800 : ℝ)).const_sub 1
  apply hlow.squeeze tendsto_const_nhds (fun n => (h n).modulus_level_required)
  intro n
  obtain ⟨_,hβ,hκ,hs,_⟩ := h n
  linarith only [hβ,hκ,hs]

end Erdos821
