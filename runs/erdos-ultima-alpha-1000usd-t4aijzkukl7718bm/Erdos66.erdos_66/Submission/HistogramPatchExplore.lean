import Submission.AnchoredGraphColorTransferExplore

/-! Total-variation and squared-energy bounds for finite histogram changes. -/
namespace Erdos66HistogramPatch
open scoped Classical
set_option maxHeartbeats 2000000

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def histogram (f : ι → κ) (q : κ) : ℝ :=
  ∑ x : ι, if f x=q then 1 else 0

lemma histogram_change_L1 (f g : ι → κ) (T : Finset ι) (hfg : ∀ x, x∉T → f x=g x) :
    (∑ q : κ, |histogram f q-histogram g q|)≤2*(T.card:ℝ) := by
  have hpoint (x : ι) : (∑ q : κ,
      |(if f x=q then (1:ℝ) else 0)-(if g x=q then 1 else 0)|)≤
      if x∈T then 2 else 0 := by
    by_cases hx : x∈T
    · rw [if_pos hx]
      calc
        _ ≤ ∑ q : κ, (|(if f x=q then (1:ℝ) else 0)|+|(if g x=q then (1:ℝ) else 0)|) :=
          Finset.sum_le_sum (fun q hq ↦ abs_sub _ _)
        _ = 2 := by
          have habs (a q : κ) :
              |(if a=q then (1:ℝ) else 0)| = if a=q then 1 else 0 := by
            by_cases h : a=q <;> simp [h]
          simp_rw [habs]
          norm_num [Finset.sum_add_distrib]
    · simp only [hfg x hx,sub_self,abs_zero,Finset.sum_const_zero,hx,if_false,le_refl]
  unfold histogram
  simp only [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q : κ, ∑ x : ι,
        |(if f x=q then (1:ℝ) else 0)-(if g x=q then 1 else 0)| :=
      Finset.sum_le_sum (fun q hq ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ x : ι, ∑ q : κ,
        |(if f x=q then (1:ℝ) else 0)-(if g x=q then 1 else 0)| := Finset.sum_comm
    _ ≤ ∑ x : ι, if x∈T then (2:ℝ) else 0 := Finset.sum_le_sum (fun x hx ↦ hpoint x)
    _ = 2*(T.card:ℝ) := by rw [←Finset.sum_filter]; simp [mul_comm]

lemma histogram_change_L2 (f g : ι → κ) (T : Finset ι) (hfg : ∀ x, x∉T → f x=g x) :
    (∑ q : κ, (histogram f q-histogram g q)^2)≤4*(T.card:ℝ)^2 := by
  have he := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun q hq ↦ abs_nonneg (histogram f q-histogram g q))
  simp only [sq_abs] at he
  have hL1 := histogram_change_L1 f g T hfg
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun q hq ↦ abs_nonneg _)) hL1 2
  nlinarith only [he,hsq]

end Erdos66HistogramPatch
