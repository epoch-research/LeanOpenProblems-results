import FormalConjecturesUtil

/-! Positive uniform lower bounds for finite products with summable deficits. -/
namespace Erdos1206.PositiveLocalProducts
open Finset
open scoped Classical

/-- Positive local factors with a summable deficit have a uniform positive
lower bound over all finite products. -/
theorem uniform_product_lower {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 < f i ∧ f i ≤ 1)
    (hs : Summable (fun i => 1-f i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏i∈S,f i := by
  have hl : Summable (fun i => Real.log (f i)) := by
    have hh := Real.summable_log_one_add_of_summable hs.neg
    apply hh.congr
    intro i
    congr 1
    ring
  have hnon (i : ι) : 0 ≤ -Real.log (f i) := by
    exact neg_nonneg.mpr (Real.log_nonpos (hf i).1.le (hf i).2)
  refine ⟨Real.exp (-(∑' i,-Real.log (f i))),Real.exp_pos _,fun S => ?_⟩
  have hsum := Summable.sum_le_tsum S (fun i _ => hnon i) hl.neg
  have hh := Real.exp_le_exp.mpr (neg_le_neg hsum)
  have he : Real.exp (-(∑i∈S,-Real.log (f i)))=∏i∈S,f i := by
    simp only [sum_neg_distrib,neg_neg,Real.exp_sum]
    exact prod_congr rfl (fun i _ => Real.exp_log (hf i).1)
  rwa [he] at hh

#print axioms uniform_product_lower
end Erdos1206.PositiveLocalProducts
