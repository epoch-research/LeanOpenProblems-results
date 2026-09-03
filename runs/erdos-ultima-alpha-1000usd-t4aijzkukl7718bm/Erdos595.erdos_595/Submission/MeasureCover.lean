import Submission.NegativeInner
import Submission.QuarterGraph

/-!
The quarter-measure candidate cannot witness Erdős 595: every disjointness
graph of measurable positive-probability sets has a countable triangle-free
edge cover. No separability assumption is needed.
-/

open SimpleGraph Set MeasureTheory
open scoped ENNReal

namespace Erdos595MeasureCover

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def centered (A : Set Ω) (hA : MeasurableSet A) : Lp ℝ 2 μ :=
  indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) -
    μ.real A • indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)

theorem inner_centered (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℝ (centered μ A hA) (centered μ B hB) =
      μ.real (A ∩ B) - μ.real A * μ.real B := by
  simp only [centered, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
    inter_univ, univ_inter]
  simp only [probReal_univ]
  ring

/-- Positive-measure disjointness representations, even on arbitrarily large
nonseparable probability spaces, always give countable triangle-free covers. -/
theorem countable_cover_of_measurable_disjointness {V : Type*} (G : SimpleGraph V)
    (A : V → Set Ω) (hm : ∀ v, MeasurableSet (A v)) (hp : ∀ v, μ (A v) ≠ 0)
    (hd : ∀ u v, G.Adj u v → Disjoint (A u) (A v)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  apply Erdos595NegativeInner.countable_cover_of_negative_inner G
    (fun v => centered μ (A v) (hm v))
  intro u v huv
  rw [inner_centered, Set.disjoint_iff_inter_eq_empty.mp (hd u v huv)]
  simp only [measureReal_empty, zero_sub, neg_lt_zero]
  exact mul_pos (ENNReal.toReal_pos (hp u) (measure_ne_top μ _))
    (ENNReal.toReal_pos (hp v) (measure_ne_top μ _))

/-- In particular, every quarter graph is coverable. The ultrafilter and its
conull-set property play no role in this obstruction. -/
theorem quarterGraph_countable_cover (p : Ultrafilter Ω) :
    Erdos595Work.IsCountableUnionOfTriangleFree (Erdos595Quarter.quarterGraph μ p) := by
  apply countable_cover_of_measurable_disjointness μ _ Subtype.val
    (fun v => v.property.1) ?_ (fun _ _ h => h)
  intro v
  rw [v.property.2.1]
  exact ne_of_gt (by
    simpa only [one_div] using (ENNReal.inv_pos.mpr (show (4 : ℝ≥0∞) ≠ ∞ by simp)))

#print axioms countable_cover_of_measurable_disjointness
#print axioms quarterGraph_countable_cover

end Erdos595MeasureCover
