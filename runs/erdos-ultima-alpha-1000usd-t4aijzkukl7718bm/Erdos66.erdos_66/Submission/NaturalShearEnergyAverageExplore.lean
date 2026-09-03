import Submission.WeightedShearEnergyExplore
import Submission.RowShearNaturalAverageExplore

/-! Uniform bounds for averaged actual lower-carry counts, conditional on
centered cyclic self-count errors of the two row sets. -/
namespace Erdos66NaturalShearEnergyAverage
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66FirstRowFixingShear Erdos66WeightedShearEnergy Erdos66RowShearNaturalAverage
  Erdos66IntegerBlock Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

lemma sum_prefix_indicator (t : ℕ) (ht : t < p) :
    (∑ x : ZMod p, if x.val ≤ t then (1 : ℝ) else 0) = (t+1 : ℕ) := by
  have hh := sum_zmod_range p (fun x ↦ if x.val ≤ t then (1 : ℕ) else 0)
  have he : (∑ x ∈ Finset.range p, if (x : ZMod p).val ≤ t then (1 : ℕ) else 0) = t+1 := by
    have hf : (Finset.range p).filter (fun x : ℕ ↦ (x : ZMod p).val ≤ t) = Finset.range (t+1) := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_range]
      constructor
      · rintro ⟨hx,h⟩
        rw [ZMod.val_natCast_of_lt hx] at h
        omega
      · intro hx
        have hxp : x < p := by omega
        exact ⟨hxp,by rw [ZMod.val_natCast_of_lt hxp]; omega⟩
    rw [← Finset.card_filter,hf,Finset.card_range]
  exact_mod_cast hh.trans he

/-- The mean is the exact lower-carry overlap (t+1)/p, and the squared
error of the shear average is at most the product of the self-errors. -/
theorem lower_average_error_sq (A B : Finset (ZMod p)) (y v : ZMod p)
    (hy : y ≠ 0) (hv : v ≠ 0) (hs : y+v ≠ 0) (t : ℕ) (ht : t < p)
    (a b E D : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hA : ∀ z : ZMod p, |(pairCount A A z : ℝ)-a| ≤ E)
    (hB : ∀ z : ZMod p, |(pairCount B B z : ℝ)-b| ≤ D) :
    ((∑ c : ZMod p, (lower p (shiftSet A (c*y)) (shiftSet B (c*v)) t : ℝ)) /
        (p : ℝ) -
      ((A.card : ℝ)*B.card/p * (t+1 : ℕ)) / (p : ℝ))^2 ≤ E*D := by
  have hh := normalized_weighted_row_shear_error_sq A B y v (t : ZMod p) hy hv hs
    (fun x ↦ if x.val ≤ t then 1 else 0) (fun z ↦ by dsimp only; split_ifs <;> norm_num)
    a b E D hE hD hA hB
  simp only [ZMod.card,sum_prefix_indicator p t ht] at hh
  simpa only [lower_weightedPair] using hh

/-- Only one row needs a small relative self-error: a bounded error for the
other row still gives a shrinking averaged carry error. -/
theorem lower_average_error_bound (A B : Finset (ZMod p)) (y v : ZMod p)
    (hy : y ≠ 0) (hv : v ≠ 0) (hs : y+v ≠ 0) (t : ℕ) (ht : t < p)
    (a b E D ε V : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hA : ∀ z : ZMod p, |(pairCount A A z : ℝ)-a| ≤ E)
    (hB : ∀ z : ZMod p, |(pairCount B B z : ℝ)-b| ≤ D)
    (hED : E*D ≤ (ε*V)^2) :
    |(∑ c : ZMod p, (lower p (shiftSet A (c*y)) (shiftSet B (c*v)) t : ℝ)) /
        (p : ℝ) -
      ((A.card : ℝ)*B.card/p * (t+1 : ℕ)) / (p : ℝ)| ≤ ε*V := by
  have hh := (lower_average_error_sq p A B y v hy hv hs t ht a b E D hE hD hA hB).trans hED
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hε hV)).mp (by simpa only [sq_abs] using hh)

end Erdos66NaturalShearEnergyAverage
