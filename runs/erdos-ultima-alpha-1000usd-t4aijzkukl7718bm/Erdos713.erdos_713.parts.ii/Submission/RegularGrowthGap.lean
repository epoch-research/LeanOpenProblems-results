import FormalConjecturesUtil
import Submission.RegularPowerGrowth
import Submission.PolarityLowerBound

/-! Regular irrational-growth C4-free families are far from being extremal.
This is a diagnostic and is not a disproof of the original conjecture. -/
open SimpleGraph Filter Asymptotics
open scoped Topology
namespace Erdos713RegularGrowthGap
set_option maxHeartbeats 1000000

/-- Every positive pure-power sequence with exponent below 3/2 is negligible
compared with the C4 extremal number at the same cofinal host orders. -/
lemma ratio_extremal_tendsto_zero {N E : ℕ → ℕ} {α c : ℝ}
    (hN : Tendsto N atTop atTop) (hα : α < 3 / 2) (hc : 0 < c)
    (hE : (fun i => (E i : ℝ)) ~[atTop] (fun i => c * (N i : ℝ) ^ α)) :
    Tendsto (fun i => (E i : ℝ) / (extremalNumber (N i) (cycleGraph 4) : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := hE.isBigO.exists_pos
  have hzero : Tendsto (fun i => (N i : ℝ) ^ (α - 3 / 2)) atTop (𝓝 0) := by
    simpa only [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hN)
  have hlim := hzero.const_mul (64 * C * c)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun i => div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)) ?_ hlim
  filter_upwards [hbound.bound, hN.eventually_ge_atTop 4] with i hi hNi
  have hNr : (0 : ℝ) < N i := by exact_mod_cast (show 0 < N i by omega)
  have he : (E i : ℝ) ≤ C * c * (N i : ℝ) ^ α := by
    simpa only [Real.norm_natCast, Real.norm_of_nonneg
      (mul_nonneg hc.le (Real.rpow_nonneg hNr.le α)), mul_assoc] using hi
  have hlo := Erdos713PolarityLowerBound.c4_lower_power (N i) hNi
  calc
    (E i : ℝ) / (extremalNumber (N i) (cycleGraph 4) : ℝ)
      ≤ (C * c * (N i : ℝ) ^ α) / ((N i : ℝ) ^ (3 / 2 : ℝ) / 64) :=
        div_le_div₀ (by positivity) he (by positivity) hlo
    _ = 64 * C * c * (N i : ℝ) ^ (α - 3 / 2) := by
      rw [Real.rpow_sub hNr]
      ring

open scoped Classical in
/-- The explicit irrational regular graph construction has vanishing, rather
than asymptotically optimal, relative edge count. -/
theorem exists_irrational_regular_family_with_gap :
    ∃ α : ℝ, 1 < α ∧ α < 3 / 2 ∧ Irrational α ∧
      ∃ N d : ℕ → ℕ, Tendsto N atTop atTop ∧ Tendsto d atTop atTop ∧
        ∃ G : ∀ i, SimpleGraph (Fin (N i)),
          (∀ i, (cycleGraph 4).Free (G i) ∧ ∀ v, (G i).degree v = d i) ∧
          (fun i => (Nat.card (G i).edgeSet : ℝ)) ~[atTop]
            (fun i => (1 / 2 : ℝ) * (N i : ℝ) ^ α) ∧
          (fun i => (d i : ℝ)) ~[atTop]
            (fun i => (N i : ℝ) ^ (α - 1)) ∧
          Tendsto (fun i => (Nat.card (G i).edgeSet : ℝ) /
            (extremalNumber (N i) (cycleGraph 4) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨α, hα, hαhi, hirr, N, d, hN, hd, G, hG, hE, hdeg⟩ :=
    Erdos713RegularPowerGrowth.exists_irrational_regular_family
  exact ⟨α, hα, hαhi, hirr, N, d, hN, hd, G, hG, hE, hdeg,
    ratio_extremal_tendsto_zero hN hαhi (by norm_num) hE⟩

#print axioms ratio_extremal_tendsto_zero
#print axioms exists_irrational_regular_family_with_gap
end Erdos713RegularGrowthGap
