import Submission.PhaseUnionBennett
import Submission.CoreFilteredDeletion

/-! Exact first-moment resampling and a Markov version of the low-count
cylinder bound. These are conditional criteria, not a quadratic gap bound. -/
namespace Erdos970.Resampling
open Finset Real Erdos970.GapAverages

lemma populationSurvivors_mean (S P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    phaseMean P (fun r => ((populationSurvivors S P r).card : ℝ)) =
      (S.card : ℝ) * density P := by
  simp_rw [populationSurvivors_card]
  rw [phaseMean_sum]
  simp only [phaseMean_point P hP, sum_const, nsmul_eq_mul]

lemma populationLowCountFraction_nonneg (S P : Finset ℕ) (b : ℝ) :
    0 ≤ populationLowCountFraction S P b := by
  unfold populationLowCountFraction phaseMean
  apply div_nonneg _ (by positivity)
  apply sum_nonneg
  intro r hr
  split_ifs <;> norm_num

/-- Uniform tail resampling has the exact mean |S|*density(P). Markov's
inequality gives a positive low-count fraction whenever b exceeds this mean. -/
theorem populationLowCountFraction_markov_lower (S P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℝ) (hb : 0 < b) :
    1 - (S.card : ℝ) * density P / b ≤ populationLowCountFraction S P b := by
  have hp (r : Phase P) :
      b * (1 - if ((populationSurvivors S P r).card : ℝ) ≤ b then 1 else 0) ≤
        ((populationSurvivors S P r).card : ℝ) := by
    split_ifs with hr
    · simpa using Nat.cast_nonneg (α := ℝ) (populationSurvivors S P r).card
    · simpa using (le_of_lt (not_le.mp hr))
  have hh := phaseMean_mono P hp
  rw [phaseMean_mul, phaseMean_sub, phaseMean_const P hP,
    populationSurvivors_mean S P hP] at hh
  change b * (1 - populationLowCountFraction S P b) ≤ _ at hh
  have hd : 1 - populationLowCountFraction S P b ≤ (S.card : ℝ) * density P / b :=
    (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hh)
  linarith

end Erdos970.Resampling

namespace Erdos970.GapAverages
open Finset Real Erdos970.Resampling

lemma single_phase_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : Phase P → ℝ) (hf : ∀ r, 0 ≤ f r) (r : Phase P) :
    f r * (∏ p ∈ P, (p : ℝ)⁻¹) ≤ phaseMean P f := by
  have hh := single_le_sum (s := (univ : Finset (Phase P)))
    (f := f) (fun s _ => hf s) (mem_univ r)
  have hd : (0 : ℝ) < ∏ p : P, (p.val : ℝ) := prod_pos
    (fun p _ => by exact_mod_cast (hP p.val p.property).pos)
  have hp : (∏ p ∈ P, (p : ℝ)⁻¹) = (∏ p : P, (p.val : ℝ))⁻¹ := by
    rw [prod_coe_sort P (fun p : ℕ => (p : ℝ)), prod_inv_distrib]
  rw [hp, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hh hd.le

/-- A fixed core contributes a full tail distribution, rather than requiring
every phase in that cylinder to have small count. No cover premise is needed. -/
theorem lowCountFraction_union_markov_lower (Q R : Finset ℕ)
    (hdis : Disjoint Q R) (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ p ∈ R, p.Prime)
    (m : ℕ) (b : ℝ) (hb : 0 < b) (r : Phase Q) :
    (1 - intervalCount Q m r * density R / b) *
        (∏ q ∈ Q, (q : ℝ)⁻¹) ≤ lowCountFraction (Q ∪ R) m b := by
  rw [lowCountFraction_union Q R hdis]
  have hh := populationLowCountFraction_markov_lower
    (populationSurvivors (range m) Q r) R hR b hb
  have hc : ((populationSurvivors (range m) Q r).card : ℝ) =
      intervalCount Q m r := populationSurvivors_card _ _ _
  rw [hc] at hh
  exact (mul_le_mul_of_nonneg_right hh (prod_nonneg (fun _ _ => by positivity))).trans
    (single_phase_lower Q hQ _
      (fun s => populationLowCountFraction_nonneg _ R b) r)

/-- A uniform upper bound on the core count may replace its exact value.
The density factor is preserved, unlike the whole-cylinder deletion bound. -/
theorem lowCountFraction_union_markov_lower_of_count_le (Q R : Finset ℕ)
    (hdis : Disjoint Q R) (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ p ∈ R, p.Prime)
    (m : ℕ) (b D : ℝ) (hb : 0 < b) (r : Phase Q)
    (hD : intervalCount Q m r ≤ D) :
    (1 - D * density R / b) * (∏ q ∈ Q, (q : ℝ)⁻¹) ≤
      lowCountFraction (Q ∪ R) m b := by
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hD (density_pos R hR).le) hb.le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hh 1)
    (prod_nonneg (fun _ _ => by positivity))).trans
    (lowCountFraction_union_markov_lower Q R hdis hQ hR m b hb r)

/-- The same estimate for a retained subset of the original prime set. -/
theorem lowCountFraction_markov_lower_of_core (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (b : ℝ) (hb : 0 < b) (r : Phase P) :
    (1 - intervalCount Q m (corePhase P Q hQP r) * density (P \ Q) / b) *
        (∏ q ∈ Q, (q : ℝ)⁻¹) ≤ lowCountFraction P m b := by
  have hh := lowCountFraction_union_markov_lower Q (P \ Q)
    (Finset.disjoint_left.mpr (fun q hq hqR => (Finset.mem_sdiff.mp hqR).2 hq))
    (fun q hq => hP q (hQP hq))
    (fun p hp => hP p (Finset.mem_sdiff.mp hp).1)
    m b hb (corePhase P Q hQP r)
  simpa only [union_sdiff_of_subset hQP] using hh

/-- A covered phase yields a Markov-cylinder lower bound with the old
core-filtered deletion budget discounted by the density of the freed tail. -/
theorem lowCountFraction_markov_lower_filtered (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (b D : ℝ) (hb : 0 < b)
    (r : Phase P) (hr : intervalCount P m r = 0)
    (hD : filteredDeletionBudget P Q hQP m r ≤ D) :
    (1 - D * density (P \ Q) / b) * (∏ q ∈ Q, (q : ℝ)⁻¹) ≤
      lowCountFraction P m b := by
  have hc := (core_count_le_filteredDeletionBudget P Q hQP m r hr).trans hD
  have hd : 0 ≤ density (P \ Q) := (density_pos _
    (fun p hp => hP p (Finset.mem_sdiff.mp hp).1)).le
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) hb.le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hh 1)
    (prod_nonneg (fun _ _ => by positivity))).trans
    (lowCountFraction_markov_lower_of_core P Q hQP hP m b hb r)

#print axioms lowCountFraction_markov_lower_of_core
#print axioms lowCountFraction_markov_lower_filtered
#print axioms Erdos970.Resampling.populationSurvivors_mean
#print axioms Erdos970.Resampling.populationLowCountFraction_markov_lower
#print axioms lowCountFraction_union_markov_lower
#print axioms lowCountFraction_union_markov_lower_of_count_le
end Erdos970.GapAverages
