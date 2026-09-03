import Submission.ExceptionalPairDeletionExplore
import Submission.RealWeightedCharacterEnergyExplore
import Submission.AffineRootAggregateExplore

/-! Deleting points changes a signed convolution by at most the lost
unsigned representations. In particular the codegree deletion bound also
controls the character-signed profile. -/
namespace Erdos66SignedProfileDeletion
open AdditiveCombinatorics Erdos66ExceptionalPairDeletion Erdos66SharedParameterKernel
  Erdos66AffineRootAggregate Erdos66RealWeightedCharacterEnergy
open scoped Classical
set_option maxHeartbeats 1800000

lemma signed_pair_loss (D E : Finset ℕ) (hED : E ⊆ D) (σ : ℕ → ℝ)
    (hσ : ∀ i, |σ i| ≤ 1) (i j : ℕ) :
    |(selectedWeight D i*σ i)*(selectedWeight D j*σ j)-
      (selectedWeight E i*σ i)*(selectedWeight E j*σ j)| ≤
      selectedWeight D i*selectedWeight D j-selectedWeight E i*selectedWeight E j := by
  have hsi : |σ i*σ j| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hσ i) (hσ j) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  by_cases hiE : i∈E <;> by_cases hjE : j∈E <;>
    by_cases hiD : i∈D <;> by_cases hjD : j∈D
  all_goals try exact False.elim (hiD (hED hiE))
  all_goals try exact False.elim (hjD (hED hjE))
  all_goals simp only [selectedWeight,hiE,hjE,hiD,hjD,if_true,if_false,one_mul,zero_mul,
    mul_zero,sub_self,sub_zero,abs_zero] at *
  all_goals first | exact hsi | norm_num

lemma signed_fiber_loss (D E : Finset ℕ) (hED : E ⊆ D) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (σ : ℕ → ℝ) (hσ : ∀ i, |σ i| ≤ 1) :
    |labelFiber h (fun i ↦ selectedWeight D i*σ i) q-
      labelFiber h (fun i ↦ selectedWeight E i*σ i) q| ≤
        (sumRep (D : Set ℕ) q : ℝ)-(sumRep (E : Set ℕ) q : ℝ) := by
  rw [←selectedWeight_fiber_eq_sumRep D h q hD,←selectedWeight_fiber_eq_sumRep E h q (hED.trans hD)]
  unfold labelFiber
  simp_rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i+j=q
  · simp only [hij,if_true]
    exact signed_pair_loss D E hED σ hσ i j
  · simp [hij]

lemma signed_kept_loss (p : ℕ) [Fact p.Prime] (D T : Finset ℕ) (h R q : ℕ)
    (hD : D ⊆ Finset.range h) (a : ZMod p) (hq : q∉T)
    (hR : ∀ b∈T, b≠q → codegree D b q ≤ R) :
    |signedFiber h (selectedWeight D) a q-signedFiber h (selectedWeight (kept D T)) a q| ≤
      2*(T.card : ℝ)*R := by
  have hm : sumRep (kept D T : Set ℕ) q ≤ sumRep (D : Set ℕ) q :=
    by
      classical
      simp only [sumRep_def]
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1,kept_subset D T hx.2.1,kept_subset D T hx.2.2⟩
  have hl : (sumRep (D : Set ℕ) q : ℝ)-(sumRep (kept D T : Set ℕ) q : ℝ) ≤ 2*(T.card : ℝ)*R := by
    have hh := representation_loss_le D T R q hq hR
    exact_mod_cast hh
  have hσ (i : ℕ) : |(quadraticChar (ZMod p) (a+(i : ZMod p)) : ℝ)| ≤ 1 := by
    have hh := Erdos66FiniteField.quadraticChar_abs_le_one (a+(i : ZMod p))
    exact_mod_cast hh
  exact (signed_fiber_loss D (kept D T) (kept_subset D T) h q hD _ hσ).trans hl

end Erdos66SignedProfileDeletion
