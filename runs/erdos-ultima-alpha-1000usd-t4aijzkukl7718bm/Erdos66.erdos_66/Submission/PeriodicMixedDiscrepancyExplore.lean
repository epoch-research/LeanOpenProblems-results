import Submission.PhasedResidueCountingExplore
import Submission.NatPairAlgebraExplore

/-! Mixed natural counts against a clipped periodic template, controlled by
residue histograms. This does not supply a logarithmically small error. -/
namespace Erdos66PeriodicMixedDiscrepancy
open Erdos66Counting Erdos66ResidueCounting Erdos66NatPairAlgebra
  Erdos66PhasedResidueCounting
open scoped Classical
set_option maxHeartbeats 1800000

variable (M : ℕ) [NeZero M]

noncomputable def hist (S : Finset ℕ) (z : ZMod M) : ℕ :=
  (S.filter (fun (a : ℕ) ↦ (a:ZMod M)=z)).card

noncomputable def periodicSlice (D : Finset (ZMod M)) (L U : ℕ) : Finset ℕ :=
  (Finset.Ico L U).filter (fun (b : ℕ) ↦ (b:ZMod M)∈D)

lemma reflected_hist (S : Finset ℕ) (n : ℕ) (z : ZMod M) :
    (S.filter (fun (a : ℕ) ↦ (n:ZMod M)-(a:ZMod M)=z)).card=hist M S ((n:ZMod M)-z) := by
  congr 1
  ext a
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor <;> intro h <;> linear_combination -h

/-- All endpoints in S are eligible for the displayed periodic interval.
The formula counts actual natural pairs, not just congruences. -/
lemma pairs_periodicSlice (S : Finset ℕ) (D : Finset (ZMod M)) (L U n : ℕ)
    (hS : ∀ a∈S, a≤n ∧ L≤n-a ∧ n-a<U) :
    pairs S (periodicSlice M D L U) n=∑ z∈D, hist M S ((n:ZMod M)-z) := by
  rw [pairs_eq_filter]
  have he : S.filter (fun (a : ℕ) ↦ a≤n ∧ n-a∈periodicSlice M D L U)=
      S.filter (fun (a : ℕ) ↦ (n:ZMod M)-(a:ZMod M)∈D) := by
    apply Finset.filter_congr
    intro a ha
    obtain ⟨han,haL,haU⟩ := hS a ha
    simp [periodicSlice,han,haL,haU,Nat.cast_sub han]
  rw [he,←Finset.sum_card_fiberwise_eq_card_filter S D]
  apply Finset.sum_congr rfl
  intro z hz
  exact reflected_hist M S n z

lemma pairs_periodicSlice_error (S : Finset ℕ) (D : Finset (ZMod M)) (L U n : ℕ)
    (hS : ∀ a∈S, a≤n ∧ L≤n-a ∧ n-a<U) (E : ℝ)
    (hE : ∀ z, |(hist M S z:ℝ)-(S.card:ℝ)/M|≤E) :
    |(pairs S (periodicSlice M D L U) n:ℝ)-(S.card:ℝ)*D.card/M|≤E*D.card := by
  rw [pairs_periodicSlice M S D L U n hS,Nat.cast_sum]
  have hm : (S.card:ℝ)*D.card/M=∑ _z∈D, (S.card:ℝ)/M := by simp; ring
  rw [hm,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z∈D, |(hist M S ((n:ZMod M)-z):ℝ)-(S.card:ℝ)/M| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z∈D, E := Finset.sum_le_sum (fun z _ ↦ hE _)
    _ = _ := by simp; ring

noncomputable def intervalPoints (A : Set ℕ) (u v : ℕ) : Finset ℕ :=
  cutoff A v \ cutoff A u

lemma cutoff_subset_of_le (A : Set ℕ) {u v : ℕ} (huv : u≤v) : cutoff A u⊆cutoff A v := by
  intro a ha
  obtain ⟨hau,haA⟩ := mem_cutoff.mp ha
  exact mem_cutoff.mpr ⟨hau.trans_le huv,haA⟩

lemma interval_card_real (A : Set ℕ) (u v : ℕ) (huv : u≤v) :
    ((intervalPoints A u v).card:ℝ)=(count A v:ℝ)-count A u := by
  rw [intervalPoints,Finset.card_sdiff_of_subset (cutoff_subset_of_le A huv)]
  exact Nat.cast_sub (Finset.card_le_card (cutoff_subset_of_le A huv))

lemma interval_hist_real (A : Set ℕ) (u v : ℕ) (huv : u≤v) (z : ZMod M) :
    (hist M (intervalPoints A u v) z:ℝ)=
      (count (residueSet M A z) v:ℝ)-count (residueSet M A z) u := by
  have he : (intervalPoints A u v).filter (fun (a : ℕ) ↦ (a:ZMod M)=z)=
      intervalPoints (residueSet M A z) u v := by
    ext a
    simp only [intervalPoints,Finset.mem_filter,Finset.mem_sdiff,mem_cutoff,
      residueSet,Set.mem_setOf_eq]
    tauto
  change (((intervalPoints A u v).filter (fun (a : ℕ) ↦ (a:ZMod M)=z)).card:ℝ)=_
  rw [he]
  exact interval_card_real (residueSet M A z) u v huv

lemma interval_hist_error (A : Set ℕ) (u v : ℕ) (huv : u≤v) (E : ℝ)
    (hu : ∀ z, |(count (residueSet M A z) u:ℝ)-(count A u:ℝ)/M|≤E)
    (hv : ∀ z, |(count (residueSet M A z) v:ℝ)-(count A v:ℝ)/M|≤E)
    (z : ZMod M) :
    |(hist M (intervalPoints A u v) z:ℝ)-((intervalPoints A u v).card:ℝ)/M|≤2*E := by
  rw [interval_hist_real M A u v huv z,interval_card_real A u v huv]
  have he : (count (residueSet M A z) v:ℝ)-count (residueSet M A z) u-
      ((count A v:ℝ)-count A u)/M=
      ((count (residueSet M A z) v:ℝ)-(count A v:ℝ)/M)-
      ((count (residueSet M A z) u:ℝ)-(count A u:ℝ)/M) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hu z,hv z])

/-- Prefix residue control gives a cross estimate against an independently
chosen periodic interval, with its cardinality cost explicit. -/
theorem interval_periodic_mixed_error (A : Set ℕ) (u v : ℕ) (huv : u≤v)
    (D : Finset (ZMod M)) (L U n : ℕ)
    (hS : ∀ a∈intervalPoints A u v, a≤n ∧ L≤n-a ∧ n-a<U)
    (E : ℝ)
    (hE : ∀ N z, |(count (residueSet M A z) N:ℝ)-(count A N:ℝ)/M|≤E) :
    |(pairs (intervalPoints A u v) (periodicSlice M D L U) n:ℝ)-
      ((intervalPoints A u v).card:ℝ)*D.card/M|≤2*E*D.card := by
  exact pairs_periodicSlice_error M (intervalPoints A u v) D L U n hS (2*E)
    (interval_hist_error M A u v huv E (hE u) (hE v))

/-- The actual occurrence-phased set is admissible as the old side, with
    the full modulus and template-type cost retained. -/
theorem phased_interval_periodic_mixed_error {α : Type*} [Fintype α] [DecidableEq α]
    (f : ℕ → α) (C : α → Finset (ZMod M)) (u v : ℕ) (huv : u≤v)
    (D : Finset (ZMod M)) (L U n : ℕ)
    (hS : ∀ a∈intervalPoints (balancedBlockSet M f C) u v,
      a≤n ∧ L≤n-a ∧ n-a<U) :
    |(pairs (intervalPoints (balancedBlockSet M f C) u v)
        (periodicSlice M D L U) n:ℝ)-
      ((intervalPoints (balancedBlockSet M f C) u v).card:ℝ)*D.card/M| ≤
      2*((Fintype.card α:ℝ)+2)*M*D.card := by
  convert interval_periodic_mixed_error M (balancedBlockSet M f C) u v huv D L U n hS
    (((Fintype.card α:ℝ)+2)*M) (balanced_residue_discrepancy M f C) using 1 <;> ring

end Erdos66PeriodicMixedDiscrepancy
