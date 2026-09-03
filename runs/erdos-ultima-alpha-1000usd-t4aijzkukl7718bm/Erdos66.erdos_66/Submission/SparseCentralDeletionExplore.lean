import Submission.RemoteCentralDeletionExplore
import Submission.SquareExponentScheduleExplore
import Submission.CentralEndpointResetExplore
import Submission.ClippingBudgetTransferExplore

/-! Infinite unions of central packets at square-separated dyadic centers.
Deletion mass is negligible, and bounded packet collateral sums to o(log n)
at every target other than the chosen centers. -/
namespace Erdos66SparseCentralDeletion
open Filter AdditiveCombinatorics Erdos66Counting Erdos66CentralTripleDeletion
  Erdos66CentralEndpointReset Erdos66SquareExponentSchedule Erdos66DyadicDeletion
  Erdos66ClippingBudgetTransfer Erdos66Compactness Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 2800000

def packetUnion (D : ℕ → Finset ℕ) : Set ℕ := {a | ∃ j, a∈D j}

lemma hits_biUnion_bound (A : Set ℕ) (I : Finset ℕ) (D : ℕ → Finset ℕ) (z : ℕ) :
    (hits A (I.biUnion D) z).card ≤ ∑ j∈I, (hits A (D j) z).card := by
  have hs : hits A (I.biUnion D) z ⊆ I.biUnion (fun j ↦ hits A (D j) z) := by
    intro a ha
    obtain ⟨ha,haz,hza⟩ := Finset.mem_filter.mp ha
    obtain ⟨j,hj,ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨ha,haz,hza⟩⟩
  exact (Finset.card_le_card hs).trans Finset.card_biUnion_le

lemma packetUnion_cutoff_rep (A : Set ℕ) (k : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hk : ∀ j, (j+1)^2 ≤ k j) (hloc : ∀ j a, a∈D j → 2^(k j)<2*a) (z : ℕ) :
    sumRep (A\packetUnion D) z=
      sumRep (A\((Finset.range (activeBound z)).biUnion D : Set ℕ)) z := by
  apply sumRep_congr_below
  intro a haz
  have he : a∈packetUnion D ↔ a∈(Finset.range (activeBound z)).biUnion D := by
    constructor
    · rintro ⟨j,hj⟩
      have hbound := index_lt_activeBound k hk j z (by have := hloc j a hj; omega)
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hbound,hj⟩
    · intro ha
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp ha
      exact ⟨j,hj⟩
  simp only [Set.mem_diff,Finset.mem_coe,he]

lemma packetUnion_loss_bound (A : Set ℕ) (k : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hk : ∀ j, (j+1)^2 ≤ k j) (hloc : ∀ j a, a∈D j → 2^(k j)<2*a)
    (M : ℕ) (hhits : ∀ j z, z≠2^(k j) → (hits A (D j) z).card ≤ M)
    (z : ℕ) (hz : ¬∃ j, z=2^(k j)) :
    sumRep A z ≤ sumRep (A\packetUnion D) z+2*activeBound z*M := by
  rw [packetUnion_cutoff_rep A k D hk hloc z]
  have hh := deletion_inside_host A A ((Finset.range (activeBound z)).biUnion D) (Set.Subset.refl A) z
  have hc := hits_biUnion_bound A (Finset.range (activeBound z)) D z
  have hsum : (∑ j∈Finset.range (activeBound z), (hits A (D j) z).card) ≤ activeBound z*M := by
    calc
      _ ≤ ∑ _j∈Finset.range (activeBound z), M :=
        Finset.sum_le_sum (fun j _ ↦ hhits j z (fun h ↦ hz ⟨j,h⟩))
      _ = _ := by simp
  rw [Nat.mul_assoc]
  omega

/-- The error is set to zero exactly on the prescribed center set. -/
theorem off_center_loss_limit (A : Set ℕ) (k : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hk : ∀ j, (j+1)^2 ≤ k j) (hloc : ∀ j a, a∈D j → 2^(k j)<2*a)
    (M : ℕ) (hhits : ∀ j z, z≠2^(k j) → (hits A (D j) z).card ≤ M) :
    Tendsto (fun z : ℕ ↦ if ∃ j, z=2^(k j) then 0 else
      ((sumRep A z : ℝ)-sumRep (A\packetUnion D) z)/Real.log ((z : ℝ)+2))
      atTop (𝓝 0) := by
  have hb := activeBound_log_limit.const_mul (2*(M : ℝ))
  simp only [mul_zero] at hb
  apply squeeze_zero ?_ ?_ hb
  · intro z
    split_ifs
    · rfl
    · apply div_nonneg _ (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith))
      have hh := sumRep_mono (show A\packetUnion D ⊆ A from Set.diff_subset) z
      exact sub_nonneg.mpr (by exact_mod_cast hh)
  · intro z
    have hl : 0 ≤ Real.log ((z : ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith)
    split_ifs with hz
    · positivity
    · have hh := packetUnion_loss_bound A k D hk hloc M hhits z hz
      have hh' : (sumRep A z : ℝ) ≤ sumRep (A\packetUnion D) z+2*(activeBound z : ℝ)*M := by
        exact_mod_cast hh
      have he := div_le_div_of_nonneg_right (show (sumRep A z : ℝ)-sumRep (A\packetUnion D) z ≤
        2*(activeBound z : ℝ)*M by linarith) hl
      convert he using 1
      ring

lemma packetUnion_negligible (A : Set ℕ) (k : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hD : ∀ j, D j ⊆ removed A (k j)) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (henv : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)) :
    Tendsto (fun N : ℕ ↦ (count (packetUnion D) N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N))
      atTop (𝓝 0) := by
  have hsub : packetUnion D ⊆ A\pruned A := by
    rintro a ⟨j,hj⟩
    have hh := mem_removed.mp (hD j hj)
    exact ⟨hh.choose_spec.2.1,fun ha ↦ ha.2 (k j) (hD j hj)⟩
  have hc (N : ℕ) : count (packetUnion D) N ≤ count (A\pruned A) N := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨haN,ha⟩ := mem_cutoff.mp ha
    exact mem_cutoff.mpr ⟨haN,hsub ha⟩
  have he (N : ℕ) : (count (A\pruned A) N : ℝ)=(count A N : ℝ)-count (pruned A) N := by
    have hh := count_diff_add A (pruned A) (pruned_subset A) N
    have hh' : (count (A\pruned A) N : ℝ)+count (pruned A) N=count A N := by exact_mod_cast hh
    linarith
  apply squeeze_zero (fun N ↦ div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) ?_
    (discrepancy_normalized_limit hK hC henv)
  intro N
  rw [←he N]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact_mod_cast hc N

end Erdos66SparseCentralDeletion
