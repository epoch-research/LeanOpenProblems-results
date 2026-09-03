import Submission.AssignedPacketRepairExplore
import Submission.PredecessorCandidateDegreeExplore

/-! Candidate-degree estimates for any bounded-fiber assignment into the old
set. The old/new and deleted/old costs are both retained. -/
namespace Erdos66AssignedPacketDegree
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66PredecessorCell
  Erdos66PredecessorPacketRepair Erdos66ReflectionRoundingPatch
  Erdos66PredecessorCandidateDegree
open scoped Classical
set_option maxHeartbeats 2400000
variable {α : Type*} [Fintype α]

lemma assigned_hit_card (A : Finset ℕ) (assign : ℕ → ℕ) (f : α → ℕ) (H : ℕ)
    (hmem : ∀ a, assign (f a) ∈ A)
    (hf : ∀ r, (Finset.univ.filter (fun a ↦ assign (f a) = r)).card ≤ H)
    (z : ℕ) :
    (Finset.univ.filter (fun a ↦ assign (f a) ≤ z ∧
      z-assign (f a) ∈ A)).card ≤ H*sumRep (A : Set ℕ) z := by
  let T := A.filter (fun r ↦ r ≤ z ∧ z-r ∈ A)
  have hh := bounded_preimage_card (fun a ↦ assign (f a)) H (by intro r; convert hf r using 1 <;> congr 2) T
  have he : (Finset.univ.filter (fun a ↦ assign (f a) ∈ T)) =
      Finset.univ.filter (fun a ↦ assign (f a) ≤ z ∧
        z-assign (f a) ∈ A) := by
    ext a
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, hmem a]
  have hT : T.card = sumRep (A : Set ℕ) z := by rw [← pairs_self, pairs_eq_filter]
  rw [hT] at hh
  convert hh using 1
  congr 1
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, hmem a]

theorem assigned_candidate_degrees (A : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ) (x : α → ℕ)
    (H W : ℕ) (start : Bool → ℕ) (V : ℝ)
    (hinj : ∀ b, Function.Injective (endpoint n x b))
    (hwindow : ∀ b a, start b ≤ endpoint n x b a ∧ endpoint n x b a < start b+W)
    (hlocal : ∀ L, ((intervalPart (A : Set ℕ) L (L+W)).card : ℝ) ≤ V)
    (hmem : ∀ b a, assign (endpoint n x b a) ∈ A)
    (hfiber : ∀ b r, (Finset.univ.filter (fun a ↦ assign (endpoint n x b a)=r)).card ≤ H) :
    ((Erdos66AssignedPacketRepair.badChoices A assign n x).card : ℝ) ≤ 2*V+2*H*sumRep (A : Set ℕ) n ∧
      ∀ z, ((Erdos66AssignedPacketRepair.swapHits A assign n x z).card : ℝ) ≤ 2*V+2*H*sumRep (A : Set ℕ) z := by
  have hdel (b : Bool) (z : ℕ) :
      ((Finset.univ.filter (fun a ↦ assign (endpoint n x b a) ≤ z ∧
        z-assign (endpoint n x b a) ∈ A)).card : ℝ) ≤ H*sumRep (A : Set ℕ) z := by
    exact_mod_cast assigned_hit_card A assign (endpoint n x b) H (hmem b) (hfiber b) z
  constructor
  · change ((Finset.univ.filter (fun a ↦ ∃ b, endpoint n x b a ∈ A ∨ _)).card : ℝ) ≤ _
    have hh := bool_union_card_bound
      (fun b a ↦ endpoint n x b a ∈ A)
      (fun b a ↦ assign (endpoint n x b a) ≤ n ∧
        n-assign (endpoint n x b a) ∈ A)
      V (H*sumRep (A : Set ℕ) n) (fun b ↦ ?_) (by intro b; convert hdel b n using 1 <;> congr 3)
    · convert hh using 1
      · congr 3
      · ring
    · have hc := interval_old_card (A : Set ℕ) (endpoint n x b) (hinj b) (start b) W (hwindow b)
      have hc' : ((Finset.univ.filter (fun a ↦ endpoint n x b a ∈ A)).card : ℝ) ≤
          (intervalPart (A : Set ℕ) (start b) (start b+W)).card := by exact_mod_cast hc
      convert hc'.trans (hlocal (start b)) using 1 <;> congr 3
  · intro z
    change ((Finset.univ.filter (fun a ↦ ∃ b, (endpoint n x b a ≤ z ∧ z-endpoint n x b a ∈ A) ∨ _)).card : ℝ) ≤ _
    have hh := bool_union_card_bound
      (fun b a ↦ endpoint n x b a ≤ z ∧ z-endpoint n x b a ∈ A)
      (fun b a ↦ assign (endpoint n x b a) ≤ z ∧
        z-assign (endpoint n x b a) ∈ A)
      V (H*sumRep (A : Set ℕ) z) (fun b ↦ ?_) (by intro b; convert hdel b z using 1 <;> congr 3)
    · convert hh using 1
      · congr 3
      · ring
    · have hc := interval_hit_card (A : Set ℕ) (endpoint n x b) (hinj b) (start b) W z (hwindow b)
      have hc' : ((Finset.univ.filter (fun a ↦ endpoint n x b a ≤ z ∧ z-endpoint n x b a ∈ A)).card : ℝ) ≤
          (intervalPart (A : Set ℕ) (z+1-(start b+W)) (z+1-(start b+W)+W)).card := by exact_mod_cast hc
      convert hc'.trans (hlocal _) using 1 <;> congr 3

end Erdos66AssignedPacketDegree
