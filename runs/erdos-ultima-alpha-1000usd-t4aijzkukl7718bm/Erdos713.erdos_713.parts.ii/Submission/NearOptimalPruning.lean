import FormalConjecturesUtil
import Submission.UniformIncidence

/-! High-degree pruning with arbitrarily small vertex and edge loss.
The pruned graph is not asserted exactly extremal or clone-saturated. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713NearOptimalPruning
open Erdos713UniformIncidence Erdos713Cloning
set_option maxHeartbeats 2000000
variable {V W : Type*}

lemma induce_neighbor_card_le [Fintype V] (G : SimpleGraph V) (S : Set V) (v : S) :
    Nat.card ((G.induce S).neighborSet v) ≤ Nat.card (G.neighborSet v.val) := by
  let f : (G.induce S).neighborSet v → G.neighborSet v.val :=
    fun w => ⟨w.val.val,w.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : G.neighborSet v.val => z.val) h
  exact Nat.card_le_card_of_injective f hf

/-- The vertex set removed and its original degree mass are both small,
uniformly over H-free hosts. The scale is the original order n. -/
theorem prune_high_degrees (H : SimpleGraph W) {α c : ℝ}
    (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n → H.Free G →
        ∃ S : Finset V,
          (S.card : ℝ) ≤ ε*n ∧
          (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤ ε*(n : ℝ)^α ∧
          (Nat.card G.edgeSet : ℝ) ≤ (Nat.card (G.induce (S : Set V)ᶜ).edgeSet : ℝ)+ε*(n : ℝ)^α ∧
          H.Free (G.induce (S : Set V)ᶜ) ∧
          ∀ v : ↥((S : Set V)ᶜ),
            (Nat.card ((G.induce (S : Set V)ᶜ).neighborSet v) : ℝ) ≤ K*(n : ℝ)^(α-1) := by
  classical
  obtain ⟨K₀,hK₀,hMass⟩ := high_degree_mass H ha hc h hε
  let K := max 1 K₀
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKK : K₀ ≤ K := le_max_right _ _
  refine ⟨K,hK,?_⟩
  filter_upwards [hMass,eventually_gt_atTop (0 : ℕ)] with n hmass hn
  intro V instV G hcard hf
  let S := univ.filter (fun v : V => K*(n : ℝ)^(α-1) < (Nat.card (G.neighborSet v) : ℝ))
  have hp : 0 < (n : ℝ)^(α-1) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hS (v : V) (hv : v ∈ S) : K*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ) :=
    (mem_filter.mp hv).2.le
  have hMassS := hmass V G hcard hf S (fun v hv =>
    (mul_le_mul_of_nonneg_right hKK hp.le).trans (hS v hv))
  have hSmall : (S.card : ℝ) ≤ ε*n := by
    have hsum := sum_le_sum (s := S) hS
    simp only [sum_const,nsmul_eq_mul] at hsum
    have hkone := mul_le_mul_of_nonneg_right hK1
      (show 0 ≤ (S.card : ℝ)*(n : ℝ)^(α-1) by positivity)
    have hFac := rpow_factor (Nat.cast_nonneg n) ha
    rw [hFac] at hMassS
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith only [hsum,hMassS,hkone]
  have hDel : (Nat.card G.edgeSet : ℝ) ≤
      (Nat.card (G.induce (S : Set V)ᶜ).edgeSet : ℝ)+ε*(n : ℝ)^α := by
    have hh : (Nat.card G.edgeSet : ℝ) ≤ (Nat.card (G.induce (S : Set V)ᶜ).edgeSet : ℝ)+
        ∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ) := by
      exact_mod_cast edges_le_induce_compl_add_degree G S
    exact hh.trans (add_le_add le_rfl hMassS)
  refine ⟨S,hSmall,hMassS,hDel,fun hQ => hf (hQ.trans ⟨Copy.induce G _⟩),?_⟩
  intro v
  have hv : (Nat.card (G.neighborSet v.val) : ℝ) ≤ K*(n : ℝ)^(α-1) := by
    have hnS : v.val ∉ S := v.property
    simpa only [S,mem_filter,mem_univ,true_and,not_lt] using hnS
  exact (Nat.cast_le.mpr (induce_neighbor_card_le G _ v)).trans hv

#print axioms induce_neighbor_card_le
#print axioms prune_high_degrees
end Erdos713NearOptimalPruning
