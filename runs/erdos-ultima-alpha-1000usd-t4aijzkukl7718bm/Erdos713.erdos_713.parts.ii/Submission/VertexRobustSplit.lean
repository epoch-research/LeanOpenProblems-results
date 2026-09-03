import FormalConjecturesUtil
import Submission.UniformIncidence
import Submission.SplitEdgePacking

/-! Vertex avoidance uses the gap to order n-|S|-1. This is a weighted
transversal bound, not unconditional vertex-disjointness of split copies. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713VertexRobustSplit
open Erdos713VertexMerging Erdos713VertexSplitWitnesses
open Erdos713RobustMergeWitnesses Erdos713SplitEdgePacking Erdos713UniformIncidence
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma common_induce_le [Fintype V] (G : SimpleGraph V) (A : Set V) (u v : A) :
    Nat.card ((G.induce A).commonNeighbors u v) ≤ Nat.card (G.commonNeighbors u.val v.val) := by
  apply Nat.card_le_card_of_injective
    (fun x : (G.induce A).commonNeighbors u v =>
      (⟨x.val.val,x.property⟩ : G.commonNeighbors u.val v.val))
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : G.commonNeighbors u.val v.val => z.val) h

/-- If deleting S and merging the roots is H-free, the degree mass of S
plus root overlap pays for the ENTIRE multi-order backward decrement. -/
lemma safe_delete_merge_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (S : Finset V) {u v : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hn : ¬ G.Adj u v)
    (hf : H.Free (merge (G.induce (S : Set V)ᶜ) ⟨u,hu⟩ ⟨v,hv⟩ hn)) :
    extremalNumber (Fintype.card V) H ≤
      extremalNumber (Fintype.card V-S.card-1) H +
      (∑ z ∈ S, Nat.card (G.neighborSet z)) + Nat.card (G.commonNeighbors u v) := by
  have hne : (⟨u,hu⟩ : ↥((S : Set V)ᶜ)) ≠ ⟨v,hv⟩ := fun h => huv (congrArg Subtype.val h)
  have hb := safe_merge_bound H (G.induce (S : Set V)ᶜ) hne hn hf
  have hc := common_induce_le G (S : Set V)ᶜ ⟨u,hu⟩ ⟨v,hv⟩
  dsimp only at hc
  have hdel := edges_le_induce_compl_add_degree G S
  have hcard : Fintype.card ↥((S : Set V)ᶜ) = Fintype.card V-S.card := by
    change Fintype.card {x : V // x ∉ S} = _
    rw [Fintype.card_subtype_compl]
    simp
  rw [hcard] at hb
  omega

def Avoids (H : SimpleGraph W) (G : SimpleGraph V) (u v : V) (S : Finset V) : Prop :=
  ∃ f : Witness H G u v, ∀ x, f.copy x ∉ S

theorem avoiding_of_degree_cost [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (S : Finset V) {u v : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hn : ¬ G.Adj u v)
    (hsmall : ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ) +
      (Nat.card (G.commonNeighbors u v) : ℝ) <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-S.card-1) H : ℝ)) : Avoids H G u v S := by
  have hcontains : H ⊑ merge (G.induce (S : Set V)ᶜ) ⟨u,hu⟩ ⟨v,hv⟩ hn := by
    by_contra hno
    have hN := safe_delete_merge_bound H G he S hu hv huv hn hno
    have hR : (extremalNumber (Fintype.card V) H : ℝ) ≤
        (extremalNumber (Fintype.card V-S.card-1) H : ℝ) +
        ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ) + (Nat.card (G.commonNeighbors u v) : ℝ) := by
      exact_mod_cast hN
    linarith
  have hfree : H.Free (G.induce (S : Set V)ᶜ) :=
    fun h => hf (h.trans ⟨Copy.induce G _⟩)
  obtain ⟨w,T,f,hL,hR,hNL,hNR⟩ := split_copy_of_merge (u := ⟨u,hu⟩) (v := ⟨v,hv⟩) hfree hn hcontains
  let g := (Copy.induce G (S : Set V)ᶜ).comp f
  have hgL : g (some w) = u := congrArg Subtype.val hL
  have hgR : g none = v := congrArg Subtype.val hR
  refine ⟨⟨w,T,g,hgL,hgR,hNL,hNR⟩,?_⟩
  intro x
  exact (f x).property

/-- A vertex transversal for all nontrivial split copies has a large
original degree sum. No upper bound on those degrees is presumed. -/
theorem transversal_degree_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (S : Finset V) {u v : V} (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hn : ¬ G.Adj u v) (hblock : ¬ Avoids H G u v S) :
    (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-S.card-1) H : ℝ) ≤
      ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ) + (Nat.card (G.commonNeighbors u v) : ℝ) := by
  by_contra hh
  exact hblock (avoiding_of_degree_cost H G hf he S hu hv huv hn (lt_of_not_ge hh))

#print axioms safe_delete_merge_bound
#print axioms avoiding_of_degree_cost
#print axioms transversal_degree_bound
end Erdos713VertexRobustSplit
