import Submission.Work

/-! Two endpoint tails per active vertex give a binary escape counting bound.
This does not assert that a globally closed blocked family always exists. -/

open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization
namespace Erdos583BinaryEscapeDevelopment
open scoped Classical

set_option maxHeartbeats 1200000

/-- With two edge-disjoint endpoint tails per source vertex, all final neighbors
are distinct. Neighbors supplied by a disjoint closed root trail are additional
unused targets. A closed collection therefore needs enough boundary vertices. -/
lemma binary_tail_boundary_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} (S A : Finset V) (hv : v ∉ S)
    (p : ∀ w : S, Bool → G.Walk w.val v)
    (hd : Pairwise fun x y : S × Bool ↦
      Disjoint (p x.1 x.2).toSubgraph.edgeSet (p y.1 y.2).toSubgraph.edgeSet)
    (C : G.Walk v v)
    (hc : ∀ w b, Disjoint C.toSubgraph.edgeSet (p w b).toSubgraph.edgeSet)
    (hclosed : ∀ w b, (p w b).penultimate ∈ S ∪ A)
    (hroot : ∀ z, C.toSubgraph.Adj v z → z ∈ S ∪ A) :
    S.card + (C.toSubgraph.neighborSet v).ncard ≤ A.card := by
  classical
  let f (x : S × Bool) := (p x.1 x.2).penultimate
  have hne (w : S) : w.val ≠ v := fun h ↦ hv (h ▸ w.property)
  have hf : Function.Injective f := by
    apply tail_last_neighbor_injective (fun x : S × Bool ↦ p x.1 x.2)
    · intro x; exact hne x.1
    · exact hd
  let E := Finset.univ.image f
  let R := Finset.univ.filter (fun z ↦ C.toSubgraph.Adj v z)
  have hE : E.card = 2*S.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp [Nat.mul_comm]
  have hR : R.card = (C.toSubgraph.neighborSet v).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext z
    simp [R]
  have hdis : Disjoint E R := by
    apply Finset.disjoint_left.mpr
    intro z hzE hzR
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hzE
    have hz : C.toSubgraph.Adj v (f x) := (Finset.mem_filter.mp hzR).2
    have ht : s(v,f x) ∈ (p x.1 x.2).toSubgraph.edgeSet :=
      ((p x.1 x.2).toSubgraph_adj_penultimate (Walk.not_nil_of_ne (hne x.1))).symm
    exact Set.disjoint_left.mp (hc x.1 x.2) hz ht
  have hsub : E ∪ R ⊆ S ∪ A := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
      exact hclosed x.1 x.2
    · exact hroot z ((Finset.mem_filter.mp hz).2)
  have hcount := (Finset.card_le_card hsub).trans (Finset.card_union_le S A)
  rw [Finset.card_union_of_disjoint hdis,hE,hR] at hcount
  omega

/-- If the boundary is too small, one of the final neighbors or one of the
root-trail neighbors must leave the proposed closed set. This is a counting
escape, not yet a trail-system exchange realizing that escape. -/
lemma exists_binary_tail_escape {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} (S A : Finset V) (hv : v ∉ S)
    (p : ∀ w : S, Bool → G.Walk w.val v)
    (hd : Pairwise fun x y : S × Bool ↦
      Disjoint (p x.1 x.2).toSubgraph.edgeSet (p y.1 y.2).toSubgraph.edgeSet)
    (C : G.Walk v v)
    (hc : ∀ w b, Disjoint C.toSubgraph.edgeSet (p w b).toSubgraph.edgeSet)
    (hsmall : A.card < S.card + (C.toSubgraph.neighborSet v).ncard) :
    ∃ z, G.Adj v z ∧ z ∉ S ∪ A ∧
      (C.toSubgraph.Adj v z ∨ ∃ w b, (p w b).penultimate = z) := by
  classical
  by_contra! hn
  have hclosed (w : S) (b : Bool) : (p w b).penultimate ∈ S ∪ A := by
    by_contra hz
    have hne : w.val ≠ v := fun h ↦ hv (h ▸ w.property)
    have ha := ((p w b).adj_penultimate (Walk.not_nil_of_ne hne)).symm
    exact (hn _ ha hz).2 w b rfl
  have hroot (z : V) (hz : C.toSubgraph.Adj v z) : z ∈ S ∪ A := by
    by_contra hz'
    exact (hn z (C.toSubgraph.adj_sub hz) hz').1 hz
  exact (not_le_of_gt hsmall) (binary_tail_boundary_bound S A hv p hd C hc hclosed hroot)

/-- A nonempty closed trail in a simple graph has at least two distinct root
neighbors, so a closed binary-tail collection has at least two extra boundary
vertices beyond its source vertices. -/
lemma binary_tail_boundary_add_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} (S A : Finset V) (hv : v ∉ S)
    (p : ∀ w : S, Bool → G.Walk w.val v)
    (hd : Pairwise fun x y : S × Bool ↦
      Disjoint (p x.1 x.2).toSubgraph.edgeSet (p y.1 y.2).toSubgraph.edgeSet)
    (C : G.Walk v v) (ht : C.IsTrail) (hn : ¬C.Nil)
    (hc : ∀ w b, Disjoint C.toSubgraph.edgeSet (p w b).toSubgraph.edgeSet)
    (hclosed : ∀ w b, (p w b).penultimate ∈ S ∪ A)
    (hroot : ∀ z, C.toSubgraph.Adj v z → z ∈ S ∪ A) :
    S.card + 2 ≤ A.card := by
  classical
  have htwo : 2 ≤ (C.toSubgraph.neighborSet v).ncard := by
    have hsub : {C.snd,C.penultimate} ⊆ C.toSubgraph.neighborSet v := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact C.toSubgraph_adj_snd hn
      · rw [Set.mem_singleton_iff.mp hz]
        exact (C.toSubgraph_adj_penultimate hn).symm
    have hh := Set.ncard_le_ncard hsub
    simpa only [Set.ncard_pair (closed_trail_snd_ne_penultimate C ht hn)] using hh
  have hh := binary_tail_boundary_bound S A hv p hd C hc hclosed hroot
  omega

end Erdos583BinaryEscapeDevelopment
