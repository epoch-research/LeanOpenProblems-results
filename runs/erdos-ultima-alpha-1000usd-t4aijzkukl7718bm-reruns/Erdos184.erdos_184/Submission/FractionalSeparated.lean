import Submission.FractionalEnvelope
import Submission.OneVertexCycles

/-! Exact additivity across a separation with at most one supported vertex
in common. This does not assert a rounding bound. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalSeparated
open FractionalCycles FractionalEnvelope
variable {V : Type*} [Fintype V]
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

/-- Change only the ambient graph of a cycle whose edges are in the new graph. -/
def restrictCycle {G A : SimpleGraph V} (H : CyclePiece G)
    (h : H.val.edgeSet ⊆ A.edgeSet) : CyclePiece A :=
  ⟨{ verts := H.val.verts
     Adj := H.val.Adj
     adj_sub := fun {u v} hab => h (show s(u,v) ∈ H.val.edgeSet from hab)
     symm := H.val.symm
     edge_vert := H.val.edge_vert }, H.property.1, by
       intro v
       simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
         using H.property.2 v⟩

@[simp] lemma restrictCycle_edges {G A : SimpleGraph V} (H : CyclePiece G)
    (h : H.val.edgeSet ⊆ A.edgeSet) : (restrictCycle H h).val.edgeSet = H.val.edgeSet := rfl

lemma disjoint_of_support_inter_le_one {A B : SimpleGraph V}
    (hover : (A.support ∩ B.support).ncard ≤ 1) : Disjoint A.edgeSet B.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e ha hb
  induction e using Sym2.ind with
  | h u v =>
    have hs := Set.ncard_le_one_iff_subsingleton.mp hover
    have huv : u = v := hs ⟨⟨v,ha⟩,⟨v,hb⟩⟩ ⟨⟨u,A.symm ha⟩,⟨u,B.symm hb⟩⟩
    exact A.ne_of_adj ha huv

/-- Fractional partitions of edge-disjoint graphs combine without a cost loss. -/
lemma combine {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hdis : Disjoint A.edgeSet B.edgeSet)
    (s : CyclePiece A → ℝ) (t : CyclePiece B → ℝ)
    (hs : IsFractionalPartition A s) (ht : IsFractionalPartition B t) :
    ∃ w : CyclePiece G → ℝ, IsFractionalPartition G w ∧ cost w = cost s + cost t := by
  have hAG : A ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_left)
  have hBG : B ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_right)
  let C : CyclePiece A ⊕ CyclePiece B → CyclePiece G :=
    Sum.elim (promoteCycle hAG) (promoteCycle hBG)
  let a : CyclePiece A ⊕ CyclePiece B → ℝ := Sum.elim s t
  have ha : ∀ i, 0 ≤ a i := by intro i; cases i with
    | inl H => exact hs.1 H
    | inr H => exact ht.1 H
  have hcov : ∀ e ∈ G.edgeSet, (∑ i, if e ∈ (C i).val.edgeSet then a i else 0) = 1 := by
    intro e he
    rw [Fintype.sum_sum_type]
    change (∑ H : CyclePiece A, if e ∈ H.val.edgeSet then s H else 0) +
      (∑ H : CyclePiece B, if e ∈ H.val.edgeSet then t H else 0) = 1
    rw [coverage_all hs e, coverage_all ht e]
    rw [← hcover] at he
    rcases he with he | he
    · simp [he, Set.disjoint_left.mp hdis he]
    · simp [he, Set.disjoint_right.mp hdis he]
  refine ⟨pushWeight C a, fractional_of_family G C a ha hcov, ?_⟩
  unfold cost
  rw [pushWeight_sum, Fintype.sum_sum_type]
  rfl

/-- Splitting needs cycle containment, not merely edge-disjointness. -/
lemma split {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hdis : Disjoint A.edgeSet B.edgeSet)
    (hcontain : ∀ H : CyclePiece G,
      H.val.edgeSet ⊆ A.edgeSet ∨ H.val.edgeSet ⊆ B.edgeSet)
    (t : CyclePiece G → ℝ) (ht : IsFractionalPartition G t) :
    ∃ s : CyclePiece A → ℝ, ∃ u : CyclePiece B → ℝ,
      IsFractionalPartition A s ∧ IsFractionalPartition B u ∧ cost s + cost u = cost t := by
  let p (H : CyclePiece G) := H.val.edgeSet ⊆ A.edgeSet
  let IA := {H : CyclePiece G // p H}
  let IB := {H : CyclePiece G // ¬ p H}
  have hb (H : IB) : H.val.val.edgeSet ⊆ B.edgeSet :=
    (hcontain H.val).resolve_left H.property
  let CA : IA → CyclePiece A := fun H => restrictCycle H.val H.property
  let CB : IB → CyclePiece B := fun H => restrictCycle H.val (hb H)
  let a : IA → ℝ := fun H => t H.val
  let b : IB → ℝ := fun H => t H.val
  have ha : ∀ H, 0 ≤ a H := fun H => ht.1 H.val
  have hb' : ∀ H, 0 ≤ b H := fun H => ht.1 H.val
  have hcovA : ∀ e ∈ A.edgeSet, (∑ H : IA, if e ∈ (CA H).val.edgeSet then a H else 0) = 1 := by
    intro e he
    change (∑ H : IA, if e ∈ H.val.val.edgeSet then t H.val else 0) = 1
    rw [sum_subtype_indicator p (fun H => if e ∈ H.val.edgeSet then t H else 0)]
    have heG : e ∈ G.edgeSet := hcover ▸ (Or.inl he)
    rw [← ht.2 e heG]
    apply Finset.sum_congr rfl
    intro H _
    by_cases hp : p H
    · simp [hp]
    · have hB := (hcontain H).resolve_left hp
      have hn : e ∉ H.val.edgeSet := fun h => Set.disjoint_left.mp hdis he (hB h)
      simp [hp,hn]
  have hcovB : ∀ e ∈ B.edgeSet, (∑ H : IB, if e ∈ (CB H).val.edgeSet then b H else 0) = 1 := by
    intro e he
    change (∑ H : IB, if e ∈ H.val.val.edgeSet then t H.val else 0) = 1
    rw [sum_subtype_indicator (fun H => ¬ p H) (fun H => if e ∈ H.val.edgeSet then t H else 0)]
    have heG : e ∈ G.edgeSet := hcover ▸ (Or.inr he)
    rw [← ht.2 e heG]
    apply Finset.sum_congr rfl
    intro H _
    by_cases hp : p H
    · have hn : e ∉ H.val.edgeSet := fun h => Set.disjoint_left.mp hdis (hp h) he
      simp [hp,hn]
    · simp [hp]
  refine ⟨pushWeight CA a, pushWeight CB b,
    fractional_of_family A CA a ha hcovA, fractional_of_family B CB b hb' hcovB, ?_⟩
  unfold cost
  rw [pushWeight_sum, pushWeight_sum]
  change (∑ H : IA, t H.val) + (∑ H : IB, t H.val) = ∑ H, t H
  rw [sum_subtype_indicator, sum_subtype_indicator, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hp : p H <;> simp [hp]

lemma even_sup {A B : SimpleGraph V} (hdis : Disjoint A.edgeSet B.edgeSet)
    (heA : ∀ v, Even (A.degree v)) (heB : ∀ v, Even (B.degree v)) :
    ∀ v, Even ((A ⊔ B).degree v) := by
  intro v
  have hh := degree_sup_of_edge_disjoint A B hdis v
  have ha := heA v
  have hb := heB v
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ha hb ⊢
  rw [hh]
  exact ha.add hb

/-- Exact fractional cost is additive across one-vertex separations. -/
lemma optimum_add {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1)
    (heA : ∀ v, Even (A.degree v)) (heB : ∀ v, Even (B.degree v)) :
    optimum G = optimum A + optimum B := by
  have hd := disjoint_of_support_inter_le_one hover
  have heG : ∀ v, Even (G.degree v) := by
    have heq : G = A ⊔ B := edgeSet_injective (by simpa using hcover.symm)
    rw [heq]
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using even_sup hd heA heB v
  apply le_antisymm
  · obtain ⟨s,hs,hcs⟩ := optimum_attained A heA
    obtain ⟨t,ht,hct⟩ := optimum_attained B heB
    obtain ⟨w,hw,hcw⟩ := combine hcover hd s t hs ht
    have hh := optimum_le_cost hw
    rwa [hcw,hcs,hct] at hh
  · obtain ⟨t,ht,hct⟩ := optimum_attained G heG
    obtain ⟨s,u,hs,hu,hc⟩ := split hcover hd (fun H =>
      cycle_contained_in_one_vertex_separation hcover hover H.val H.property.1 H.property.2) t ht
    have hsa := optimum_le_cost hs
    have hub := optimum_le_cost hu
    linarith

/-- The envelope itself is additive; the ambient graphs need not be even. -/
lemma envelope_add {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1) :
    envelope G = envelope A + envelope B := by
  have hAG : A ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_left)
  have hBG : B ≤ G := edgeSet_subset_edgeSet.mp (by rw [← hcover]; exact Set.subset_union_right)
  apply le_antisymm
  · apply envelope_le
    intro H hHG heH
    have hcov : (H ⊓ A).edgeSet ∪ (H ⊓ B).edgeSet = H.edgeSet := by
      rw [edgeSet_inf, edgeSet_inf, ← Set.inter_union_distrib_left, hcover]
      exact Set.inter_eq_left.mpr (edgeSet_mono hHG)
    have hov : ((H ⊓ A).support ∩ (H ⊓ B).support).ncard ≤ 1 :=
      (Set.ncard_le_ncard (Set.inter_subset_inter
        (support_mono (show H ⊓ A ≤ A from inf_le_right))
        (support_mono (show H ⊓ B ≤ B from inf_le_right)))).trans hover
    have heHA := even_left_of_one_vertex_separation heH hcov hov
    have heHB := even_left_of_one_vertex_separation heH
      (show (H ⊓ B).edgeSet ∪ (H ⊓ A).edgeSet = H.edgeSet by rw [Set.union_comm]; exact hcov)
      (by rwa [Set.inter_comm])
    rw [optimum_add hcov hov heHA heHB]
    exact add_le_add (optimum_le_envelope inf_le_right heHA) (optimum_le_envelope inf_le_right heHB)
  · obtain ⟨X,hXA,heX,hx⟩ := attained A
    obtain ⟨Y,hYB,heY,hy⟩ := attained B
    have hov : (X.support ∩ Y.support).ncard ≤ 1 :=
      (Set.ncard_le_ncard (Set.inter_subset_inter (support_mono hXA) (support_mono hYB))).trans hover
    have heXY := even_sup (disjoint_of_support_inter_le_one hov) heX heY
    have hle : X ⊔ Y ≤ G := sup_le (hXA.trans hAG) (hYB.trans hBG)
    have hh := optimum_le_envelope hle (by
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heXY v)
    rw [optimum_add (by rw [edgeSet_sup]) hov heX heY, hx, hy] at hh
    exact hh

end Erdos184.FractionalSeparated
