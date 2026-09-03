import Submission.LogDeficitCritical
import Submission.ExpansionPaths

/-! Short connecting paths in logarithmic-deficit counterexamples, including
connections between large sets after bounded edge or cycle deletion. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit ExpansionPaths
open SqrtDeficitSeparator (externalBoundary)
universe u
set_option maxHeartbeats 1000000
variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

lemma IsVertexMinimal.expands (hG : IsVertexMinimal C G) (hC : 0 < C) :
    ExpandsAbove G 0 (6*scale (Fintype.card V)) := by
  intro X _ hX hhalf
  have hb := hG.boundary_bound hC X hX hhalf
  have hm := scale_mono (show X.ncard ≤ Fintype.card V by omega)
  have hmul := Nat.mul_le_mul_right (externalBoundary G X).ncard
    (Nat.mul_le_mul_left 6 hm)
  exact hb.le.trans hmul

lemma IsVertexMinimal.expands_after_edge_deletion (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t) :
    ExpandsAbove (G.deleteEdges F) (4*scale (Fintype.card V)*t)
      (12*scale (Fintype.card V)) := by
  intro X hlow hX hhalf
  have hm := scale_mono (show X.ncard ≤ Fintype.card V by omega)
  have ht : 4*scale X.ncard*t ≤ X.ncard :=
    (Nat.mul_le_mul_right t (Nat.mul_le_mul_left 4 hm)).trans hlow
  have hb := hG.robust_boundary_bound hC F t hF X hX hhalf ht
  exact hb.le.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hm))

lemma IsVertexMinimal.expands_after_packing (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t : ℕ) (hP : P.card ≤ C*t) :
    ExpandsAbove (G \ unionPieces G P) (4*scale (Fintype.card V)*t)
      (12*scale (Fintype.card V)) := by
  intro X hlow hX hhalf
  have hm := scale_mono (show X.ncard ≤ Fintype.card V by omega)
  have ht : 4*scale X.ncard*t ≤ X.ncard :=
    (Nat.mul_le_mul_right t (Nat.mul_le_mul_left 4 hm)).trans hlow
  have hb := hG.robust_packing_boundary_bound hC P hc hd t hP X hX hhalf ht
  exact hb.le.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hm))

/-- A polylogarithmic upper bound for a path between any two vertices. -/
lemma IsVertexMinimal.short_path (hG : IsVertexMinimal C G) (hC : 0 < C)
    (u v : V) : ∃ p : G.Walk u v, p.IsPath ∧
      p.length ≤ 12*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1) := by
  obtain ⟨a,ha,b,hb,p,hp,hlen⟩ := short_path_between_sets G
    (show 0 < 6*scale (Fintype.card V) by exact Nat.mul_pos (by decide) (scale_pos _))
    (hG.expands hC) {u} {v} (by simp) (by omega) (by simp) (by omega)
  have ha' : a = u := ha
  have hb' : b = v := hb
  subst a
  subst b
  refine ⟨p,hp,?_⟩
  nlinarith

/-- Large sets can still be joined by a short simple path after deleting
at most C*t arbitrary edges. The endpoint sets need not be disjoint. -/
lemma IsVertexMinimal.short_path_after_edge_deletion (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t)
    (A B : Set V) (hA : 0 < A.ncard) (hB : 0 < B.ncard)
    (haA : 4*scale (Fintype.card V)*t ≤ A.ncard)
    (haB : 4*scale (Fintype.card V)*t ≤ B.ncard) :
    ∃ u ∈ A, ∃ v ∈ B, ∃ p : (G.deleteEdges F).Walk u v,
      p.IsPath ∧ p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1) := by
  obtain ⟨u,hu,v,hv,p,hp,hlen⟩ := short_path_between_sets (G.deleteEdges F)
    (show 0 < 12*scale (Fintype.card V) by exact Nat.mul_pos (by decide) (scale_pos _))
    (hG.expands_after_edge_deletion hC F t hF) A B hA haA hB haB
  exact ⟨u,hu,v,hv,p,hp,by nlinarith⟩

lemma IsVertexMinimal.short_path_after_packing (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t : ℕ) (hP : P.card ≤ C*t)
    (A B : Set V) (hA : 0 < A.ncard) (hB : 0 < B.ncard)
    (haA : 4*scale (Fintype.card V)*t ≤ A.ncard)
    (haB : 4*scale (Fintype.card V)*t ≤ B.ncard) :
    ∃ u ∈ A, ∃ v ∈ B, ∃ p : (G \ unionPieces G P).Walk u v,
      p.IsPath ∧ p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1) := by
  obtain ⟨u,hu,v,hv,p,hp,hlen⟩ := short_path_between_sets (G \ unionPieces G P)
    (show 0 < 12*scale (Fintype.card V) by exact Nat.mul_pos (by decide) (scale_pos _))
    (hG.expands_after_packing hC P hc hd t hP) A B hA haA hB haB
  exact ⟨u,hu,v,hv,p,hp,by nlinarith⟩

end Erdos184.LogDeficitSeparator
