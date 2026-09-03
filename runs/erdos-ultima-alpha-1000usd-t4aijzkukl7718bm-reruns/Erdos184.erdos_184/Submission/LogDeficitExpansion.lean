import Submission.LogDeficitSeparator

/-! Near-linear external-neighborhood bounds, resilient under edge or cycle deletion.
These are necessary conditions on counterexamples, not a contradiction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit
open SqrtDeficitSeparator (externalBoundary)
universe u
set_option maxHeartbeats 1000000
variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

/-- Convert the dyadic separator inequalities into an external-neighborhood bound. -/
lemma boundary_bound_of_separator_bounds (H : SimpleGraph V) (t : ℕ)
    (hsep : ∀ (U W : Set V), U ∪ W = Set.univ →
      U.ncard < Fintype.card V → W.ncard < Fintype.card V →
      (∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬H.Adj x y) →
      ∀ j : ℕ, 2^j ≤ U.ncard → 2^j ≤ W.ncard →
      (2^j : ℕ)*weight j < (3 * (U ∩ W).ncard + t : ℕ))
    (X : Set V) (hX : 0 < X.ncard) (hhalf : 2*X.ncard ≤ Fintype.card V) :
    X.ncard < 2 * scale X.ncard * (3 * (externalBoundary H X).ncard + t) := by
  let S := externalBoundary H X
  have hdis : Disjoint X S := by
    apply Set.disjoint_left.mpr
    intro x hx hs
    exact hs.1 hx
  have hU : (X ∪ S).ncard = X.ncard + S.ncard := Set.ncard_union_eq hdis
  have hW : X.ncard + Xᶜ.ncard = Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl X
  by_cases hUl : (X ∪ S).ncard < Fintype.card V
  · have hWl : Xᶜ.ncard < Fintype.card V := by omega
    have hUW : (X ∪ S) ∪ Xᶜ = Set.univ := by
      ext x
      simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_univ,iff_true]
      tauto
    have hinter : (X ∪ S) ∩ Xᶜ = S := by
      ext x
      have hs : x ∈ S → x ∉ X := fun h => h.1
      simp only [Set.mem_inter_iff,Set.mem_union,Set.mem_compl_iff]
      tauto
    have hc : ∀ x ∈ (X ∪ S) \ Xᶜ, ∀ y ∈ Xᶜ \ (X ∪ S), ¬H.Adj x y := by
      intro x hx y hy hxy
      have hxX : x ∈ X := by simpa using hx.2
      have hyX : y ∉ X := hy.1
      have hyS : y ∉ S := fun h => hy.2 (Or.inr h)
      exact hyS ⟨hyX,x,hxX,hxy⟩
    have hp := Nat.pow_log_le_self 2 (Nat.ne_of_gt hX)
    have hjU : 2^(Nat.log 2 X.ncard) ≤ (X ∪ S).ncard := by omega
    have hjW : 2^(Nat.log 2 X.ncard) ≤ Xᶜ.ncard := by omega
    have hb := hsep (X ∪ S) Xᶜ hUW hUl hWl hc (Nat.log 2 X.ncard) hjU hjW
    rw [hinter] at hb
    exact lt_scale_mul_of_weight_lt hb
  · have hxS : X.ncard ≤ S.ncard := by omega
    have hscale := scale_pos X.ncard
    change X.ncard < 2 * scale X.ncard * (3*S.ncard+t)
    nlinarith

/-- The deletion budget is C*t edges at every set scale, with no evenness
hypothesis on the graph after deleting those edges. -/
lemma IsVertexMinimal.edge_deletion_boundary_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t)
    (X : Set V) (hX : 0 < X.ncard) (hhalf : 2*X.ncard ≤ Fintype.card V) :
    X.ncard < 2 * scale X.ncard *
      (3 * (externalBoundary (G.deleteEdges F) X).ncard + t) :=
  boundary_bound_of_separator_bounds (G.deleteEdges F) t
    (hG.edge_deletion_separator_bound hC F t hF) X hX hhalf

/-- Deleting whole cycle pieces has the same cost, independent of their lengths. -/
lemma IsVertexMinimal.packing_boundary_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t : ℕ) (hP : P.card ≤ C*t)
    (X : Set V) (hX : 0 < X.ncard) (hhalf : 2*X.ncard ≤ Fintype.card V) :
    X.ncard < 2 * scale X.ncard *
      (3 * (externalBoundary (G \ unionPieces G P) X).ncard + t) :=
  boundary_bound_of_separator_bounds (G \ unionPieces G P) t
    (hG.packing_separator_bound hC P hc hd t hP) X hX hhalf

lemma IsVertexMinimal.boundary_bound (hG : IsVertexMinimal C G) (hC : 0 < C)
    (X : Set V) (hX : 0 < X.ncard) (hhalf : 2*X.ncard ≤ Fintype.card V) :
    X.ncard < 6 * scale X.ncard * (externalBoundary G X).ncard := by
  have hb := hG.edge_deletion_boundary_bound hC ∅ 0 (by simp) X hX hhalf
  simp only [SimpleGraph.deleteEdges_empty,add_zero] at hb
  nlinarith

/-- At scale x, deletion of at most C*x/(4*scale(x)) edges leaves an
external boundary of size greater than x/(12*scale(x)). -/
lemma IsVertexMinimal.robust_boundary_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t)
    (X : Set V) (hX : 0 < X.ncard) (hhalf : 2*X.ncard ≤ Fintype.card V)
    (ht : 4*scale X.ncard*t ≤ X.ncard) :
    X.ncard < 12*scale X.ncard*(externalBoundary (G.deleteEdges F) X).ncard := by
  have hb := hG.edge_deletion_boundary_bound hC F t hF X hX hhalf
  nlinarith

lemma IsVertexMinimal.robust_packing_boundary_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t : ℕ) (hP : P.card ≤ C*t)
    (X : Set V) (hX : 0 < X.ncard) (hhalf : 2*X.ncard ≤ Fintype.card V)
    (ht : 4*scale X.ncard*t ≤ X.ncard) :
    X.ncard < 12*scale X.ncard*(externalBoundary (G \ unionPieces G P) X).ncard := by
  have hb := hG.packing_boundary_bound hC P hc hd t hP X hX hhalf
  nlinarith

end Erdos184.LogDeficitSeparator
