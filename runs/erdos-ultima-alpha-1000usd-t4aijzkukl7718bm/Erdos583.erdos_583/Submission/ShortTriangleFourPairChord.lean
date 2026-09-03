import Submission.ShortTriangleExternalCarrier

/-! A degree-four pair forces an existing external shortcut edge. -/
namespace Erdos583ShortTriangleFourPairChordDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleSingleCarrierDevelopment Erdos583ShortTriangleIncidenceDevelopment
open Erdos583ShortTriangleExternalCarrierDevelopment Erdos583DoubleSmoothTriangleDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma failure_degree_five_short_triangle_four_pair_chord {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hd : Nat.card (G.neighborSet r)=5)
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=4) :
    ∃ a b c d, G.Adj x a ∧ G.Adj x b ∧ G.Adj y c ∧ G.Adj y d ∧
      a ≠ b ∧ c ≠ d ∧ a ≠ r ∧ b ≠ r ∧ a ≠ y ∧ b ≠ y ∧
      c ≠ r ∧ d ≠ r ∧ c ≠ x ∧ d ≠ x ∧ s(a,b) ≠ s(c,d) ∧
      (G.Adj a b ∨ G.Adj c d) := by
  classical
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hq := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)).1
  obtain ⟨j,hji,hrP,hunique⟩ := short_triangle_degree_five_unique_carrier T hs hm r L hc ht hq hd
  let P := T.walk j
  have hP : P.IsPath := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hji
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  obtain ⟨a,b,hxa,hxb,hab,hra,hrb,hya,hyb,hNx⟩ :=
    DegreeFourReduction.degree_four_other_neighbors hrx.symm hxy hry.ne hdx
  obtain ⟨c,d,hyc,hyd,hcd,hrc,hrd,hxc,hxd,hNy⟩ :=
    DegreeFourReduction.degree_four_other_neighbors hry.symm hxy.symm hrx.ne hdy
  let C : Set (Sym2 (Fin n)) := {s(r,x),s(x,y),s(r,y)}
  let F := G.deleteEdges C
  have hCe : L.cycle.toSubgraph.edgeSet=C := by
    rw [hC]
    ext e
    simp only [C,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
  have hnxa : s(x,a) ∉ C := by simp [C,hrx.ne.symm,hxy.ne,hra.symm,hya.symm]
  have hnxb : s(x,b) ∉ C := by simp [C,hrx.ne.symm,hxy.ne,hrb.symm,hyb.symm]
  have hnyc : s(y,c) ∉ C := by simp [C,hry.ne.symm,hxy.ne.symm,hrc.symm,hxc.symm]
  have hnyd : s(y,d) ∉ C := by simp [C,hry.ne.symm,hxy.ne.symm,hrd.symm,hxd.symm]
  have hxap : s(x,a) ∈ P.edges := unique_carrier_external_edge T r L j hunique hxC hrx.ne.symm hxa
    (by rwa [hCe])
  have hxbp : s(x,b) ∈ P.edges := unique_carrier_external_edge T r L j hunique hxC hrx.ne.symm hxb
    (by rwa [hCe])
  have hycp : s(y,c) ∈ P.edges := unique_carrier_external_edge T r L j hunique hyC hry.ne.symm hyc
    (by rwa [hCe])
  have hydp : s(y,d) ∈ P.edges := unique_carrier_external_edge T r L j hunique hyC hry.ne.symm hyd
    (by rwa [hCe])
  have hpairs : s(a,b) ≠ s(c,d) := path_spoke_pairs_ne P hP hxy.ne hab hxap hxbp hycp hydp
  refine ⟨a,b,c,d,hxa,hxb,hyc,hyd,hab,hcd,hra.symm,hrb.symm,hya.symm,hyb.symm,
    hrc.symm,hrd.symm,hxc.symm,hxd.symm,hpairs,?_⟩
  by_contra hn
  have hnab : ¬G.Adj a b := fun h ↦ hn (Or.inl h)
  have hncd : ¬G.Adj c d := fun h ↦ hn (Or.inr h)
  have havoid (e : Sym2 (Fin n)) (he : e ∈ C) : e ∉ P.edges := by
    intro hep
    have hi : e ∈ (T.walk L.index).toSubgraph.edgeSet := by
      rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
      exact Or.inl (hCe.symm ▸ he)
    exact Set.disjoint_left.mp (T.disjoint hji.symm) hi (P.mem_edges_toSubgraph.mpr hep)
  have hF : SupportConnected F := delete_triangle_connected_of_walk hG P hrP
    (P.fst_mem_support_of_mem_edges hxap) (P.fst_mem_support_of_mem_edges hycp) havoid
  have hdis : Disjoint C F.edgeSet := by
    rw [edgeSet_deleteEdges]
    exact Set.disjoint_left.mpr (fun _ he hh ↦ hh.2 he)
  have hcover : G.edgeSet=F.edgeSet ∪ C := by
    rw [edgeSet_deleteEdges]
    apply (Set.diff_union_of_subset _).symm
    rintro e (rfl|rfl|rfl)
    · exact hrx
    · exact hxy
    · exact hry
  have hNxF (z : Fin n) (hz : F.Adj x z) : z=a ∨ z=b := by
    obtain ⟨hzG,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNx z hzG with hz | hz | hz | hz
    · subst z; exact (hnz (Or.inl Sym2.eq_swap)).elim
    · subst z; exact (hnz (Or.inr (Or.inl rfl))).elim
    · exact Or.inl hz
    · exact Or.inr hz
  have hNyF (z : Fin n) (hz : F.Adj y z) : z=c ∨ z=d := by
    obtain ⟨hzG,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNy z hzG with hz | hz | hz | hz
    · subst z; exact (hnz (Or.inr (Or.inr Sym2.eq_swap))).elim
    · subst z; exact (hnz (Or.inr (Or.inl Sym2.eq_swap))).elim
    · exact Or.inl hz
    · exact Or.inr hz
  exact hfail (two_fresh_shortcuts_triangle_reduction hsmall (deleteEdges_le C) hF hrx hxy hry hdis hcover
    (deleteEdges_adj.mpr ⟨hxa,hnxa⟩) (deleteEdges_adj.mpr ⟨hxb,hnxb⟩)
    (deleteEdges_adj.mpr ⟨hyc,hnyc⟩) (deleteEdges_adj.mpr ⟨hyd,hnyd⟩)
    hab hcd hya.symm hyb.symm hNxF hNyF (fun h ↦ hnab (deleteEdges_le C h))
    (fun h ↦ hncd (deleteEdges_le C h)) hpairs)

end Erdos583ShortTriangleFourPairChordDevelopment
