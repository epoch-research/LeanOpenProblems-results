import Submission.MinimalCycleConnectivity

/-! Bridge-only restoration after deleting an even subgraph of a globally
minimal graph. These are necessary conditions, not a uniform cycle bound. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work
set_option maxHeartbeats 400000
variable {V : Type*} [Fintype V]

namespace Critical
lemma number_delete_bridges (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, G.IsBridge e) :
    number G = number (G.deleteEdges (F : Set (Sym2 V))) + F.card := by
  induction F using Finset.induction_on generalizing G with
  | empty => simp
  | @insert e F he ih =>
    have hb := hF e (Finset.mem_insert_self _ _)
    have hrest : ∀ f ∈ F, (G.deleteEdges {e}).IsBridge f := by
      intro f hf
      have hb' := hF f (Finset.mem_insert_of_mem hf)
      have hmem := (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hb').1
      apply SimpleGraph.IsBridge.anti_of_mem_edgeSet (G.deleteEdges_le _) _ hb'
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨hmem,fun h => he ((Set.mem_singleton_iff.mp h) ▸ hf)⟩
    have hnum := number_delete_bridge hb
    have hih := ih (G.deleteEdges {e}) hrest
    rw [SimpleGraph.deleteEdges_deleteEdges] at hih
    have hset : ({e} : Set (Sym2 V)) ∪ (F : Set (Sym2 V)) = (insert e F : Finset (Sym2 V)) := by
      ext x
      simp
    rw [hset] at hih
    rw [Finset.card_insert_of_notMem he]
    omega

lemma number_sdiff_add_le (G E : SimpleGraph V) (hEG : E ≤ G) :
    number G ≤ number (G \ E) + number E := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum (G \ E)
  obtain ⟨A,hA,hdecA,hcardA⟩ := exists_minimum E
  have hdis : Disjoint (G \ E).edgeSet E.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.disjoint_sdiff_left
  have hcover : (G \ E).edgeSet ∪ E.edgeSet = G.edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.diff_union_of_subset (SimpleGraph.edgeSet_mono hEG)
  obtain ⟨B,hB,hdecB,hbound⟩ := combine_decompositions sdiff_le hEG hdis hcover
    D A hD hdec hA hdecA
  have hn := number_le B hB hdecB
  omega
end Critical

namespace BridgeExtension

/-- A subgraph can be extended to the ambient graph's reachability relation
using only edges that are bridges in the extension. -/
lemma exists_extension (R G : SimpleGraph V) (hRG : R ≤ G) :
    ∃ N : Finset (Sym2 V),
      (N : Set (Sym2 V)) ⊆ G.edgeSet \ R.edgeSet ∧
      (∀ e ∈ N, (R ⊔ SimpleGraph.fromEdgeSet (N : Set (Sym2 V))).IsBridge e) ∧
      (R ⊔ SimpleGraph.fromEdgeSet (N : Set (Sym2 V))).Reachable = G.Reachable := by
  obtain ⟨T,_,hTm⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
    (G := R) (H := ⊥) bot_le SimpleGraph.isAcyclic_bot
  have hTR : T ≤ R := hTm.prop.1
  have htR : T.Reachable = R.Reachable := SimpleGraph.reachable_eq_of_maximal_isAcyclic T hTm
  obtain ⟨F,hTF,hFm⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
    (G := G) (H := T) (hTR.trans hRG) hTm.prop.2
  have hFG : F ≤ G := hFm.prop.1
  have hfG : F.Reachable = G.Reachable := SimpleGraph.reachable_eq_of_maximal_isAcyclic F hFm
  let N := F.edgeFinset \ R.edgeFinset
  have hN : ∀ e, e ∈ N ↔ e ∈ F.edgeSet ∧ e ∉ R.edgeSet := by
    intro e
    simp only [N,Finset.mem_sdiff,SimpleGraph.mem_edgeFinset]
  have hS : R ⊔ SimpleGraph.fromEdgeSet (N : Set (Sym2 V)) = R ⊔ F := by
    ext x y
    simp only [SimpleGraph.sup_adj,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe,hN]
    constructor
    · rintro (hr | ⟨⟨hf,_⟩,_⟩)
      · exact Or.inl hr
      · exact Or.inr hf
    · rintro (hr | hf)
      · exact Or.inl hr
      · by_cases hr : R.Adj x y
        · exact Or.inl hr
        · exact Or.inr ⟨⟨hf,hr⟩,hf.ne⟩
  refine ⟨N,?_,?_,?_⟩
  · intro e he
    have hh := (hN e).mp he
    exact ⟨SimpleGraph.edgeSet_mono hFG hh.1,hh.2⟩
  · intro e he
    rw [hS]
    have hh := (hN e).mp he
    have hbF : F.IsBridge e :=
      SimpleGraph.isAcyclic_iff_forall_edge_isBridge.mp hFm.prop.2 hh.1
    induction e using Sym2.ind with | h a b =>
    have hTd : T ≤ F.deleteEdges {s(a,b)} := by
      intro x y hxy
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hTF hxy,?_⟩
      intro heq
      have hmem : s(x,y) ∈ R.edgeSet := hTR hxy
      rw [Set.mem_singleton_iff] at heq
      rw [heq] at hmem
      exact hh.2 hmem
    have hRd : ∀ x y, R.Reachable x y → (F.deleteEdges {s(a,b)}).Reachable x y := by
      intro x y hxy
      have ht : T.Reachable x y := by rwa [htR]
      exact ht.mono hTd
    apply SimpleGraph.isBridge_iff.mpr
    refine ⟨Or.inr hh.1,?_⟩
    change ¬ ((R ⊔ F).deleteEdges {s(a,b)}).Reachable a b
    rintro ⟨q⟩
    have hreach : ∀ {x y : V}, ((R ⊔ F).deleteEdges {s(a,b)}).Walk x y →
        (F.deleteEdges {s(a,b)}).Reachable x y := by
      intro x y q
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons x z y hxz q ih =>
        have hxz' := SimpleGraph.deleteEdges_adj.mp hxz
        have hstep : (F.deleteEdges {s(a,b)}).Reachable x z := by
          rcases hxz'.1 with hr | hf
          · exact hRd x z hr.reachable
          · exact (SimpleGraph.deleteEdges_adj.mpr ⟨hf,hxz'.2⟩).reachable
        exact hstep.trans ih
    exact (SimpleGraph.isBridge_iff.mp hbF).2 (hreach q)
  · rw [hS]
    funext x y
    apply propext
    constructor
    · exact SimpleGraph.Reachable.mono (sup_le hRG hFG)
    · intro hxy
      have hf : F.Reachable x y := by rwa [hfG]
      exact hf.mono le_sup_right

end BridgeExtension

namespace EdgeHull
open Critical
variable {G E : SimpleGraph V}

lemma Minimal.bridge_restoration_lt (hm : Minimal G) (hEG : E ≤ G)
    (hE : ∀ v, Even (E.degree v)) (hEbot : E ≠ ⊥)
    (F : Finset (Sym2 V)) (hFE : (F : Set (Sym2 V)) ⊆ E.edgeSet)
    (hbridge : ∀ e ∈ F, ((G \ E) ⊔ SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsBridge e) :
    F.card < number E := by
  let R := G \ E
  let S := R ⊔ SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  have hFG : SimpleGraph.fromEdgeSet (F : Set (Sym2 V)) ≤ G := by
    intro x y hxy
    exact hEG (hFE hxy.1)
  have hSG : S ≤ G := sup_le sdiff_le hFG
  have hdel : S.deleteEdges (F : Set (Sym2 V)) = R := by
    ext x y
    simp only [S,SimpleGraph.deleteEdges_adj,SimpleGraph.sup_adj,SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hxy,hnot⟩
      rcases hxy with hxy | ⟨hxy,_⟩
      · exact hxy
      · exact (hnot hxy).elim
    · intro hxy
      exact ⟨Or.inl hxy,fun hf => hxy.2 (hFE hf)⟩
  have hne : S ≠ G := by
    intro heq
    obtain ⟨u,p,hp⟩ := exists_cycle_of_even_ne_bot E hE hEbot
    cases p with
    | nil => exact hp.ne_nil rfl
    | @cons u v u huv p =>
      have heG : G.Adj u v := hEG huv
      have heS : S.Adj u v := heq.symm ▸ heG
      have heF : s(u,v) ∈ F := by
        rcases heS with hr | hf
        · exact (hr.2 huv).elim
        · exact hf.1
      have hbG : G.IsBridge s(u,v) := heq ▸ hbridge _ heF
      have hbE := SimpleGraph.IsBridge.anti_of_mem_edgeSet hEG huv hbG
      exact (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hbE).2
        (.cons huv p) hp (by simp)
  have hn := number_delete_bridges S F hbridge
  rw [hdel] at hn
  have hmin := hm S hSG hne
  have hbound := number_sdiff_add_le G E hEG
  change number G ≤ number R + number E at hbound
  omega

/-- Deleting any nonempty even subgraph of a globally minimal core permits
restoring the original reachability with fewer edges than its decomposition
number. Thus deleting q edge-disjoint cycles needs at most q-1 restoration
edges, even though minimality need not pass to the cofactor. -/
lemma Minimal.exists_small_bridge_restoration (hm : Minimal G) (hEG : E ≤ G)
    (hE : ∀ v, Even (E.degree v)) (hEbot : E ≠ ⊥) :
    ∃ F : Finset (Sym2 V), (F : Set (Sym2 V)) ⊆ E.edgeSet ∧ F.card < number E ∧
      (∀ e ∈ F, ((G \ E) ⊔ SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsBridge e) ∧
      ((G \ E) ⊔ SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable = G.Reachable := by
  obtain ⟨F,hF,hb,hr⟩ := BridgeExtension.exists_extension (G \ E) G sdiff_le
  have hFE : (F : Set (Sym2 V)) ⊆ E.edgeSet := by
    intro e he
    have hh := hF he
    by_contra hnot
    apply hh.2
    rw [SimpleGraph.edgeSet_sdiff]
    exact ⟨hh.1,hnot⟩
  exact ⟨F,hFE,hm.bridge_restoration_lt hEG hE hEbot F hFE hb,hb,hr⟩

end EdgeHull
end Erdos184Work

#print axioms Erdos184Work.Critical.number_delete_bridges
#print axioms Erdos184Work.EdgeHull.Minimal.bridge_restoration_lt

#print axioms Erdos184Work.BridgeExtension.exists_extension
#print axioms Erdos184Work.EdgeHull.Minimal.exists_small_bridge_restoration
