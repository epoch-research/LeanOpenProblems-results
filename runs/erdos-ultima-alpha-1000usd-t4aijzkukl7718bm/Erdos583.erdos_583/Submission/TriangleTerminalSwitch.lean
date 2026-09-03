import Submission.RootedPairReplacement
import Submission.TriangleTailRootTemplates

/-! The terminal-neighbor rotation of a two-edge triangular tail. -/
namespace Erdos583TriangleTerminalSwitchDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.TriangleAbsorption
open Erdos583TriangleTailRootTemplatesDevelopment
open Erdos583RootedPairReplacementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma four_neighbors_lower_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {u a b c d : V}
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c) (hd : G.Adj u d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ Nat.card (G.neighborSet u) := by
  have hsub : ({a,b,c,d} : Set V) ⊆ G.neighborSet u := by
    rintro z (rfl|rfl|rfl|rfl) <;> assumption
  have hh := Set.ncard_mono hsub
  simpa [Set.ncard_insert_of_notMem,hab,hac,had,hbc,hbd,hcd,←Nat.card_coe_set_eq] using hh

lemma terminal_carrier_degree {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t d : V}
    (F : Frame G r x y s t) (hyt : G.Adj y t) (htx : G.Adj t x) (hxs : G.Adj x s)
    (R : G.Walk s d)
    (hp : (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).IsPath)
    (hd : Disjoint (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).toSubgraph.edgeSet F.edges)
    (hr : r ∈ R.support) : 4 ≤ Nat.card (G.neighborSet s) := by
  cases R with
  | nil => exact (F.rs.ne (by simpa using hr)).elim
  | @cons _ z _ h R =>
    have hxR : x ∉ (Walk.cons h R).support := (Walk.cons_isPath_iff hxs _).mp hp.of_cons.of_cons |>.2
    have hxz : x ≠ z := fun hh ↦ hxR (by simp [hh])
    have hze : s(s,z) ∈ (Walk.cons hyt (Walk.cons htx (Walk.cons hxs (Walk.cons h R)))).toSubgraph.edgeSet := by simp
    have hrz : r ≠ z := by
      intro hh
      exact Set.disjoint_left.mp hd hze (by simp [Frame.edges,←hh,Sym2.eq_swap])
    have htz : t ≠ z := by
      intro hh
      exact Set.disjoint_left.mp hd hze (by simp [Frame.edges,←hh])
    exact four_neighbors_lower_bound F.rs.symm F.st hxs.symm h
      F.tr.symm F.rx.ne hrz F.tx htz hxz

lemma terminal_switch_data {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t d : V}
    (F : Frame G r x y s t) (hyt : G.Adj y t) (htx : G.Adj t x) (hxs : G.Adj x s)
    (R : G.Walk s d)
    (hp : (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).IsPath)
    (hd : Disjoint (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).toSubgraph.edgeSet F.edges) :
    let C := Walk.cons F.rx (Walk.cons hxs (Walk.cons F.rs.symm Walk.nil))
    let S := Walk.cons F.ry (Walk.cons hyt Walk.nil)
    let Q := Walk.cons F.xy.symm (Walk.cons htx.symm (Walk.cons F.st.symm R))
    C.IsCycle ∧ S.IsPath ∧ Q.IsPath ∧
      (∀ z ∈ C.support, z ∈ S.support → z=r) ∧
      Disjoint (C.append S).toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      (C.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
        F.edges ∪ (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).toSubgraph.edgeSet := by
  dsimp only
  let C := Walk.cons F.rx (Walk.cons hxs (Walk.cons F.rs.symm Walk.nil))
  let S := Walk.cons F.ry (Walk.cons hyt Walk.nil)
  let Q := Walk.cons F.xy.symm (Walk.cons htx.symm (Walk.cons F.st.symm R))
  have hR := hp.of_cons.of_cons.of_cons
  have hyR : y ∉ R.support := fun hh ↦ (Walk.cons_isPath_iff hyt _).mp hp |>.2 (by simp [hh])
  have htR : t ∉ R.support := fun hh ↦ (Walk.cons_isPath_iff htx _).mp hp.of_cons |>.2 (by simp [hh])
  have hxR : x ∉ R.support := (Walk.cons_isPath_iff hxs _).mp hp.of_cons.of_cons |>.2
  have hC : C.IsCycle := by
    have hrx := F.rx.ne
    have hrs := F.rs.ne
    have hxs' := hxs.ne
    simp only [C,Walk.cons_isCycle_iff,Walk.isPath_def,Walk.support_cons,Walk.support_nil,
      List.nodup_cons,List.nodup_nil,and_true,List.mem_cons,List.not_mem_nil,or_false,not_or,
      Walk.edges_cons,Walk.edges_nil]
    simp only [not_or,Sym2.eq_iff,not_and_or]
    aesop
  have hS : S.IsPath := by
    simp [S,Walk.cons_isPath_iff,F.ry.ne,hyt.ne,F.tr.symm]
  have hQ : Q.IsPath := by
    simp only [Q,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨⟨hR,htR⟩,htx.ne.symm,hxR⟩,F.xy.ne.symm,hyt.ne,hyR⟩
  have hint : ∀ z ∈ C.support, z ∈ S.support → z=r := by
    intro z hzC hzS
    simp only [C,S,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hzC hzS
    rcases hzC with rfl | rfl | rfl | rfl
    · rfl
    · rcases hzS with hh | hh | hh
      · exact hh
      · exact (F.xy.ne hh).elim
      · exact (F.tx hh.symm).elim
    · rcases hzS with hh | hh | hh
      · exact hh
      · exact (F.sy hh).elim
      · exact (F.st.ne hh).elim
    · rfl
  have hX := trail_append_of_disjoint hC.isTrail hS.isTrail
    (edge_disjoint_of_one_common_vertex C S hint)
  have he : (C.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
      F.edges ∪ (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).toSubgraph.edgeSet := by
    ext e
    simp only [C,S,Q,Frame.edges,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
      Walk.edges_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_append,Set.mem_union,
      Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := s) (b := r),
      Sym2.eq_swap (a := y) (b := x),Sym2.eq_swap (a := x) (b := t),Sym2.eq_swap (a := t) (b := s)]
    tauto
  have hlen : (C.append S).length+Q.length =
      (F.edges ∪ (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).toSubgraph.edgeSet).ncard := by
    rw [Set.union_comm,F.union_ncard _ hp hd]
    simp only [C,S,Q,Walk.length_append,Walk.length_cons,Walk.length_nil]
    omega
  exact ⟨hC,hS,hQ,hint,disjoint_of_cover_length _ _ hX hQ.isTrail _ he hlen,he⟩

lemma failure_no_terminal_triangle_carrier {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    {r x y s t d : Fin n} (L : RootedCycleRep T r) (j : Fin _)
    (hij : L.index ≠ j) (F : Frame G r x y s t)
    (hyt : G.Adj y t) (htx : G.Adj t x) (hxs : G.Adj x s) (R : G.Walk s d)
    (hp : (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).IsPath)
    (hLe : (T.walk L.index).toSubgraph.edgeSet=F.edges)
    (hPe : (T.walk j).toSubgraph=(Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).toSubgraph)
    (hr : r ∈ R.support) (hdr : Nat.card (G.neighborSet r)=5)
    (hdx : Nat.card (G.neighborSet x)=4) : False := by
  have hd : Disjoint (Walk.cons hyt (Walk.cons htx (Walk.cons hxs R))).toSubgraph.edgeSet F.edges := by
    rw [←hPe,←hLe]
    exact T.disjoint hij.symm
  obtain ⟨hC,hS,hQ,hint,hsep,hcover⟩ := terminal_switch_data F hyt htx hxs R hp hd
  rw [←hLe,←hPe] at hcover
  obtain ⟨U,M,hUs,hMC,hMS⟩ := replace_rooted_pair T hs r L j hij _ _ _ hC hS hQ hint hsep hcover
  have hMmax : ∀ W : TrailFamily G _, W.score ≤ U.score := fun W ↦ (hm W).trans_eq hUs.symm
  have hMscore : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  have hMt : M.tail.length=2 := hMS
  have hds := terminal_carrier_degree F hyt htx hxs R hp hd hr
  obtain ⟨_,_,_,hqs⟩ :=
    Erdos583ShortTriangleMixedCasesDevelopment.failure_degree_five_short_triangle_nonroot_degrees
      hsmall hG hfail U hMscore hMmax r M F.rx hxs F.rs hMC (Or.inr hMt) hdr
  have hds4 : Nat.card (G.neighborSet s)=4 := by omega
  exact Erdos583ShortTriangleQuarticPairExclusionDevelopment.failure_no_degree_five_short_triangle_quartic_pair
    hsmall hG hfail U hMscore hMmax r M F.rx hxs F.rs hMC (Or.inr hMt) hdr hdx hds4

end Erdos583TriangleTerminalSwitchDevelopment
