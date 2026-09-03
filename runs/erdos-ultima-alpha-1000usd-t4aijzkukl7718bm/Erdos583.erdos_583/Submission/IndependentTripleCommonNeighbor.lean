import Submission.RegularRootAppend
import Submission.IndependentThreeEvenSharp

/-! Sharp floor-half decomposition for three independent even vertices with
one common neighbor, obtained by restoring three edges as regular petals. -/
namespace Erdos583IndependentTripleCommonNeighborDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.PendantCompletion Erdos583Work.EndpointSelection
open Erdos583RegularRootAppendDevelopment Erdos583RegularFlowerExposuresDevelopment
open Erdos583PathFamilyRootedCutDevelopment
open Erdos583IndependentThreeEvenSharpDevelopment
open Erdos583EvenEdgeRestorationDevelopment
open Erdos583ThreeEvenSharpRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma star_edges_distinct {V : Type*} {r a b : V} (ha : r ≠ a) (hab : a ≠ b) :
    s(r,a) ≠ s(r,b) := by
  intro hh
  rcases Sym2.eq_iff.mp hh with ⟨_,he⟩|⟨_,he⟩
  · exact hab he
  · exact ha he.symm

lemma sharp_independent_three_common_neighbor {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a b c w : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=a ∨ x=b ∨ x=c)
    (hwa : G.Adj w a) (hwb : G.Adj w b) (hwc : G.Adj w c)
    (hnab : ¬G.Adj a b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  classical
  let I := G.deleteEdges {s(w,a)}
  let J := I.deleteEdges {s(w,b)}
  let K := J.deleteEdges {s(w,c)}
  have hbI : I.Adj w b := deleteEdges_adj.mpr ⟨hwb,by
    simpa only [Set.mem_singleton_iff] using star_edges_distinct hwb.ne hab.symm⟩
  have hcI : I.Adj w c := deleteEdges_adj.mpr ⟨hwc,by
    simpa only [Set.mem_singleton_iff] using star_edges_distinct hwc.ne hac.symm⟩
  have hcJ : J.Adj w c := deleteEdges_adj.mpr ⟨hcI,by
    simpa only [Set.mem_singleton_iff] using star_edges_distinct hwc.ne hbc.symm⟩
  have hwaI := delete_edge_neighbor_card_left G hwa
  have hwbJ := delete_edge_neighbor_card_left I hbI
  have hwcK := delete_edge_neighbor_card_left J hcJ
  change Nat.card (I.neighborSet w)+1=Nat.card (G.neighborSet w) at hwaI
  change Nat.card (J.neighborSet w)+1=Nat.card (I.neighborSet w) at hwbJ
  change Nat.card (K.neighborSet w)+1=Nat.card (J.neighborSet w) at hwcK
  have hGw : Odd (Nat.card (G.neighborSet w)) := Nat.not_even_iff_odd.mp (by
    rw [he]
    exact not_or.mpr ⟨hwa.ne,not_or.mpr ⟨hwb.ne,hwc.ne⟩⟩)
  have hKw : Even (Nat.card (K.neighborSet w)) := by
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hGw
    omega
  have hKa : Odd (Nat.card (K.neighborSet a)) := by
    rw [delete_edge_neighbor_card_other J hwa.ne.symm hac,
      delete_edge_neighbor_card_other I hwa.ne.symm hab]
    exact EdgeDefect.even_degree_delete_edge_odd hwa ((he a).mpr (Or.inl rfl))
  have hKb : Odd (Nat.card (K.neighborSet b)) := by
    rw [delete_edge_neighbor_card_other J hwb.ne.symm hbc]
    apply EdgeDefect.even_degree_delete_edge_odd hbI
    rw [delete_edge_neighbor_card_other G hwb.ne.symm hab.symm]
    exact (he b).mpr (Or.inr (Or.inl rfl))
  have hKc : Odd (Nat.card (K.neighborSet c)) := by
    apply EdgeDefect.even_degree_delete_edge_odd hcJ
    rw [delete_edge_neighbor_card_other I hwc.ne.symm hbc.symm,
      delete_edge_neighbor_card_other G hwc.ne.symm hac.symm]
    exact (he c).mpr (Or.inr (Or.inr rfl))
  have hKo (x : V) (hxw : x ≠ w) : Odd (Nat.card (K.neighborSet x)) := by
    by_cases hxa : x=a
    · subst x; exact hKa
    by_cases hxb : x=b
    · subst x; exact hKb
    by_cases hxc : x=c
    · subst x; exact hKc
    rw [delete_edge_neighbor_card_other J hxw hxc,
      delete_edge_neighbor_card_other I hxw hxb,delete_edge_neighbor_card_other G hxw hxa]
    apply Nat.not_even_iff_odd.mp
    rw [he]
    exact not_or.mpr ⟨hxa,not_or.mpr ⟨hxb,hxc⟩⟩
  obtain ⟨D,hD,hne,hDq,hDc⟩ := MarkedBudgets.one_even_path_partition K w hKw hKo
  obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hne
  have htq (x : V) : T.quota x=if x=w then 0 else 1 := by rw [hTq,hDq]
  have hTJ : J.edgeSet=insert s(w,c) K.edgeSet := by
    rw [show K.edgeSet=J.edgeSet \ {s(w,c)} from edgeSet_deleteEdges _,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(w,c) ∈ J.edgeSet from hcJ)).symm
  obtain ⟨U,hUr,hUq⟩ := regular_append_edge_positive (J.deleteEdges_le _) T w c
    (path_family_regular_rooted T hT w) (by simp [htq,hwc.ne.symm]) hcJ (by simp) hTJ
  have hUb : U.quota b=1 := by
    have hh := hUq b
    simp only [htq,hwb.ne.symm,hwb.ne,hbc.symm,↓reduceIte,add_zero] at hh
    exact hh
  have hJI : I.edgeSet=insert s(w,b) J.edgeSet := by
    rw [show J.edgeSet=I.edgeSet \ {s(w,b)} from edgeSet_deleteEdges _,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(w,b) ∈ I.edgeSet from hbI)).symm
  obtain ⟨P,hPr,hPq⟩ := regular_append_edge_positive (I.deleteEdges_le _) U w b
    hUr (by omega) hbI (by simp) hJI
  have hPa : P.quota a=1 := by
    have h1 := hUq a
    have h2 := hPq a
    simp only [htq,hwa.ne.symm,hwa.ne,hac.symm,hab.symm,↓reduceIte,add_zero] at h1 h2
    omega
  have hIG : G.edgeSet=insert s(w,a) I.edgeSet := by
    rw [show I.edgeSet=G.edgeSet \ {s(w,a)} from edgeSet_deleteEdges _,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(w,a) ∈ G.edgeSet from hwa)).symm
  obtain ⟨Q,hQr,hQq⟩ := regular_append_edge_positive (G.deleteEdges_le _) P w a
    hPr (by omega) hwa (by simp) hIG
  have hQw : Q.quota w=3 := by
    have h1 := hUq w
    have h2 := hPq w
    have h3 := hQq w
    simp only [htq,hwc.ne.symm,hwb.ne.symm,hwa.ne.symm,↓reduceIte,add_zero] at h1 h2 h3
    omega
  have hzero : {z | Q.quota z=0} ⊆ ({a,b,c} : Set V) := by
    intro z hz
    change Q.quota z=0 at hz
    by_contra hnot
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hnot
    have h1 := hUq z
    have h2 := hPq z
    have h3 := hQq z
    simp only [hz,htq,Ne.symm hnot.1,Ne.symm hnot.2.1,Ne.symm hnot.2.2,
      if_false,zero_add] at h1 h2 h3
    by_cases hzw : z=w
    · subst z; omega
    · simp only [hzw,Ne.symm hzw,↓reduceIte,add_zero] at h1 h2 h3
      omega
  have hz : {z | Q.quota z=0}.ncard ≤ 3 := by
    have hh := Set.ncard_le_ncard hzero
    have h3 : ({a,b,c} : Set V).ncard=3 := by simp [Set.ncard_insert_of_notMem,hab,hac,hbc]
    omega
  have hf : (G.induce {z | Even (Nat.card (G.neighborSet z))}).IsAcyclic := by
    have hset : {z | Even (Nat.card (G.neighborSet z))}=({a,b,c} : Set V) := by ext z; exact he z
    rw [hset]
    exact triple_induce_acyclic_of_nonedge G a b c hnab
  obtain ⟨R,hR⟩ := normalize_regular_three_zeros Q w hQr hz (by omega) hf
  obtain ⟨E,hE,hEc⟩ := MatchingAppend.path_family_partition R hR
  exact ⟨E,hE,by omega⟩

end Erdos583IndependentTripleCommonNeighborDevelopment
