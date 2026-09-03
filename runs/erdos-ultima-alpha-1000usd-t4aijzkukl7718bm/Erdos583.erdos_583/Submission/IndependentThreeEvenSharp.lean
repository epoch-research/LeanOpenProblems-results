import Submission.ThreeEvenSharpRestoration
import Submission.LocalZeroNormalization

/-! Sharp restoration for three independent even vertices, when an outside
vertex is adjacent to exactly two of them. No unrestricted activity or
endpoint-separation assertion is used. -/
namespace Erdos583IndependentThreeEvenSharpDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.PendantCompletion Erdos583Work.EndpointSelection
open Erdos583Work.ComponentDeficit
open Erdos583EvenEdgeRestorationDevelopment
open Erdos583LocalZeroNormalizationDevelopment
open Erdos583ThreeEvenSharpRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

lemma delete_edge_neighbor_card_other {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u v x : V} (hxu : x ≠ u) (hxv : x ≠ v) :
    Nat.card ((G.deleteEdges {s(u,v)}).neighborSet x)=Nat.card (G.neighborSet x) := by
  classical
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  exact degree_delete_edge_other G hxu hxv

lemma delete_edge_neighbor_card_left {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u v : V} (h : G.Adj u v) :
    Nat.card ((G.deleteEdges {s(u,v)}).neighborSet u)+1=Nat.card (G.neighborSet u) := by
  classical
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  exact degree_delete_edge_left G h

lemma sharp_independent_three_two_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a b c w : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=a ∨ x=b ∨ x=c)
    (haw : G.Adj w a) (hbw : G.Adj b w)
    (hnab : ¬G.Adj a b) (hnac : ¬G.Adj a c) (hnbc : ¬G.Adj b c)
    (hnwc : ¬G.Adj w c) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  classical
  have hwc : w ≠ c := by rintro rfl; exact hnac haw.symm
  let I := G.deleteEdges {s(b,w)}
  let J := I.deleteEdges {s(w,a)}
  have hawI : I.Adj w a := by
    apply deleteEdges_adj.mpr
    refine ⟨haw,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq_iff]
    rintro (⟨hwb,_⟩|⟨_,hab'⟩)
    · exact hbw.ne hwb.symm
    · exact hab hab'
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  have hcw : c ≠ w := hwc.symm
  have hJc : Even (Nat.card (J.neighborSet c)) := by
    rw [delete_edge_neighbor_card_other I hcw hca,
      delete_edge_neighbor_card_other G hcb hcw]
    exact (he c).mpr (Or.inr (Or.inr rfl))
  have hJa : Odd (Nat.card (J.neighborSet a)) := by
    apply EdgeDefect.even_degree_delete_edge_odd hawI
    rw [delete_edge_neighbor_card_other G hab haw.ne.symm]
    exact (he a).mpr (Or.inl rfl)
  have hJb : Odd (Nat.card (J.neighborSet b)) := by
    rw [delete_edge_neighbor_card_other I hbw.ne hab.symm]
    have hh := EdgeDefect.even_degree_delete_edge_odd hbw.symm
      ((he b).mpr (Or.inr (Or.inl rfl)))
    simpa only [I,Sym2.eq_swap] using hh
  have hJw : Odd (Nat.card (J.neighborSet w)) := by
    have hGw : Odd (Nat.card (G.neighborSet w)) := Nat.not_even_iff_odd.mp (by
      rw [he]
      exact not_or.mpr ⟨haw.ne,not_or.mpr ⟨hbw.ne.symm,hwc⟩⟩)
    have hI : Nat.card (I.neighborSet w)+1=Nat.card (G.neighborSet w) := by
      simpa only [I,Sym2.eq_swap] using delete_edge_neighbor_card_left G hbw.symm
    have hJ := delete_edge_neighbor_card_left I hawI
    change Nat.card (J.neighborSet w)+1=Nat.card (I.neighborSet w) at hJ
    obtain ⟨k,hk⟩ := hGw
    exact ⟨k-1,by omega⟩
  have hJo (x : V) (hxc : x ≠ c) : Odd (Nat.card (J.neighborSet x)) := by
    by_cases hxa : x=a
    · subst x; exact hJa
    by_cases hxb : x=b
    · subst x; exact hJb
    by_cases hxw : x=w
    · subst x; exact hJw
    rw [delete_edge_neighbor_card_other I hxw hxa,
      delete_edge_neighbor_card_other G hxb hxw]
    apply Nat.not_even_iff_odd.mp
    rw [he]
    tauto
  obtain ⟨D,hD,hne,hDq,hDc⟩ := MarkedBudgets.one_even_path_partition J c hJc hJo
  obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hne
  have hq (x : V) : T.quota x=if x=c then 0 else 1 := by rw [hTq,hDq]
  obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T (v := a) (by simp [hq,hac])
  have hcoverI : I.edgeSet=insert s(w,a) J.edgeSet := by
    rw [show J.edgeSet=I.edgeSet \ {s(w,a)} from edgeSet_deleteEdges _,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(w,a) ∈ I.edgeSet from hawI)).symm
  have havoidI (x : V) (hx : I.Adj w x) : T.quota x ≠ 0 := by
    have hxc : x ≠ c := by rintro rfl; exact hnwc (G.deleteEdges_le _ hx)
    simp [hq,hxc]
  obtain ⟨P,hP,hPq⟩ := append_edge_away_from_inactive (I.deleteEdges_le {s(w,a)})
    T hT i hi hawI (by simp) hcoverI havoidI
  have hPw : P.quota w=2 := by
    have hh := hPq w
    simp only [hq,hwc,haw.ne.symm,↓reduceIte,add_zero] at hh
    omega
  have hPzero (x : V) (hx : P.quota x=0) : x=a ∨ x=c := by
    by_cases hxa : x=a
    · exact Or.inl hxa
    by_cases hxc : x=c
    · exact Or.inr hxc
    have hh := hPq x
    simp only [hx,hq,hxc,Ne.symm hxa,↓reduceIte,add_zero] at hh
    omega
  obtain ⟨j,hj⟩ := DeletionEndpoint.endpoint_of_positive_quota P (v := w) (by omega)
  have hcoverG : G.edgeSet=insert s(b,w) I.edgeSet := by
    rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(b,w) ∈ G.edgeSet from hbw)).symm
  have havoidG (x : V) (hx : G.Adj b x) : P.quota x ≠ 0 := by
    intro hzero
    rcases hPzero x hzero with rfl|rfl
    · exact hnab hx.symm
    · exact hnbc hx
  obtain ⟨Q,hQ,_⟩ := append_edge_away_from_inactive (G.deleteEdges_le {s(b,w)})
    P hP j hj hbw (by simp) hcoverG havoidG
  obtain ⟨E,hE,hEc⟩ := MatchingAppend.path_family_partition Q hQ
  exact ⟨E,hE,by omega⟩

lemma sharp_three_even_two_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hthree : evenCount G=3) (a b c w : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (G.neighborSet a)))
    (hb : Even (Nat.card (G.neighborSet b)))
    (hc : Even (Nat.card (G.neighborSet c)))
    (haw : G.Adj w a) (hbw : G.Adj b w)
    (hnab : ¬G.Adj a b) (hnac : ¬G.Adj a c) (hnbc : ¬G.Adj b c)
    (hnwc : ¬G.Adj w c) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  apply sharp_independent_three_two_neighbors G a b c w hab hac hbc ?_
    haw hbw hnab hnac hnbc hnwc
  have hset := triple_even_set_of_card_three G hthree hab hac hbc ha hb hc
  intro x
  exact Set.ext_iff.mp hset x

end Erdos583IndependentThreeEvenSharpDevelopment
