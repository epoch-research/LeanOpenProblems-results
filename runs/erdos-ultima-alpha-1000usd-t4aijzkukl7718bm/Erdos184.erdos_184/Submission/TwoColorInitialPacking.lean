import Submission.CoveredPathParity

/-! Initial two-color endpoint packings.  The paths need not cover every edge;
completion with the color constraint is not asserted. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.TwoColor
open Erdos184Work.Vertex
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Each path has endpoints in the same one of the two color classes. -/
def Monochromatic (S : Finset V) (L : List (Piece G)) : Prop :=
  ∀ p ∈ L, p.src ∈ S ↔ p.dst ∈ S

omit [Fintype V] in
lemma edgeList_append (L M : List (Piece G)) :
    edgeList (L ++ M) = edgeList L ++ edgeList M := by
  simp only [edgeList,List.flatMap_append]

omit [Fintype V] in
lemma endpoints_append (L M : List (Piece G)) :
    endpoints (L ++ M) = endpoints L ++ endpoints M := by
  simp only [endpoints,List.flatMap_append]

omit [Fintype V] in
lemma endpoint_mem_of_piece {L : List (Piece G)} {p : Piece G} (hp : p ∈ L) :
    p.src ∈ endpoints L ∧ p.dst ∈ endpoints L := by
  constructor <;> apply List.mem_flatMap.mpr
  · exact ⟨p,hp,by simp⟩
  · exact ⟨p,hp,by simp⟩

/-- A parity forest for the first color, followed by extraction in its
complement, supplies the two compatible endpoint classes. -/
lemma exists_initial (hG : G.Preconnected)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v)))
    (S : Finset V) (hS : Even S.card) :
    ∃ L : List (Piece G), Admissible L ∧ Monochromatic S L := by
  obtain ⟨F,hFG,hFa,_,hFp⟩ := exists_parity_forest hG S hS
  have hFo (v : V) : v ∈ oddVertices F ↔ v ∈ S := by
    have h := hFp v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h
    simp only [mem_oddVertices,Nat.odd_iff]
    rw [h]
    split_ifs <;> simp_all
  let K := G \ F
  have hKG : K ≤ G := sdiff_le
  have hKo (v : V) : v ∈ oddVertices K ↔ v ∉ S := by
    have hd := degree_sdiff_add G F hFG v
    have hf := hFp v
    have hg := Nat.odd_iff.mp (hodd v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hf
    simp only [mem_oddVertices,Nat.odd_iff,K]
    by_cases hv : v ∈ S
    · rw [if_pos hv] at hf
      simp only [hv,not_true_eq_false,iff_false]
      omega
    · rw [if_neg hv] at hf
      simp only [hv,not_false_eq_true,iff_true]
      omega
  obtain ⟨A,hAe,hAv,hAc,hAt,_⟩ := forest_path_partition F hFa
  obtain ⟨B,R,hRK,hRe,hBe,hBv,hBc,hBd,hBt⟩ := exists_extraction K
  have hAt' (v : V) : v ∈ endpoints A ↔ v ∈ S := (hAt v).trans (hFo v)
  have hBt' (v : V) : v ∈ endpoints B ↔ v ∉ S := (hBt v).trans (hKo v)
  have heDis : (edgeList A).Disjoint (edgeList B) := by
    intro e heA heB
    have ha := (hAc e).mpr heA
    have hb := (hBc e).mpr (Or.inl heB)
    change e ∈ (G \ F).edgeSet at hb
    rw [SimpleGraph.edgeSet_sdiff] at hb
    exact hb.2 ha
  have hvDis : (endpoints A).Disjoint (endpoints B) := by
    intro v hvA hvB
    exact (hBt' v).mp hvB ((hAt' v).mp hvA)
  let A' := A.map (Piece.mapLe hFG)
  let B' := B.map (Piece.mapLe hKG)
  refine ⟨A' ++ B',?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · simpa only [edgeList_append,A',B',edgeList_mapLe] using hAe.append hBe heDis
    · simpa only [endpoints_append,A',B',endpoints_mapLe] using hAv.append hBv hvDis
    · intro v
      simp only [endpoints_append,A',B',endpoints_mapLe,List.mem_append,hAt',hBt']
      exact em _
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      have hv := endpoint_mem_of_piece hq
      exact iff_of_true ((hAt' _).mp hv.1) ((hAt' _).mp hv.2)
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      have hv := endpoint_mem_of_piece hq
      exact iff_of_false ((hBt' _).mp hv.1) ((hBt' _).mp hv.2)

/-- A maximum is taken only among color-respecting endpoint packings. -/
def ColorMaximal (S : Finset V) (L : List (Piece G)) : Prop :=
  Admissible L ∧ Monochromatic S L ∧
    ∀ M : List (Piece G), Admissible M → Monochromatic S M →
      (edgeList M).length ≤ (edgeList L).length

lemma exists_color_maximal (hG : G.Preconnected)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v)))
    (S : Finset V) (hS : Even S.card) :
    ∃ L : List (Piece G), ColorMaximal S L := by
  obtain ⟨L,hL,hC⟩ := exists_initial hG hodd S hS
  let P : ℕ → Prop := fun k => ∃ L : List (Piece G),
    Admissible L ∧ Monochromatic S L ∧ (edgeList L).length = k
  have hp : P (edgeList L).length := ⟨L,hL,hC,rfl⟩
  obtain ⟨M,hM,hCM,hm⟩ := Nat.findGreatest_spec (edgeList_length_le hL.1) hp
  refine ⟨M,hM,hCM,?_⟩
  intro N hN hCN
  rw [hm]
  exact Nat.le_findGreatest (edgeList_length_le hN.1) ⟨N,hN,hCN,rfl⟩

lemma ColorMaximal.path_count {S : Finset V} {L : List (Piece G)}
    (hL : ColorMaximal S L) : 2 * L.length = Fintype.card V := hL.1.path_count

lemma ColorMaximal.residual_even {S : Finset V} {L : List (Piece G)}
    (hL : ColorMaximal S L) (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∀ v, Even (Nat.card ((G \ coveredGraph L).neighborSet v)) :=
  by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      hL.1.residual_even hodd v

end Erdos184Work.OddPaths.TwoColor
#print axioms Erdos184Work.OddPaths.TwoColor.exists_initial
#print axioms Erdos184Work.OddPaths.TwoColor.exists_color_maximal
