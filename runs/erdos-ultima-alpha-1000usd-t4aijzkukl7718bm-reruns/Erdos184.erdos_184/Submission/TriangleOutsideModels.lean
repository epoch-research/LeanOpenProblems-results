import Submission.TriangleOutsideClassification
import Submission.PaddedGraphEncoding

/-! Arbitrary finite graphs satisfying the triangle-outside budget have one of
six normalized encodings. The hypotheses here concern the outside graph itself. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.TriangleOutsideModels
open SmallGraphEncoding PaddedGraphEncoding
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma small_degree_vertex (G : SimpleGraph V) {n : ℕ}
    (hn : Fintype.card V = n) (hnpos : 0 < n)
    (hlo : ∀ v, 1 ≤ G.degree v)
    (he : G.edgeSet.ncard + 3 = 2*n) :
    ∃ (v : V) (d : ℕ), G.degree v = d ∧ 1 ≤ d ∧ d ≤ 3 ∧
      ∀ w, d ≤ G.degree w := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v,hv⟩ := G.exists_minimal_degree_vertex
  have hmin (w : V) : G.degree v ≤ G.degree w := by
    rw [← hv]
    exact G.minDegree_le_degree w
  refine ⟨v,G.degree v,rfl,hlo v,?_,hmin⟩
  by_contra! hd
  have hs : (∑ _v : V, 4) ≤ ∑ w : V, G.degree w := by
    apply Finset.sum_le_sum
    intro w _
    have := hmin w
    omega
  have hh := G.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hn] at hs
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  omega

lemma exists_normalized (G : SimpleGraph V) {n : ℕ}
    (hn : Fintype.card V = n) (hnlo : 2 ≤ n) (hnhi : n ≤ 6)
    (hlo : ∀ v, 1 ≤ G.degree v) (hhi : ∀ v, G.degree v ≤ 4)
    (he : G.edgeSet.ncard + 3 = 2*n) (hG : EvenCycleCore.NoTwoCycles G) :
    ∃ (d code : ℕ) (e : Fin n ≃ V),
      TriangleOutsideData.good d n code = true ∧
      graph 6 d code = G.map (e.symm.toEmbedding.trans (Fin.castLEEmb hnhi)) := by
  obtain ⟨v,d,hd,hdlo,hdhi,hdmin⟩ := small_degree_vertex G hn (by omega) hlo he
  obtain ⟨e,code,hcode,henc⟩ := exists_padded_encoding table6 G v hn hnhi hd
  let f := e.symm.toEmbedding.trans (Fin.castLEEmb hnhi)
  have hecount : (graph 6 d code).edgeSet.ncard = G.edgeSet.ncard := by
    rw [henc]
    simpa only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using card_edgeFinset_map f G
  have helig : TriangleOutsideData.eligible d n code = true := by
    simp only [TriangleOutsideData.eligible,Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro i hi
      have hi6 : i < 6 := List.mem_range.mp hi
      by_cases hin : i < n
      · rw [if_pos hin,decide_eq_true_eq]
        have hh := padded_degree G e hnhi ⟨i,hin⟩
        have hg := graph_degree 6 d code ⟨i,hi6⟩
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hg
        rw [henc] at hg
        have hl := hdmin (e ⟨i,hin⟩)
        have hu := hhi (e ⟨i,hin⟩)
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hg hl hu
        change Nat.card ((G.map f).neighborSet ⟨i,hi6⟩) =
          Nat.card (G.neighborSet (e ⟨i,hin⟩)) at hh
        change Nat.card ((G.map f).neighborSet ⟨i,hi6⟩) = degreeCode 6 d code i at hg
        rw [← hg,hh]
        exact ⟨hl,hu⟩
      · rw [if_neg hin,decide_eq_true_eq]
        have hh := padded_degree_outside G e hnhi ⟨i,hi6⟩ (by change n ≤ i; omega)
        have hg := graph_degree 6 d code ⟨i,hi6⟩
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hg
        rw [henc] at hg
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hg
        omega
    · rw [decide_eq_true_eq,sum_degreeCode,hecount]
      omega
  have hno : EvenCycleCore.NoTwoCycles (graph 6 d code) := by
    have hh := NoTwoCyclesTransport.map hG f
    rw [← henc] at hh
    exact hh
  refine ⟨d,code,e,?_,henc⟩
  exact TriangleOutsideData.classification d n code hdlo hdhi hnlo hnhi
    (by simpa using hcode) helig hno

end Erdos184.TriangleOutsideModels
