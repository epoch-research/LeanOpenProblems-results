import Submission.SmallGraphTailBound
import Submission.OutsideQuadrilateralData
import Submission.QuadrilateralSevenClassification

/-! Arbitrary quadrilateral-outside graphs admit a checked single-root model. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.QuadrilateralOutsideModels
open SmallGraphEncoding PaddedGraphEncoding
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

omit [Fintype V] in
lemma trianglefree_map {W : Type*} (G : SimpleGraph V) (f : V ↪ W)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    ∀ u v w, (G.map f).Adj u v → (G.map f).Adj v w → (G.map f).Adj w u → False := by
  intro u v w huv hvw hwu
  obtain ⟨x,y,hxy,rfl,rfl⟩ := huv
  obtain ⟨y',z,hyz,hy',rfl⟩ := hvw
  have hyy := f.injective hy'
  subst y'
  exact htri x y z hxy hyz (map_adj_apply.mp hwu)

lemma eligible_of_conditions (n code : ℕ)
    (hdeg : ∀ i : Fin 7, if i.val < n then
      2 ≤ (graph 7 2 code).degree i ∧ (graph 7 2 code).degree i ≤ 3
      else (graph 7 2 code).degree i = 0)
    (he : (graph 7 2 code).edgeSet.ncard + 4 = 2*n)
    (htri : ∀ u v w, (graph 7 2 code).Adj u v →
      (graph 7 2 code).Adj v w → (graph 7 2 code).Adj w u → False) :
    QuadrilateralOutsideData.eligible n code = true := by
  simp only [QuadrilateralOutsideData.eligible,Bool.and_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [List.all_eq_true]
    intro i hi
    have hh := hdeg ⟨i,List.mem_range.mp hi⟩
    simp only [graph_degree,degreeCode_two] at hh
    split_ifs with hin
    · rw [decide_eq_true_eq]
      simpa only [Fin.val_mk,if_pos hin] using hh
    · rw [decide_eq_true_eq]
      simpa only [Fin.val_mk,if_neg hin] using hh
  · rw [decide_eq_true_eq]
    change ((List.range 7).map (degreeCode 7 2 code)).sum = 4*n-8
    rw [sum_degreeCode]
    omega
  · simp only [List.all_eq_true]
    intro i hi j hj k hk
    rw [Bool.not_eq_true',Bool.eq_false_iff]
    intro ha
    simp only [Bool.and_eq_true] at ha
    exact htri ⟨i,List.mem_range.mp hi⟩ ⟨j,List.mem_range.mp hj⟩
      ⟨k,List.mem_range.mp hk⟩ ha.1.1 ha.1.2 ha.2

lemma classified (n code : ℕ) (hnlo : 4 ≤ n) (hnhi : n ≤ 7) (hc : code < 32768)
    (he : QuadrilateralOutsideData.eligible n code = true) :
    code ∈ QuadrilateralOutsideData.patterns n := by
  have hzero : ∀ i : Fin 7, n ≤ i.val → (graph 7 2 code).degree i = 0 := by
    intro i hi
    have hh := he
    simp only [QuadrilateralOutsideData.eligible,Bool.and_eq_true] at hh
    have hz := List.all_eq_true.mp hh.1.1 i.val (List.mem_range.mpr i.isLt)
    rw [if_neg (by omega),decide_eq_true_eq] at hz
    simpa only [graph_degree,degreeCode_two] using hz
  have hb := SmallGraphTailBound.tail_bound code n hnhi hc hzero
  interval_cases n
  · exact QuadrilateralOutsideData.checked_4 ⟨code,by norm_num at hb; exact hb⟩ he
  · exact QuadrilateralOutsideData.checked_5 ⟨code,by norm_num at hb; exact hb⟩ he
  · exact QuadrilateralOutsideData.checked_6 ⟨code,by norm_num at hb; exact hb⟩ he
  · exact QuadrilateralOutsideData.checked_7_single_root ⟨code,hc⟩ he

lemma exists_normalized (G : SimpleGraph V) {n : ℕ}
    (hn : Fintype.card V = n) (hnlo : 4 ≤ n) (hnhi : n ≤ 7)
    (hlo : ∀ v, 2 ≤ G.degree v) (hhi : ∀ v, G.degree v ≤ 3)
    (he : G.edgeSet.ncard + 4 = 2*n)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    ∃ (code : ℕ) (e : Fin n ≃ V),
      code ∈ QuadrilateralOutsideData.patterns n ∧
      graph 7 2 code = G.map (e.symm.toEmbedding.trans (Fin.castLEEmb hnhi)) := by
  obtain ⟨v,hv⟩ := OutsideQuadrilateralData.degree_two_vertex G hn hnhi hlo he
  obtain ⟨e,code,hcode,henc⟩ := exists_padded_encoding table7 G v hn hnhi hv
  let f := e.symm.toEmbedding.trans (Fin.castLEEmb hnhi)
  have hecount : (graph 7 2 code).edgeSet.ncard = G.edgeSet.ncard := by
    rw [henc]
    simpa only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using card_edgeFinset_map f G
  have hdeg : ∀ i : Fin 7, if i.val < n then
      2 ≤ (graph 7 2 code).degree i ∧ (graph 7 2 code).degree i ≤ 3
      else (graph 7 2 code).degree i = 0 := by
    intro i
    split_ifs with hin
    · have hh := padded_degree G e hnhi ⟨i.val,hin⟩
      have hl := hlo (e ⟨i.val,hin⟩)
      have hu := hhi (e ⟨i.val,hin⟩)
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hl hu ⊢
      rw [henc]
      change Nat.card ((G.map f).neighborSet i) = Nat.card (G.neighborSet (e ⟨i.val,hin⟩)) at hh
      rw [hh]
      exact ⟨hl,hu⟩
    · have hh := padded_degree_outside G e hnhi i (by omega)
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
      rwa [henc]
  have ht : ∀ u v w, (graph 7 2 code).Adj u v →
      (graph 7 2 code).Adj v w → (graph 7 2 code).Adj w u → False := by
    rw [henc]
    exact trianglefree_map G f htri
  have helig := eligible_of_conditions n code hdeg (by omega) ht
  exact ⟨code,e,classified n code hnlo hnhi (by simpa using hcode) helig,henc⟩

end Erdos184.QuadrilateralOutsideModels
