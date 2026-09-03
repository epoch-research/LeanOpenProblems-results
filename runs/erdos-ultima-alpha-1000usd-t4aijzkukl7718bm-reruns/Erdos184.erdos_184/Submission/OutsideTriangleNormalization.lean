import Submission.TriangleOutsideModels

/-! Normalization of the graph outside an induced triangle under the
four-regularity and no-two-cycles hypotheses. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.OutsideTriangleNormalization
open HighGirthCritical EvenCycleCore SmallGraphEncoding
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

omit [Fintype V] in
lemma induce_outside_eq (G : SimpleGraph V) (S : Set V) :
    (avoid G S).induce (G.support \ S) = G.induce (G.support \ S) := by
  ext x y
  exact ⟨fun h => h.1,fun h => ⟨h,x.property.2,y.property.2⟩⟩

lemma outside_induce_degree (G : SimpleGraph V) (S : Set V) (x : ↥(G.support \ S)) :
    (G.induce (G.support \ S)).degree x = (avoid G S).degree x.val := by
  have hh := degree_induce_of_support_subset (avoid_support_subset G S) x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  rwa [induce_outside_eq] at hh

lemma outside_induce_edges (G : SimpleGraph V) (S : Set V) :
    (G.induce (G.support \ S)).edgeSet.ncard = (avoid G S).edgeSet.ncard := by
  have hh := card_edgeFinset_induce_of_support_subset (avoid_support_subset G S)
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  rwa [induce_outside_eq] at hh

lemma outside_induce_no_two (G : SimpleGraph V) (S : Set V)
    (hout : NoTwoCycles (avoid G S)) : NoTwoCycles (G.induce (G.support \ S)) := by
  let φ : G.induce (G.support \ S) →g avoid G S :=
    ⟨Subtype.val,fun {x y} h => ⟨h,x.property.2,y.property.2⟩⟩
  have hh := NoTwoCyclesTransport.of_injective_hom hout φ Subtype.val_injective
  intro P Q hp hq hd
  apply hh P Q ⟨hp.1,?_⟩ ⟨hq.1,?_⟩ hd
  · intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hp.2 v
  · intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hq.2 v

lemma triangle_outside_data {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) (htri : C.verts.ncard = 3)
    (hout : NoTwoCycles (avoid G C.verts)) :
    let A := G.induce (G.support \ C.verts)
    let n := (G.support \ C.verts).ncard
    2 ≤ n ∧ n ≤ 6 ∧ (∀ v, 1 ≤ A.degree v ∧ A.degree v ≤ 4) ∧
      A.edgeSet.ncard + 3 = 2*n := by
  dsimp only
  have hCsup := CriticalOutsideCycles.cycle_verts_in_support C hc.2
  have hs := CountThreeOrder.support_bound_from_cycle hfour C hc hout
  have hn := Set.ncard_diff_add_ncard_of_subset hCsup
  have he := CycleOutsideBudget.outside_edges_formula hfour C hc hind
  rw [htri] at he hs hn
  have hem := outside_induce_edges G C.verts
  refine ⟨by omega,by omega,?_,by omega⟩
  intro v
  have hd := degree_avoid_add_lost G C.verts v.property.2
  have h4 := hfour v.val v.property.1
  have hl : (G.neighborSet v.val ∩ C.verts).ncard ≤ 3 := by
    rw [← htri]
    exact Set.ncard_le_ncard Set.inter_subset_right
  have hI := outside_induce_degree G C.verts v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd h4 hI ⊢
  exact ⟨by omega,by omega⟩

lemma triangle_outside_normalized {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) (htri : C.verts.ncard = 3)
    (hout : NoTwoCycles (avoid G C.verts)) :
    ∃ (n d code : ℕ) (hn : n ≤ 6) (e : Fin n ≃ ↥(G.support \ C.verts)),
      TriangleOutsideData.good d n code = true ∧
      graph 6 d code = (G.induce (G.support \ C.verts)).map
        (e.symm.toEmbedding.trans (Fin.castLEEmb hn)) := by
  obtain ⟨hlo,hhi,hdeg,he⟩ := triangle_outside_data hfour C hc hind htri hout
  have hcard : Fintype.card ↥(G.support \ C.verts) = (G.support \ C.verts).ncard := by
    simp only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨d,code,e,hgood,henc⟩ := TriangleOutsideModels.exists_normalized
    (G.induce (G.support \ C.verts)) hcard hlo hhi
    (fun v => (hdeg v).1) (fun v => (hdeg v).2) he (outside_induce_no_two G C.verts hout)
  exact ⟨_,d,code,hhi,e,hgood,henc⟩

end Erdos184.OutsideTriangleNormalization
