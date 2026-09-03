import Submission.PairedSuppression

/-! Two distinct edges can always be separated by splitting one path, with
at most one additional member. This is not a same-budget separation theorem. -/
namespace Erdos583SeparateTwoEdgesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583SharedExpansionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V}

lemma two_separated_iff (D : Finset G.Subgraph) (e f : Sym2 V) :
    Separated D ![e,f] ↔ ∀ K ∈ D, ¬(e ∈ K.edgeSet ∧ f ∈ K.edgeSet) := by
  constructor
  · intro h K hK ⟨he,hf⟩
    have hh := h K hK 0 1 he hf
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  · intro h K hK i j hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · exact (h K hK ⟨hi,hj⟩).elim
    · exact (h K hK ⟨hj,hi⟩).elim
    · rfl

lemma split_path_two_edges {u v : V} (P : G.Walk u v) (hP : P.IsPath)
    (e f : Sym2 V) (hef : e ≠ f) (he : e ∈ P.edges) (hf : f ∈ P.edges) :
    ∃ L M : G.Subgraph, IsPathSubgraph L ∧ IsPathSubgraph M ∧
      Disjoint L.edgeSet M.edgeSet ∧ L.edgeSet ∪ M.edgeSet=P.toSubgraph.edgeSet ∧
      e ∈ L.edgeSet ∧ f ∈ M.edgeSet := by
  classical
  obtain ⟨a,b,hab,q,r,rfl,rfl⟩ := walk_split_at_edge P e he
  have hf' : f ∈ q.edges ∨ f ∈ r.edges := by
    simpa only [Walk.edges_append,Walk.edges_cons,List.mem_append,List.mem_cons,hef.symm,false_or] using hf
  rcases hf' with hfq|hfr
  · have hd := append_trail_disjoint hP.isTrail
    refine ⟨(Walk.cons hab r).toSubgraph,q.toSubgraph,
      ⟨_,_,_,hP.of_append_right,rfl⟩,⟨_,_,_,hP.of_append_left,rfl⟩,hd.symm,?_,?_,?_⟩
    · rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup,Set.union_comm]
    · rw [Walk.mem_edges_toSubgraph]; exact List.mem_cons_self
    · exact q.mem_edges_toSubgraph.mpr hfq
  · have hform : (q.concat hab).append r=q.append (Walk.cons hab r) := Walk.concat_append q hab r
    have hp : ((q.concat hab).append r).IsPath := hform.symm ▸ hP
    refine ⟨(q.concat hab).toSubgraph,r.toSubgraph,
      ⟨_,_,_,hp.of_append_left,rfl⟩,⟨_,_,_,hp.of_append_right,rfl⟩,append_trail_disjoint hp.isTrail,?_,?_,?_⟩
    · rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,hform]
    · simp only [Walk.mem_edges_toSubgraph,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton,or_true]
    · exact r.mem_edges_toSubgraph.mpr hfr

lemma split_member_two_edges (D : Finset G.Subgraph) (hD : GoodDecomposition G D)
    (K : G.Subgraph) (hK : K ∈ D) (e f : Sym2 V) (hef : e ≠ f)
    (he : e ∈ K.edgeSet) (hf : f ∈ K.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 ∧ Separated E ![e,f] := by
  classical
  obtain ⟨u,v,P,hP,hKP⟩ := hD.1 K hK
  have heP : e ∈ P.edges := P.mem_edges_toSubgraph.mp (hKP ▸ he)
  have hfP : f ∈ P.edges := P.mem_edges_toSubgraph.mp (hKP ▸ hf)
  obtain ⟨L,M,hL,hM,hLM,hcov,heL,hfM⟩ := split_path_two_edges P hP e f hef heP hfP
  rw [←hKP] at hcov
  have hLK : L.edgeSet ⊆ K.edgeSet := hcov ▸ Set.subset_union_left
  have hMK : M.edgeSet ⊆ K.edgeSet := hcov ▸ Set.subset_union_right
  have hLD (J) (hJ : J ∈ D.erase K) : Disjoint L.edgeSet J.edgeSet :=
    (hD.2.1 hK (Finset.mem_of_mem_erase hJ) (Finset.mem_erase.mp hJ).1.symm).mono_left hLK
  have hMD (J) (hJ : J ∈ D.erase K) : Disjoint M.edgeSet J.edgeSet :=
    (hD.2.1 hK (Finset.mem_of_mem_erase hJ) (Finset.mem_erase.mp hJ).1.symm).mono_left hMK
  let E := insert L (insert M (D.erase K))
  have hgood : GoodDecomposition G E := by
    refine ⟨?_,?_,?_⟩
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with hJ|hJ
      · exact hJ ▸ hL
      rcases Finset.mem_insert.mp hJ with hJ|hJ
      · exact hJ ▸ hM
      · exact hD.1 J (Finset.mem_of_mem_erase hJ)
    · dsimp only [E]
      rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
      constructor
      · rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
        constructor
        · intro J hJ Q hQ hJQ
          exact hD.2.1 (Finset.mem_of_mem_erase hJ) (Finset.mem_of_mem_erase hQ) hJQ
        · intro J hJ _; exact hMD J hJ
      · intro J hJ _
        rcases Finset.mem_insert.mp hJ with hJ|hJ
        · exact hJ ▸ hLM
        · exact hLD J hJ
    · ext z
      constructor
      · intro hz
        obtain ⟨J,hz⟩ := Set.mem_iUnion.mp hz
        obtain ⟨_,hz⟩ := Set.mem_iUnion.mp hz
        exact J.edgeSet_subset hz
      · intro hz
        have hzD := hD.2.2.symm ▸ hz
        obtain ⟨J,hzJ⟩ := Set.mem_iUnion.mp hzD
        obtain ⟨hJD,hzJ⟩ := Set.mem_iUnion.mp hzJ
        by_cases hJK : J=K
        · subst J
          rw [←hcov] at hzJ
          rcases hzJ with hzL|hzM
          · exact Set.mem_iUnion.mpr ⟨L,Set.mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,hzL⟩⟩
          · exact Set.mem_iUnion.mpr ⟨M,Set.mem_iUnion.mpr
              ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),hzM⟩⟩
        · exact Set.mem_iUnion.mpr ⟨J,Set.mem_iUnion.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hJK,hJD⟩)),hzJ⟩⟩
  refine ⟨E,hgood,?_,?_⟩
  · have h1 := Finset.card_insert_le L (insert M (D.erase K))
    have h2 := Finset.card_insert_le M (D.erase K)
    have h3 := Finset.card_erase_add_one hK
    dsimp only [E]
    omega
  · apply (two_separated_iff E e f).mpr
    intro J hJ ⟨heJ,hfJ⟩
    rcases Finset.mem_insert.mp hJ with hJ|hJ
    · subst J
      exact Set.disjoint_left.mp hLM hfJ hfM
    rcases Finset.mem_insert.mp hJ with hJ|hJ
    · subst J
      exact Set.disjoint_left.mp hLM heL heJ
    · exact Set.disjoint_left.mp
        (hD.2.1 hK (Finset.mem_of_mem_erase hJ) (Finset.mem_erase.mp hJ).1.symm) he heJ

lemma separate_two_edges (D : Finset G.Subgraph) (hD : GoodDecomposition G D)
    (e f : Sym2 V) (hef : e ≠ f) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 ∧ Separated E ![e,f] := by
  classical
  by_cases hs : Separated D ![e,f]
  · exact ⟨D,hD,Nat.le_succ _,hs⟩
  · have hh : ∃ K ∈ D, e ∈ K.edgeSet ∧ f ∈ K.edgeSet := by
      by_contra hn
      exact hs ((two_separated_iff D e f).mpr (fun K hK h ↦ hn ⟨K,hK,h⟩))
    obtain ⟨K,hK,he,hf⟩ := hh
    exact split_member_two_edges D hD K hK e f hef he hf

end Erdos583SeparateTwoEdgesDevelopment
