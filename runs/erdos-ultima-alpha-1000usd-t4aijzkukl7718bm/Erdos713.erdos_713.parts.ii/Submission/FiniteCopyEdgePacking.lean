import FormalConjecturesUtil

/-! A finite maximal edge-disjoint packing of copies leaves a free remainder.
No quantitative extremal-rate inference is part of this lemma. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713FiniteCopyEdgePacking
variable {W V : Type*} [Fintype W] [Fintype V]
set_option maxHeartbeats 1000000

/-- An edge set supporting one injective, not necessarily induced, copy. -/
def CopyEdges (H : SimpleGraph W) (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  ∃ f : Copy H G, (H.map f.toEmbedding).edgeFinset = E

noncomputable def used (F : Finset (Finset (Sym2 V))) : Finset (Sym2 V) := F.biUnion id

def Packing (H : SimpleGraph W) (G : SimpleGraph V)
    (F : Finset (Finset (Sym2 V))) : Prop :=
  (∀ E ∈ F, CopyEdges H G E) ∧ (F : Set (Finset (Sym2 V))).PairwiseDisjoint id

omit [Fintype W] [Fintype V] in
lemma copy_map_le {H : SimpleGraph W} {G : SimpleGraph V} (f : Copy H G) :
    H.map f.toEmbedding ≤ G := by
  rw [map_le_iff_le_comap]
  exact fun _ _ h => f.toHom.map_rel' h

lemma copyEdges_card {H : SimpleGraph W} {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (h : CopyEdges H G E) : E.card = H.edgeFinset.card := by
  obtain ⟨f,rfl⟩ := h
  exact card_edgeFinset_map f.toEmbedding H

lemma copyEdges_subset {H : SimpleGraph W} {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (h : CopyEdges H G E) : E ⊆ G.edgeFinset := by
  obtain ⟨f,rfl⟩ := h
  exact edgeFinset_subset_edgeFinset.mpr (copy_map_le f)

lemma copyEdges_mono {H : SimpleGraph W} {G J : SimpleGraph V} {E : Finset (Sym2 V)}
    (hJG : J ≤ G) (h : CopyEdges H J E) : CopyEdges H G E := by
  obtain ⟨f,hf⟩ := h
  refine ⟨(Copy.ofLE J G hJG).comp f, ?_⟩
  exact hf

lemma packing_empty (H : SimpleGraph W) (G : SimpleGraph V) : Packing H G ∅ := by
  simp [Packing]

/-- The remainder after deleting a maximal packing is H-free. The deletion
cost is at most the number of packed copies times the number of edges of H. -/
theorem exists_packing (H : SimpleGraph W) (hEdge : 0 < H.edgeFinset.card)
    (G : SimpleGraph V) :
    ∃ F : Finset (Finset (Sym2 V)), Packing H G F ∧
      H.Free (G.deleteEdges (used F : Set (Sym2 V))) ∧
      G.edgeFinset.card ≤ (G.deleteEdges (used F : Set (Sym2 V))).edgeFinset.card +
        H.edgeFinset.card*F.card := by
  let P : Finset (Finset (Finset (Sym2 V))) := univ.filter (Packing H G)
  have hP : P.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_univ _,packing_empty H G⟩⟩
  obtain ⟨F,hFP,hmax⟩ := P.exists_max_image Finset.card hP
  have hF : Packing H G F := (mem_filter.mp hFP).2
  let U : Finset (Sym2 V) := used F
  let J := G.deleteEdges (U : Set (Sym2 V))
  have hfree : H.Free J := by
    rintro ⟨f⟩
    let E := (H.map f.toEmbedding).edgeFinset
    have hEJ : CopyEdges H J E := ⟨f,rfl⟩
    have hE : CopyEdges H G E := copyEdges_mono (deleteEdges_le _) hEJ
    have hEU : ∀ e ∈ E, e ∉ U := by
      intro e he
      have hh : e ∈ J.edgeSet := by
        simpa only [mem_edgeFinset] using (copyEdges_subset hEJ he)
      rw [show J = G.deleteEdges (U : Set (Sym2 V)) from rfl,edgeSet_deleteEdges] at hh
      exact hh.2
    have hnot : E ∉ F := by
      intro hEF
      have hpos : E.Nonempty := card_pos.mp (by rwa [copyEdges_card hE])
      obtain ⟨e,he⟩ := hpos
      exact hEU e he (mem_biUnion.mpr ⟨E,hEF,he⟩)
    have hd (B : Finset (Sym2 V)) (hBF : B ∈ F) : Disjoint E B := by
      apply Finset.disjoint_left.mpr
      intro e he hB
      exact hEU e he (mem_biUnion.mpr ⟨B,hBF,hB⟩)
    have hnew : Packing H G (insert E F) := by
      refine ⟨?_,?_⟩
      · intro B hB
        rcases mem_insert.mp hB with rfl|hB
        · exact hE
        · exact hF.1 B hB
      · simpa only [coe_insert] using hF.2.insert_of_notMem hnot hd
    have hm := hmax (insert E F) (mem_filter.mpr ⟨mem_univ _,hnew⟩)
    rw [card_insert_of_notMem hnot] at hm
    omega
  have hU : U.card ≤ H.edgeFinset.card*F.card := by
    calc
      _ ≤ ∑ E ∈ F, E.card := card_biUnion_le
      _ = ∑ _E ∈ F, H.edgeFinset.card := sum_congr rfl (fun E hE => copyEdges_card (hF.1 E hE))
      _ = _ := by simp [Nat.mul_comm]
  have hsub : U ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨E,hEF,heE⟩ := mem_biUnion.mp he
    exact copyEdges_subset (hF.1 E hEF) heE
  have hcount : J.edgeFinset.card + U.card = G.edgeFinset.card := by
    have hh := card_sdiff_add_card_inter G.edgeFinset U
    rw [inter_eq_right.mpr hsub] at hh
    simpa only [J,← edgeFinset_deleteEdges] using hh
  refine ⟨F,hF,hfree,?_⟩
  change G.edgeFinset.card ≤ J.edgeFinset.card + H.edgeFinset.card*F.card
  omega

#print axioms exists_packing
end Erdos713FiniteCopyEdgePacking
