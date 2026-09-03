import Submission.AttachmentModelFacts

/-! Interpreting the attachment columns of a labeled graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.AttachmentColumns
open CountThreeAttachmentData AttachmentModelFacts
set_option maxHeartbeats 1000000

noncomputable def column (G : SimpleGraph (Fin 11)) (m : Model) (j : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun c => c.val < m.girth ∧ G.Adj (cycleVertex c) (outsideVertex m j))

noncomputable def config (G : SimpleGraph (Fin 11)) (m : Model) : List (Finset (Fin 4)) :=
  (List.range m.outsideOrder).map (column G m)

lemma mem_column (G : SimpleGraph (Fin 11)) (m : Model) (j : ℕ) (c : Fin 4) :
    c ∈ column G m j ↔ c.val < m.girth ∧ G.Adj (cycleVertex c) (outsideVertex m j) := by
  simp only [column,Finset.mem_filter,Finset.mem_univ,true_and]

lemma config_length (G : SimpleGraph (Fin 11)) (m : Model) :
    (config G m).length = m.outsideOrder := by simp [config]

lemma config_getD (G : SimpleGraph (Fin 11)) (m : Model) {j : ℕ} (hj : j < m.outsideOrder) :
    (config G m).getD j ∅ = column G m j := by
  rw [List.getD_eq_getElem _ _ (by simpa [config] using hj)]
  simp only [config,List.getElem_map,List.getElem_range]

lemma cycleVertex_val (c : Fin 4) : (cycleVertex c).val = c.val := by
  simp only [cycleVertex,Fin.val_ofNat,Nat.mod_eq_of_lt (by have := c.isLt; omega : c.val < 11)]

lemma cycleVertex_injective : Function.Injective cycleVertex := by
  intro c d h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simpa only [cycleVertex_val] using hh

lemma outsideVertex_val (i : Fin 12) {j : ℕ} (hj : j < (model i).outsideOrder) :
    (outsideVertex (model i) j).val = (model i).girth+j := by
  have hb := model_bounds i
  simp only [outsideVertex,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : (model i).girth+j < 11)]

lemma outsideVertex_injOn (i : Fin 12) :
    Set.InjOn (outsideVertex (model i)) (Finset.range (model i).outsideOrder) := by
  intro j hj k hk h
  have hj' := Finset.mem_range.mp hj
  have hk' := Finset.mem_range.mp hk
  have hh := congrArg Fin.val h
  rw [outsideVertex_val i hj',outsideVertex_val i hk'] at hh
  omega

lemma outside_neighbors (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    {j : ℕ} (hj : j < (model i).outsideOrder) :
    G.neighborFinset (outsideVertex (model i) j) =
      baseNeighbors (model i) (outsideVertex (model i) j) ∪
        (column G (model i) j).image cycleVertex := by
  have hb := model_bounds i
  have hv := outsideVertex_val i hj
  have hnot : ¬(outsideVertex (model i) j).val < (model i).girth := by omega
  ext w
  simp only [mem_neighborFinset,Finset.mem_union,baseNeighbors,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · intro hadj
    by_cases hw : w.val < (model i).girth
    · let c : Fin 4 := ⟨w.val,by omega⟩
      have hcw : cycleVertex c = w := Fin.ext (cycleVertex_val c)
      right
      refine ⟨c,(mem_column G (model i) j c).mpr ⟨hw,?_⟩,hcw⟩
      rw [hcw]
      exact hadj.symm
    · exact Or.inl ((hbase _ _ (by simp only [hnot,hw])).mp hadj)
  · rintro (h | ⟨c,hc,rfl⟩)
    · exact (hbase _ _ (base_same_side i _ _ h)).mpr h
    · exact ((mem_column G (model i) j c).mp hc).2.symm

lemma outside_neighbors_disjoint (i : Fin 12) (G : SimpleGraph (Fin 11))
    {j : ℕ} (hj : j < (model i).outsideOrder) :
    Disjoint (baseNeighbors (model i) (outsideVertex (model i) j))
      ((column G (model i) j).image cycleVertex) := by
  apply Finset.disjoint_left.mpr
  intro w hw hc
  obtain ⟨c,hcm,rfl⟩ := Finset.mem_image.mp hc
  have hcol := ((mem_column G (model i) j c).mp hcm).1
  have hbase := (Finset.mem_filter.mp hw).2
  have hh := (base_same_side i _ _ hbase).mpr (by rwa [cycleVertex_val])
  rw [outsideVertex_val i hj] at hh
  omega

lemma outside_degree (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    {j : ℕ} (hj : j < (model i).outsideOrder) :
    (baseNeighbors (model i) (outsideVertex (model i) j)).card +
      (column G (model i) j).card = G.degree (outsideVertex (model i) j) := by
  have hh := congrArg Finset.card (outside_neighbors i G hbase hj)
  rw [Finset.card_union_of_disjoint (outside_neighbors_disjoint i G hj),
    Finset.card_image_of_injective _ cycleVertex_injective] at hh
  simpa only [card_neighborFinset_eq_degree] using hh.symm

lemma column_allowed (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    (hfour : ∀ v, v.val < (model i).girth + (model i).outsideOrder → G.degree v = 4)
    (htri : (model i).girth = 4 → ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    {j : ℕ} (hj : j < (model i).outsideOrder) :
    column G (model i) j ∈ (model i).options.getD j [] := by
  have hb := model_bounds i
  apply options_complete i ⟨j,by omega⟩ (column G (model i) j) hj
  · intro c hc
    exact ((mem_column G (model i) j c).mp hc).1
  · rw [outside_degree i G hbase hj]
    apply hfour
    rw [outsideVertex_val i hj]
    omega
  · intro hquad c hc d hd hedge
    have hc' := (mem_column G (model i) j c).mp hc
    have hd' := (mem_column G (model i) j d).mp hd
    have hcd : G.Adj (cycleVertex c) (cycleVertex d) :=
      (hbase _ _ (by simp only [cycleVertex_val,hc'.1,hd'.1])).mpr hedge
    exact htri hquad (outsideVertex (model i) j) (cycleVertex c) (cycleVertex d)
      hc'.2.symm hcd hd'.2

lemma config_choices (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    (hfour : ∀ v, v.val < (model i).girth + (model i).outsideOrder → G.degree v = 4)
    (htri : (model i).girth = 4 → ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    List.Forall₂ (fun x xs => x ∈ xs) (config G (model i)) (model i).options := by
  apply List.forall₂_iff_get.mpr
  refine ⟨(config_length G (model i)).trans (options_length i).symm,?_⟩
  intro j hj hk
  have hj' : j < (model i).outsideOrder := by rwa [config_length] at hj
  have hh := column_allowed i G hbase hfour htri hj'
  rw [← config_getD G (model i) hj',List.getD_eq_getElem _ _ hj,
    List.getD_eq_getElem _ _ hk] at hh
  exact hh

end Erdos184.AttachmentColumns
