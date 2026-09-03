import Submission.AttachmentColumns

/-! Row counts and validity for actual attachments to a fixed model. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.AttachmentRows
open CountThreeAttachmentData AttachmentModelFacts AttachmentColumns
set_option maxHeartbeats 1000000

noncomputable def row (G : SimpleGraph (Fin 11)) (m : Model) (c : Fin 4) : Finset ℕ :=
  (Finset.range m.outsideOrder).filter (fun j => c ∈ column G m j)

lemma cycle_neighbors (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    (hsupp : ∀ v ∈ G.support, v.val < (model i).girth + (model i).outsideOrder)
    {c : Fin 4} (hc : c.val < (model i).girth) :
    G.neighborFinset (cycleVertex c) = baseNeighbors (model i) (cycleVertex c) ∪
      (row G (model i) c).image (outsideVertex (model i)) := by
  have hcv : (cycleVertex c).val < (model i).girth := by rwa [cycleVertex_val]
  ext w
  simp only [mem_neighborFinset,Finset.mem_union,baseNeighbors,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · intro ha
    by_cases hw : w.val < (model i).girth
    · exact Or.inl ((hbase _ _ (by simp only [hcv,hw])).mp ha)
    · have hws := hsupp w ⟨cycleVertex c,ha.symm⟩
      let j := w.val - (model i).girth
      have hj : j < (model i).outsideOrder := by dsimp only [j]; omega
      have heq : outsideVertex (model i) j = w := by
        apply Fin.ext
        rw [outsideVertex_val i hj]
        dsimp only [j]
        omega
      refine Or.inr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,?_⟩,heq⟩
      apply (mem_column G (model i) j c).mpr
      exact ⟨hc,heq.symm ▸ ha⟩
  · rintro (h | ⟨j,hj,rfl⟩)
    · exact (hbase _ _ (base_same_side i _ _ h)).mpr h
    · exact ((mem_column G (model i) j c).mp (Finset.mem_filter.mp hj).2).2

lemma cycle_neighbors_disjoint (i : Fin 12) (G : SimpleGraph (Fin 11))
    {c : Fin 4} (hc : c.val < (model i).girth) :
    Disjoint (baseNeighbors (model i) (cycleVertex c))
      ((row G (model i) c).image (outsideVertex (model i))) := by
  apply Finset.disjoint_left.mpr
  intro w hw hr
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
  have hj' : j < (model i).outsideOrder := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hh := (base_same_side i _ _ (Finset.mem_filter.mp hw).2).mp (by rwa [cycleVertex_val])
  rw [outsideVertex_val i hj'] at hh
  omega

lemma cycle_degree (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    (hsupp : ∀ v ∈ G.support, v.val < (model i).girth + (model i).outsideOrder)
    {c : Fin 4} (hc : c.val < (model i).girth) :
    2 + (row G (model i) c).card = G.degree (cycleVertex c) := by
  have hh := congrArg Finset.card (cycle_neighbors i G hbase hsupp hc)
  have hinj : Set.InjOn (outsideVertex (model i)) (row G (model i) c : Set ℕ) := by
    intro j hj k hk heq
    have hj' : j ∈ Finset.range (model i).outsideOrder := (Finset.mem_filter.mp hj).1
    have hk' : k ∈ Finset.range (model i).outsideOrder := (Finset.mem_filter.mp hk).1
    exact outsideVertex_injOn i hj' hk' heq
  rw [Finset.card_union_of_disjoint (cycle_neighbors_disjoint i G hc),
    Finset.card_image_of_injOn hinj,base_cycle_degree i c hc] at hh
  simpa only [card_neighborFinset_eq_degree] using hh.symm

lemma countP_range (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = ((Finset.range n).filter (fun j => p j = true)).card := by
  rw [List.countP_eq_length_filter]
  have hh := List.toFinset_card_of_nodup ((List.nodup_range : (List.range n).Nodup).filter p)
  simpa only [List.toFinset_filter,List.toFinset_range] using hh.symm

lemma config_row_count (G : SimpleGraph (Fin 11)) (m : Model) (c : Fin 4) :
    (config G m).countP (fun s => decide (c ∈ s)) = (row G m c).card := by
  simp only [config,List.countP_map]
  rw [countP_range]
  congr 1
  ext j
  simp only [row,Finset.mem_filter,Finset.mem_range,Function.comp_apply,decide_eq_true_eq]

lemma config_valid (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    (hsupp : ∀ v ∈ G.support, v.val < (model i).girth + (model i).outsideOrder)
    (hfour : ∀ v, v.val < (model i).girth + (model i).outsideOrder → G.degree v = 4)
    (htri : (model i).girth = 4 → ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    valid (model i) (config G (model i)) = true := by
  rw [valid,Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro c hc
    have hc' : c < (model i).girth := List.mem_range.mp hc
    have hb := model_bounds i
    let c' : Fin 4 := ⟨c,by omega⟩
    have hceq : Fin.ofNat 4 c = c' := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [decide_eq_true_eq,hceq,config_row_count]
    have hh := cycle_degree i G hbase hsupp (c := c') hc'
    have h4 := hfour (cycleVertex c') (by rw [cycleVertex_val]; dsimp only [c']; omega)
    omega
  · split_ifs with hquad
    · rw [List.all_eq_true]
      intro e he
      obtain ⟨he1,he2,hedge⟩ := outside_pair_data i e he
      rw [decide_eq_true_eq,config_getD G (model i) he1,config_getD G (model i) he2]
      apply Finset.disjoint_left.mpr
      intro c hc hd
      have hc' := ((mem_column G (model i) e.1 c).mp hc).2
      have hd' := ((mem_column G (model i) e.2 c).mp hd).2
      have hab : G.Adj (outsideVertex (model i) e.1) (outsideVertex (model i) e.2) :=
        (hbase _ _ (base_same_side i _ _ hedge)).mpr hedge
      exact htri hquad (cycleVertex c) (outsideVertex (model i) e.1)
        (outsideVertex (model i) e.2) hc' hab hd'.symm
    · rfl

end Erdos184.AttachmentRows
