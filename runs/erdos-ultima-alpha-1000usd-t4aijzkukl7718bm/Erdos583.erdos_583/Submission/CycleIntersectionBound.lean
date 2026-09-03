import Submission.Work

/-! Absorbing a cycle that meets a path in at most four vertices. -/
namespace Erdos583CycleIntersectionBoundDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.TriangleAbsorption
open Erdos583Work.BridgeGlue Erdos583Work.PentagonIntersection
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma missing_ear_reduction {a b r u v : V} (hru : G.Adj r u) (hvr : G.Adj v r)
    (R : G.Walk u v) (hRlen : 2 ≤ R.length)
    (hc : (Walk.cons hru (R.concat hvr)).IsCycle)
    (P : G.Walk a b) (hp : P.IsPath) (hrP : r ∉ P.support)
    (hinter : ∃ x ∈ P.support, x ∈ (Walk.cons hru (R.concat hvr)).support)
    (hd : Disjoint (Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hsmall : ((Walk.cons hru (R.concat hvr)).toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 4)
    (ih : ∀ (H : SimpleGraph V) {s a' b' : V} (C' : H.Walk s s) (P' : H.Walk a' b'),
      C'.IsCycle → P'.IsPath → C'.length < R.length+2 →
      (C'.toSubgraph.verts ∩ P'.toSubgraph.verts).ncard ≤ 4 →
      (∃ x ∈ P'.support, x ∈ C'.support) →
      Disjoint C'.toSubgraph.edgeSet P'.toSubgraph.edgeSet →
      TwoPathCover (G := H) (C'.toSubgraph.edgeSet ∪ P'.toSubgraph.edgeSet)) :
    TwoPathCover (G := G)
      ((Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  classical
  let C := Walk.cons hru (R.concat hvr)
  have hRc : (R.concat hvr).IsPath := (Walk.cons_isCycle_iff _ hru).mp hc |>.1
  have hRp : R.IsPath := (Walk.concat_isPath_iff hvr).mp hRc |>.1
  have hrR : r ∉ R.support := (Walk.concat_isPath_iff hvr).mp hRc |>.2
  have huv : u ≠ v := by
    intro hh
    subst v
    have hnil := (Walk.isPath_iff_eq_nil R).mp hRp
    simp [hnil] at hRlen
  have heR : s(u,v) ∉ R.edges := fun hh ↦ by
    have hh' := endpoint_edge_forces_length_one R hRp hh
    omega
  have hdR : Disjoint R.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    apply Set.disjoint_left.mp hd _ hf
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_concat,List.mem_cons,
      List.concat_eq_append,List.mem_append]
    exact Or.inr (Or.inl (R.mem_edges_toSubgraph.mp he))
  have hCe : C.toSubgraph.edgeSet={s(u,r),s(r,v)} ∪ R.toSubgraph.edgeSet := by
    ext e
    simp only [C,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_concat,List.mem_cons,
      List.concat_eq_append,List.mem_append,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := r) (b := u),Sym2.eq_swap (a := v) (b := r)]
    tauto
  by_cases heP : s(u,v) ∈ P.edges
  · have huvG : G.Adj u v := P.edges_subset_edgeSet heP
    obtain ⟨hc',Q,hQ,hsep,hcover,hlen⟩ :=
      CycleEar.cycle_ear_exchange hru hvr R hc P hp huvG heP hrP hd
    have hrC' : r ∉ (Walk.cons huvG R.reverse).support := by
      simp only [Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse,not_or]
      exact ⟨hru.ne,hrR⟩
    have huQ : u ∈ Q.support := by
      have he : s(r,u) ∈ (Walk.cons huvG R.reverse).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet := by
        rw [hcover]
        left
        simp
      rcases he with he|he
      · exact (hrC' (Walk.mem_support_of_mem_edges
          ((Walk.cons huvG R.reverse).mem_edges_toSubgraph.mp he) (by simp))).elim
      · exact Walk.mem_support_of_mem_edges (Q.mem_edges_toSubgraph.mp he) (by simp)
    have hsmall' : ((Walk.cons huvG R.reverse).toSubgraph.verts ∩ Q.toSubgraph.verts).ncard ≤ 4 := by
      apply (Set.ncard_le_ncard (s := (Walk.cons huvG R.reverse).toSubgraph.verts ∩ Q.toSubgraph.verts)
        (t := C.toSubgraph.verts ∩ P.toSubgraph.verts) ?_).trans hsmall
      intro z hz
      have hzC' : z ∈ (Walk.cons huvG R.reverse).support := by simpa only [Walk.mem_verts_toSubgraph] using hz.1
      have hzQ : z ∈ Q.support := by simpa only [Walk.mem_verts_toSubgraph] using hz.2
      have hzr : z ≠ r := fun hh ↦ hrC' (hh ▸ hzC')
      have hzR : z ∈ R.support := by
        rcases (show z=u ∨ z ∈ R.support by simpa only [Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse] using hzC') with rfl|hz
        · exact R.start_mem_support
        · exact hz
      have hzC : z ∈ C.toSubgraph.verts := by
        simp only [C,Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_concat,
          List.mem_cons,List.concat_eq_append,List.mem_append]
        exact Or.inr (Or.inl hzR)
      refine ⟨hzC,?_⟩
      rw [Walk.mem_verts_toSubgraph]
      rcases Walk.mem_support_iff_exists_mem_edges.mp hzQ with rfl|⟨e,heQ,hze⟩
      · exact P.end_mem_support
      · have hE : e ∈ C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := by
          rw [←hcover]; exact Or.inr (Q.mem_edges_toSubgraph.mpr heQ)
        rcases hE with hEC|hEP
        · rw [hCe] at hEC
          rcases hEC with hEar|hER
          · rcases (show e=s(u,r) ∨ e=s(r,v) by simpa using hEar) with rfl|rfl
            · have hzu : z=u := (Sym2.mem_iff.mp hze).resolve_right hzr
              subst z
              exact P.fst_mem_support_of_mem_edges heP
            · have hzv : z=v := (Sym2.mem_iff.mp hze).resolve_left hzr
              subst z
              exact P.snd_mem_support_of_mem_edges heP
          · apply False.elim
            apply Set.disjoint_left.mp hsep _ (Q.mem_edges_toSubgraph.mpr heQ)
            simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,List.mem_cons,List.mem_reverse]
            exact Or.inr (R.mem_edges_toSubgraph.mp hER)
        · exact Walk.mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp hEP) hze
    have hh := ih G (Walk.cons huvG R.reverse) Q hc' hQ
      (by simp only [Walk.length_cons,Walk.length_reverse]; omega) hsmall'
      ⟨u,huQ,(Walk.cons huvG R.reverse).start_mem_support⟩ hsep
    simpa only [hcover] using hh
  · let H := within G ({r}ᶜ : Set V) ⊔ edge u v
    have hRle : R.toSubgraph.spanningCoe ≤ H := by
      intro x y hxy
      apply Or.inl
      refine ⟨R.toSubgraph.adj_sub hxy,?_,?_⟩
      · rintro rfl
        exact hrR (Walk.mem_support_of_adj_toSubgraph hxy)
      · rintro rfl
        exact hrR (Walk.mem_support_of_adj_toSubgraph hxy.symm)
    have hPle : P.toSubgraph.spanningCoe ≤ H := by
      intro x y hxy
      apply Or.inl
      refine ⟨P.toSubgraph.adj_sub hxy,?_,?_⟩
      · rintro rfl
        exact hrP (Walk.mem_support_of_adj_toSubgraph hxy)
      · rintro rfl
        exact hrP (Walk.mem_support_of_adj_toSubgraph hxy.symm)
    have hRE : ∀ e ∈ R.edges, e ∈ H.edgeSet := fun e he ↦
      edgeSet_mono hRle (R.mem_edges_toSubgraph.mpr he)
    have hPE : ∀ e ∈ P.edges, e ∈ H.edgeSet := fun e he ↦
      edgeSet_mono hPle (P.mem_edges_toSubgraph.mpr he)
    let R' := R.transfer H hRE
    let P' := P.transfer H hPE
    have huvH : H.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,huv⟩)
    let C' := Walk.cons huvH R'.reverse
    have hc' : C'.IsCycle := (Walk.cons_isCycle_iff _ huvH).mpr
      ⟨(hRp.transfer hRE).reverse,by simpa only [R',Walk.edges_reverse,Walk.edges_transfer,List.mem_reverse] using heR⟩
    have hC'e : C'.toSubgraph.edgeSet={s(u,v)} ∪ R.toSubgraph.edgeSet := by
      ext e
      simp only [C',R',Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,
        Walk.edges_transfer,List.mem_cons,List.mem_reverse,Set.mem_union,Set.mem_singleton_iff]
    have hP'e : P'.toSubgraph.edgeSet=P.toSubgraph.edgeSet := by
      ext e
      simp only [P',Walk.mem_edges_toSubgraph,Walk.edges_transfer]
    have hsep : Disjoint C'.toSubgraph.edgeSet P'.toSubgraph.edgeSet := by
      rw [hC'e,hP'e]
      apply disjoint_sup_left.mpr
      refine ⟨Set.disjoint_left.mpr ?_,hdR⟩
      rintro e rfl he
      exact heP (P.mem_edges_toSubgraph.mp he)
    have hint : ∃ x ∈ P'.support, x ∈ C'.support := by
      obtain ⟨x,hxP,hxC⟩ := hinter
      have hxr : x ≠ r := fun hh ↦ hrP (hh ▸ hxP)
      have hxR : x ∈ R.support := by
        simpa only [Walk.support_cons,Walk.support_concat,List.concat_eq_append,
          List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,hxr,false_or,or_false] using hxC
      refine ⟨x,by simpa only [P',Walk.support_transfer] using hxP,?_⟩
      simp only [C',R',Walk.support_cons,Walk.support_reverse,Walk.support_transfer,
        List.mem_cons,List.mem_reverse]
      exact Or.inr hxR
    have hsmall' : (C'.toSubgraph.verts ∩ P'.toSubgraph.verts).ncard ≤ 4 := by
      apply (Set.ncard_le_ncard (s := C'.toSubgraph.verts ∩ P'.toSubgraph.verts)
        (t := C.toSubgraph.verts ∩ P.toSubgraph.verts) ?_).trans hsmall
      intro z hz
      have hzC' : z=u ∨ z ∈ R.support := by
        simpa only [C',R',Walk.mem_verts_toSubgraph,Walk.support_cons,
          Walk.support_reverse,Walk.support_transfer,List.mem_cons,List.mem_reverse] using hz.1
      have hzC : z ∈ C.toSubgraph.verts := by
        simp only [C,Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_concat,
          List.mem_cons,List.concat_eq_append,List.mem_append]
        rcases hzC' with rfl|hzR
        · exact Or.inr (Or.inl R.start_mem_support)
        · exact Or.inr (Or.inl hzR)
      exact ⟨hzC,by simpa only [P',Walk.mem_verts_toSubgraph,Walk.support_transfer] using hz.2⟩
    have hcover := ih H C' P' hc' (hp.transfer hPE)
      (by simp only [C',R',Walk.length_cons,Walk.length_reverse,Walk.length_transfer]; omega)
      hsmall' hint hsep
    let ear : G.Walk u v := .cons hru.symm (.cons hvr.symm .nil)
    have hEar : ear.IsPath := by simp [ear,Walk.cons_isPath_iff,hru.ne.symm,hvr.ne.symm,huv]
    have hrest : H.deleteEdges {s(u,v)} ≤ G := by
      intro x y hxy
      have hh : H.Adj x y ∧ s(x,y) ≠ s(u,v) := by simpa only [deleteEdges_adj,Set.mem_singleton_iff] using hxy
      rcases hh.1 with hh'|hh'
      · exact hh'.1
      · exact (hh.2 ((adj_edge ..).mp hh').1.symm).elim
    have hrH : r ∉ H.support := by
      intro hh
      obtain ⟨x,hx⟩ := (H.mem_support).mp hh
      rcases hx with hx|hx
      · exact hx.2.1 rfl
      · have hx' := (edge_adj ..).mp hx
        exact hx'.1.elim (fun hh ↦ hru.ne hh.1) (fun hh ↦ hvr.ne hh.1.symm)
    have hf : ∀ x ∈ ear.support, x ≠ u → x ≠ v → x ∉ H.support := by
      intro x hx hxu hxv
      have hxr : x=r := by simpa [ear,Walk.support,hxu,hxv] using hx
      subst x
      exact hrH
    have he0 : s(u,v) ∈ C'.toSubgraph.edgeSet ∪ P'.toSubgraph.edgeSet := by
      rw [hC'e]; exact Or.inl (Or.inl rfl)
    have hh := expand_pair ear hEar hrest hf _ he0 hcover
    have hEarE : ear.toSubgraph.edgeSet=({s(u,r),s(r,v)} : Set (Sym2 V)) := by
      ext e
      simp only [ear,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
        List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff]
    have heR' : s(u,v) ∉ R.toSubgraph.edgeSet := by simpa only [Walk.mem_edges_toSubgraph] using heR
    have heP' : s(u,v) ∉ P.toSubgraph.edgeSet := by simpa only [Walk.mem_edges_toSubgraph] using heP
    have heEar : s(u,v) ∉ ear.toSubgraph.edgeSet := fun he ↦ by
      have hl := endpoint_edge_forces_length_one ear hEar (ear.mem_edges_toSubgraph.mp he)
      simp [ear] at hl
    have hEq : ((C'.toSubgraph.edgeSet ∪ P'.toSubgraph.edgeSet) \ {s(u,v)}) ∪ ear.toSubgraph.edgeSet =
        C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := by
      rw [hC'e,hP'e,hCe,←hEarE]
      ext e
      by_cases he : e=s(u,v)
      · subst e
        simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff,not_true_eq_false,
          and_false,heR',heP',heEar,or_false]
      · simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff,he,not_false_eq_true,and_true,false_or]
        tauto
    simpa only [hEq] using hh

lemma short_cycle_absorption {a b r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hl : C.length ≤ 4) (P : G.Walk a b) (hp : P.IsPath)
    (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  have h3 := hc.three_le_length
  have hcases : C.length=3 ∨ C.length=4 := by omega
  rcases hcases with hlen|hlen
  · obtain ⟨v,w,hrv,hvw,hwr,rfl⟩ := QuadrilateralAbsorption.three_cycle_rep C hlen
    have he : (Walk.cons hrv (Walk.cons hvw (Walk.cons hwr Walk.nil))).toSubgraph.edgeSet=
        ({s(r,v),s(v,w),s(r,w)} : Set (Sym2 V)) := by
      ext e
      simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
        List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := w) (b := r)]
    have hh := triangle_path_absorption hrv hvw hwr.symm P hp
      (by
        obtain ⟨x,hxP,hxC⟩ := hinter
        refine ⟨x,hxP,?_⟩
        simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hxC
        rcases hxC with rfl|rfl|rfl|rfl <;> simp)
      (fun e he' heP ↦ Set.disjoint_left.mp hd (he.symm ▸ he') heP)
    simpa only [he,Set.union_comm] using hh
  · exact four_cycle_path_absorption C hc hlen P hp hinter hd

/-- Any cycle and an intersecting edge-disjoint path can be absorbed into
two paths if they have at most four vertices in common. The cycle may have
arbitrarily many vertices outside the path. -/
lemma small_intersection_absorption {G : SimpleGraph V} {a b r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (P : G.Walk a b) (hp : P.IsPath)
    (hsmall : (C.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 4)
    (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  classical
  by_cases hl : C.length ≤ 4
  · exact short_cycle_absorption C hc hl P hp hinter hd
  have hmiss : ∃ x ∈ C.support, x ∉ P.support := by
    by_contra! hall
    have hsub : C.toSubgraph.verts ⊆ P.toSubgraph.verts := by
      intro x hx
      rw [Walk.mem_verts_toSubgraph] at hx ⊢
      exact hall x hx
    have he : C.toSubgraph.verts ∩ P.toSubgraph.verts=C.toSubgraph.verts := Set.inter_eq_left.mpr hsub
    rw [he,Walk.verts_toSubgraph,cycle_support_ncard hc] at hsmall
    omega
  obtain ⟨x,hxC,hxP⟩ := hmiss
  let D := C.rotate hxC
  have hD : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hxC
  have hDl : D.length=C.length := by
    have hh := congrArg Walk.length (C.take_spec hxC)
    simpa only [D,Walk.rotate,Walk.length_append,Nat.add_comm] using hh
  obtain ⟨u,v,hxu,hvx,R,hform⟩ := CycleEar.cycle_two_spokes D (hc.rotate hxC)
  have hRtot : R.length+2=C.length := by
    rw [hform] at hDl
    simp only [Walk.length_cons,Walk.length_concat] at hDl
    omega
  have hsmallD : (D.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 4 := by rwa [hD]
  have hinterD : ∃ z ∈ P.support, z ∈ D.support := by
    obtain ⟨z,hzP,hzC⟩ := hinter
    refine ⟨z,hzP,?_⟩
    rwa [←Walk.mem_verts_toSubgraph,hD,Walk.mem_verts_toSubgraph]
  have hdD : Disjoint D.toSubgraph.edgeSet P.toSubgraph.edgeSet := by rwa [hD]
  have hh := missing_ear_reduction hxu hvx R (by omega) (hform ▸ hc.rotate hxC) P hp hxP
    (by simpa only [hform] using hinterD) (hform ▸ hdD) (hform ▸ hsmallD) (by
      intro H s a' b' C' P' hC' hP' hlen' hsmall' hint' hdis'
      exact small_intersection_absorption (G := H) C' hC' P' hP' hsmall' hint' hdis')
  simpa only [←hform,hD] using hh
termination_by C.length

decreasing_by
  omega

/-- Every path meeting a whole cycle in a globally score-maximal trail
family shares at least five vertices with the cycle. -/
lemma maximal_cycle_intersection_ge_five {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (i j : Fin k) (hij : i ≠ j)
    {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hj : (T.walk j).IsPath)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    5 ≤ (C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  by_contra! hn
  apply maximal_cycle_not_absorbable T hm i j hij C hc hi hj
  exact small_intersection_absorption C hc (T.walk j) hj (by omega) hinter
    (by rw [←hi]; exact T.disjoint hij)

lemma single_defect_cycle_intersection_ge_five {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (i j : Fin k) (hij : i ≠ j)
    {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    5 ≤ (C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  have hj := (T.one_defect_other_paths hs i (CycleEar.cycle_member_not_path T i C hc hi)).2 j hij.symm
  exact maximal_cycle_intersection_ge_five T hm i j hij C hc hi hj hinter

end Erdos583CycleIntersectionBoundDevelopment
