import Submission.QuadrilateralAbsorption

/-! Local consequences of quadrilateral absorption for a five-cycle.
A five-cycle missed by an intersecting path can be shortened at a missing corner. -/
namespace Erdos583PentagonIntersectionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.TriangleAbsorption
open Erdos583Work.BridgeGlue Erdos583QuadrilateralAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma expand_pair {H : SimpleGraph V} {a b : V} (r : G.Walk a b) (hr : r.IsPath)
    (hrest : H.deleteEdges {s(a,b)} ≤ G)
    (hfresh : ∀ x ∈ r.support, x ≠ a → x ≠ b → x ∉ H.support)
    (E : Set (Sym2 V)) (he0 : s(a,b) ∈ E) (hp : TwoPathCover (G := H) E) :
    TwoPathCover (G := G) ((E \ {s(a,b)}) ∪ r.toSubgraph.edgeSet) := by
  classical
  obtain ⟨u,v,w,z,P,Q,hP,hQ,hd,he⟩ := hp
  obtain ⟨P',hP',hPe⟩ := path_expand_edge r hr hrest hfresh P hP
  obtain ⟨Q',hQ',hQe⟩ := path_expand_edge r hr hrest hfresh Q hQ
  have hmP (e : Sym2 V) : e ∈ P'.toSubgraph.edgeSet ↔
      (e ∈ P.toSubgraph.edgeSet ∧ e ≠ s(a,b)) ∨
      (s(a,b) ∈ P.toSubgraph.edgeSet ∧ e ∈ r.toSubgraph.edgeSet) := by
    rw [hPe]
    by_cases hp : s(a,b) ∈ P.edges
    · simp [hp]
    · simp [hp]
      rintro he rfl
      exact hp he
  have hmQ (e : Sym2 V) : e ∈ Q'.toSubgraph.edgeSet ↔
      (e ∈ Q.toSubgraph.edgeSet ∧ e ≠ s(a,b)) ∨
      (s(a,b) ∈ Q.toSubgraph.edgeSet ∧ e ∈ r.toSubgraph.edgeSet) := by
    rw [hQe]
    by_cases hp : s(a,b) ∈ Q.edges
    · simp [hp]
    · simp [hp]
      rintro he rfl
      exact hp he
  have hsep := expansion_path_disjoint_old_edges r hfresh
  have hd' : Disjoint P'.toSubgraph.edgeSet Q'.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heP heQ
    rcases (hmP e).mp heP with ⟨heP,hnP⟩|⟨heP,hrP⟩ <;>
      rcases (hmQ e).mp heQ with ⟨heQ,hnQ⟩|⟨heQ,hrQ⟩
    · exact Set.disjoint_left.mp hd heP heQ
    · exact Set.disjoint_left.mp hsep hrQ ⟨P.toSubgraph.edgeSet_subset heP,hnP⟩
    · exact Set.disjoint_left.mp hsep hrP ⟨Q.toSubgraph.edgeSet_subset heQ,hnQ⟩
    · exact Set.disjoint_left.mp hd heP heQ
  refine ⟨u,v,w,z,P',Q',hP',hQ',hd',?_⟩
  have hpos : s(a,b) ∈ P.toSubgraph.edgeSet ∨ s(a,b) ∈ Q.toSubgraph.edgeSet := by rwa [←he] at he0
  ext e
  rw [Set.mem_union,hmP,hmQ,←he]
  simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
  tauto

lemma four_cycle_path_absorption {a b r : V} (C : G.Walk r r)
    (hc : C.IsCycle) (hl : C.length=4) (P : G.Walk a b) (hp : P.IsPath)
    (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨v,w,z,hrv,hvw,hwz,hzr,hrw,hvz,hC⟩ := four_cycle_rep C hc hl
  have hV : {x | x ∈ C.support}=({r,v,w,z} : Set V) := by
    rw [←Walk.verts_toSubgraph,hC,squareWalk_verts]
  have he : C.toSubgraph.edgeSet=squareEdges r v w z := by rw [hC,squareWalk_edges]
  have hh := quadrilateral_path_absorption hrv hvw hwz hzr hrw hvz P hp
    (by simpa only [←hV,Set.mem_setOf_eq] using hinter) (by rw [←he]; exact hd.symm)
  simpa only [he,Set.union_comm] using hh

omit [Fintype V] in
lemma endpoint_edge_forces_length_one {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (he : s(a,b) ∈ P.edges) : P.length=1 := by
  cases P with
  | nil => simp at he
  | @cons _ x _ h Q =>
    have hbx : b=x := by simpa using hp.eq_snd_of_mem_edges he
    subst x
    have hQ : Q=Walk.nil := (Walk.isPath_iff_eq_nil Q).mp hp.of_cons
    simp [hQ]

lemma missing_ear_five {a b r u v : V} (hru : G.Adj r u) (hvr : G.Adj v r)
    (R : G.Walk u v) (hRlen : R.length=3)
    (hc : (Walk.cons hru (R.concat hvr)).IsCycle)
    (P : G.Walk a b) (hp : P.IsPath) (hrP : r ∉ P.support)
    (hinter : ∃ x ∈ P.support, x ∈ (Walk.cons hru (R.concat hvr)).support)
    (hd : Disjoint (Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet P.toSubgraph.edgeSet) :
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
    have hh := four_cycle_path_absorption (Walk.cons huvG R.reverse) hc'
      (by simp only [Walk.length_cons,Walk.length_reverse,hRlen]) Q hQ
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
    have hcover := four_cycle_path_absorption C' hc'
      (by simp only [C',R',Walk.length_cons,Walk.length_reverse,Walk.length_transfer,hRlen])
      P' (hp.transfer hPE) hint hsep
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

lemma five_cycle_missing_start {a b r : V} (C : G.Walk r r)
    (hc : C.IsCycle) (hl : C.length=5) (P : G.Walk a b) (hp : P.IsPath)
    (hrP : r ∉ P.support) (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨u,v,hru,hvr,R,hC⟩ := CycleEar.cycle_two_spokes C hc
  have hRlen : R.length=3 := by
    rw [hC] at hl
    simp only [Walk.length_cons,Walk.length_concat] at hl
    omega
  have hh := missing_ear_five hru hvr R hRlen (hC ▸ hc) P hp hrP
    (by simpa only [hC] using hinter) (hC ▸ hd)
  simpa only [←hC] using hh

/-- A five-cycle can be absorbed into two paths with an intersecting path
if that path misses even one cycle vertex. -/
lemma five_cycle_missing_absorption {a b r : V} (C : G.Walk r r)
    (hc : C.IsCycle) (hl : C.length=5) (P : G.Walk a b) (hp : P.IsPath)
    (hmiss : ∃ x ∈ C.support, x ∉ P.support)
    (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨x,hxC,hxP⟩ := hmiss
  let D := C.rotate hxC
  have hD : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hxC
  have hDl : D.length=5 := by
    have hh := congrArg Walk.length (C.take_spec hxC)
    simpa only [D,Walk.rotate,Walk.length_append,hl,Nat.add_comm] using hh
  have hint : ∃ y ∈ P.support, y ∈ D.support := by
    obtain ⟨y,hyP,hyC⟩ := hinter
    refine ⟨y,hyP,?_⟩
    rw [←Walk.mem_verts_toSubgraph,hD,Walk.mem_verts_toSubgraph]
    exact hyC
  have hh := five_cycle_missing_start D (hc.rotate hxC) hDl P hp hxP hint (by rw [hD]; exact hd)
  simpa only [hD] using hh

lemma maximal_cycle_not_absorbable {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hj : (T.walk j).IsPath) :
    ¬TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) := by
  rintro ⟨a,b,c,d,X,Y,hX,hY,hd,he⟩
  have hdold : Disjoint C.toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet := by
    rw [←hi]; exact T.disjoint hij
  obtain ⟨U,_,_,_,hs⟩ := GeneralPair.replace_two T i j hij a b c d X Y
    hX.isTrail hY.isTrail hd (by simpa only [hi] using he)
  have hlen := congrArg Set.ncard he
  rw [Set.ncard_union_eq hd,Set.ncard_union_eq hdold,
    trail_edgeSet_ncard X hX.isTrail,trail_edgeSet_ncard Y hY.isTrail,
    trail_edgeSet_ncard C hc.isTrail,trail_edgeSet_ncard _ hj.isTrail] at hlen
  have hvC : (T.walk i).toSubgraph.verts.ncard=C.length := by
    rw [hi,Walk.verts_toSubgraph,cycle_support_ncard hc]
  rw [hvC,(walk_vertex_ncard_eq_iff _).mpr hj,
    (walk_vertex_ncard_eq_iff X).mpr hX,(walk_vertex_ncard_eq_iff Y).mpr hY] at hs
  have hb := hm U
  omega

/-- At a global score maximum, every path meeting a whole five-cycle must
contain all five cycle vertices. This is weaker than an unrestricted absorption
claim, which is false for five-cycles. -/
lemma maximal_five_cycle_path_contains {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r)
    (hc : C.IsCycle) (hl : C.length=5)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hj : (T.walk j).IsPath)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    ∀ x ∈ C.support, x ∈ (T.walk j).support := by
  intro x hxC
  by_contra hxP
  apply maximal_cycle_not_absorbable T hm i j hij C hc hi hj
  exact five_cycle_missing_absorption C hc hl (T.walk j) hj ⟨x,hxC,hxP⟩ hinter
    (by rw [←hi]; exact T.disjoint hij)

lemma single_defect_five_cycle_contains {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r)
    (hc : C.IsCycle) (hl : C.length=5)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    ∀ x ∈ C.support, x ∈ (T.walk j).support := by
  apply maximal_five_cycle_path_contains T hm i j hij C hc hl hi _ hinter
  exact (T.one_defect_other_paths hs i (CycleEar.cycle_member_not_path T i C hc hi)).2 j hij.symm

/-- All five vertices of a whole pentagon have identical member-incidence
sets in a single-defect global maximum. -/
lemma five_cycle_equal_members {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {r : V} (C : G.Walk r r) (hc : C.IsCycle) (hl : C.length=5)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) {u v : V}
    (hu : u ∈ C.support) (hv : v ∈ C.support) (j : Fin k) :
    u ∈ (T.walk j).support ↔ v ∈ (T.walk j).support := by
  by_cases hji : j=i
  · subst j
    have hu' : u ∈ (T.walk i).support := by rwa [←Walk.mem_verts_toSubgraph,hi,Walk.mem_verts_toSubgraph]
    have hv' : v ∈ (T.walk i).support := by rwa [←Walk.mem_verts_toSubgraph,hi,Walk.mem_verts_toSubgraph]
    exact iff_of_true hu' hv'
  · constructor
    · intro huj
      exact single_defect_five_cycle_contains T hs hm i j (Ne.symm hji) C hc hl hi ⟨u,huj,hu⟩ v hv
    · intro hvj
      exact single_defect_five_cycle_contains T hs hm i j (Ne.symm hji) C hc hl hi ⟨v,hvj,hv⟩ u hu

end Erdos583PentagonIntersectionDevelopment
