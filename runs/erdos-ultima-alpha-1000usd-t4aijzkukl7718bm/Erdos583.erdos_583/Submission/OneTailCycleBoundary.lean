import Submission.UnifiedMinimalDefect
import Submission.ShortTriangleIncidence

/-! Boundary visits in a one-edge-tail defect. These local absorptions do not
assert the unrestricted Gallai bound. -/
namespace Erdos583OneTailCycleBoundaryDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.TriangleAbsorption Erdos583Work.ShortLollipop
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma tail_edge_attach_two_cycle_arcs {r v t a b : V}
    (C : G.Walk r r) (hc : C.IsCycle)
    (A : G.Walk a v) (B : G.Walk v b) (hp : (A.append B).IsPath)
    (X : G.Walk r v) (Y : G.Walk r v) (hX : X.IsPath) (hY : Y.IsPath)
    (hXY : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=C.toSubgraph.edgeSet)
    (hXL : ∀ z ∈ X.support, z ∈ A.support → z=v)
    (hYR : ∀ z ∈ Y.support, z ∈ B.support → z=v)
    (g : G.Adj r t) (htC : t ∉ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet (A.append B).toSubgraph.edgeSet)
    (hnew : s(r,t) ∉ (A.append B).toSubgraph.edgeSet)
    (hlen : X.length+Y.length=C.length)
    (hXC : ∀ z ∈ X.support, z ∈ C.support)
    (hYC : ∀ z ∈ Y.support, z ∈ C.support) :
    TwoPathCover (G := G)
      (insert s(r,t) (C.toSubgraph.edgeSet ∪ (A.append B).toSubgraph.edgeSet)) := by
  let P := X.append A.reverse
  let Q := Y.append B
  have hP : P.IsPath := path_append_of_support_intersection hX hp.of_append_left.reverse
    (by intro z hzX hzA; exact hXL z hzX (by simpa using hzA))
  have hQ : Q.IsPath := path_append_of_support_intersection hY hp.of_append_right hYR
  have he : P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
      C.toSubgraph.edgeSet ∪ (A.append B).toSubgraph.edgeSet := by
    simp only [P,Q,Walk.toSubgraph_append,Walk.toSubgraph_reverse,Subgraph.edgeSet_sup]
    rw [show X.toSubgraph.edgeSet ∪ A.toSubgraph.edgeSet ∪
      (Y.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet)=
      (X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet) ∪
        (A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet) by ext e; simp only [Set.mem_union]; tauto]
    rw [hXY]
  have hlength : P.length+Q.length=
      (C.toSubgraph.edgeSet ∪ (A.append B).toSubgraph.edgeSet).ncard := by
    rw [Set.ncard_union_eq hd,trail_edgeSet_ncard _ hc.isTrail,trail_edgeSet_ncard _ hp.isTrail]
    simp only [P,Q,Walk.length_append,Walk.length_reverse]
    omega
  have hsep := disjoint_of_cover_length P Q hP.isTrail hQ.isTrail _ he hlength
  have hnew' : s(r,t) ∉ P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet := by
    rw [he]
    rintro (hh|hh)
    · exact htC (Walk.mem_support_of_adj_toSubgraph hh.symm)
    · exact hnew hh
  have ht : t ∉ P.support ∨ t ∉ Q.support := by
    by_cases htP : t ∈ P.support
    · right
      have htA : t ∈ A.support := by
        rcases (Walk.mem_support_append_iff X A.reverse).mp htP with htX|htA
        · exact (htC (hXC t htX)).elim
        · simpa using htA
      intro htQ
      rcases (Walk.mem_support_append_iff Y B).mp htQ with htY|htB
      · exact htC (hYC t htY)
      · have htv : t ≠ v := fun hv ↦ htC (hv ▸ hXC v X.end_mem_support)
        exact hp.ne_of_mem_support_of_append htv htA htB rfl
    · exact Or.inl htP
  have hh := attach_common_start_edge g P Q hP hQ hsep hnew' ht
  rwa [he] at hh

lemma one_tail_last_neighbor_cover {r v t a b : V}
    (h : G.Adj r v) (R : G.Walk v r) (hc : (Walk.cons h R).IsCycle)
    (g : G.Adj r t) (htC : t ∉ (Walk.cons h R).support)
    (A : G.Walk a v) (B : G.Walk v b) (hp : (A.append B).IsPath)
    (hr : r ∉ (A.append B).support)
    (hB : ∀ z ∈ B.support, z ∈ (Walk.cons h R).support → z=v)
    (hd : Disjoint (Walk.cons h R).toSubgraph.edgeSet (A.append B).toSubgraph.edgeSet)
    (hnew : s(r,t) ∉ (A.append B).toSubgraph.edgeSet) :
    TwoPathCover (G := G)
      (insert s(r,t) ((Walk.cons h R).toSubgraph.edgeSet ∪ (A.append B).toSubgraph.edgeSet)) := by
  let X : G.Walk r v := Walk.cons h Walk.nil
  have hR := (Walk.cons_isCycle_iff R h).mp hc |>.1
  apply tail_edge_attach_two_cycle_arcs (Walk.cons h R) hc A B hp X R.reverse
    (by simp [X,h.ne]) hR.reverse
  · ext e
    simp [X,or_comm]
  · intro z hzX hzA
    have hz : z=r ∨ z=v := by simpa [X] using hzX
    rcases hz with hz|hz
    · exact (hr (hz ▸ (Walk.mem_support_append_iff A B).mpr (Or.inl hzA))).elim
    · exact hz
  · intro z hzR hzB
    exact hB z hzB (List.mem_cons_of_mem _ (by simpa using hzR))
  · exact g
  · exact htC
  · exact hd
  · exact hnew
  · simp [X,Nat.add_comm]
  · intro z hzX
    have hz : z=r ∨ z=v := by simpa [X] using hzX
    rcases hz with rfl|rfl
    · exact (Walk.cons h R).start_mem_support
    · exact List.mem_cons_of_mem _ R.start_mem_support
  · intro z hzR
    exact List.mem_cons_of_mem _ (by simpa using hzR)

lemma one_tail_one_touch_cover {r v t a b : V}
    (C : G.Walk r r) (hc : C.IsCycle) (g : G.Adj r t) (htC : t ∉ C.support)
    (A : G.Walk a v) (B : G.Walk v b) (hp : (A.append B).IsPath)
    (hvr : v ≠ r) (hvC : v ∈ C.support)
    (hinter : ∀ z ∈ (A.append B).support, z ∈ C.support → z=v)
    (hd : Disjoint C.toSubgraph.edgeSet (A.append B).toSubgraph.edgeSet)
    (hnew : s(r,t) ∉ (A.append B).toSubgraph.edgeSet) :
    TwoPathCover (G := G)
      (insert s(r,t) (C.toSubgraph.edgeSet ∪ (A.append B).toSubgraph.edgeSet)) := by
  obtain ⟨X,Y,hC⟩ := C.mem_support_iff_exists_append.mp hvC
  have hX : X.IsPath := (hC ▸ hc).isPath_of_append_left (Walk.not_nil_of_ne hvr)
  have hY : Y.IsPath := (hC ▸ hc).isPath_of_append_right (Walk.not_nil_of_ne hvr.symm)
  apply tail_edge_attach_two_cycle_arcs C hc A B hp X Y.reverse hX hY.reverse
  · rw [hC,Walk.toSubgraph_append,Walk.toSubgraph_reverse,Subgraph.edgeSet_sup]
  · intro z hzX hzA
    exact hinter z ((Walk.mem_support_append_iff A B).mpr (Or.inl hzA))
      (by rw [hC,Walk.mem_support_append_iff]; exact Or.inl hzX)
  · intro z hzY hzB
    exact hinter z ((Walk.mem_support_append_iff A B).mpr (Or.inr hzB))
      (by rw [hC,Walk.mem_support_append_iff]; exact Or.inr (by simpa using hzY))
  · exact g
  · exact htC
  · exact hd
  · exact hnew
  · simp [hC]
  · intro z hzX
    rw [hC,Walk.mem_support_append_iff]
    exact Or.inl hzX
  · intro z hzY
    rw [hC,Walk.mem_support_append_iff]
    exact Or.inr (by simpa using hzY)



omit [Fintype V] in
lemma one_tail_anchor_edges {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hl : L.tail.length=1) :
    (T.walk L.index).toSubgraph.edgeSet=insert s(r,L.finish) L.cycle.toSubgraph.edgeSet := by
  obtain ⟨g,hg⟩ := one_edge_form L.tail hl
  rw [L.subgraph,hg]
  ext e
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,Walk.edges_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff]
  tauto

omit [Fintype V] in
lemma one_tail_finish_outside {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hl : L.tail.length=1) : L.finish ∉ L.cycle.support := by
  intro ht
  exact (Walk.adj_of_length_eq_one hl).ne
    (L.inter L.finish ht L.tail.end_mem_support).symm

lemma maximum_one_tail_no_last_neighbor {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) {a v b : V}
    (A : G.Walk a v) (B : G.Walk v b) (hp : (A.append B).IsPath)
    (hP : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hr : r ∉ (A.append B).support)
    (hB : ∀ z ∈ B.support, z ∈ L.cycle.support → z=v) :
    ¬L.cycle.toSubgraph.Adj r v := by
  intro hv
  let h := L.cycle.toSubgraph.adj_sub hv
  obtain ⟨R,hR,hRC⟩ := CycleFirstVisits.cycle_edge_first L.cycle L.isCycle h
    (L.cycle.mem_edges_toSubgraph.mp hv)
  have hd := T.disjoint hij
  dsimp only at hd
  rw [one_tail_anchor_edges T r L hl,hP] at hd
  obtain ⟨hnew,hdis⟩ := Set.disjoint_insert_left.mp hd
  have ht : L.finish ∉ (Walk.cons h R).support := by
    rw [←Walk.mem_verts_toSubgraph,hRC,Walk.mem_verts_toSubgraph]
    exact one_tail_finish_outside T r L hl
  have hBC : ∀ z ∈ B.support, z ∈ (Walk.cons h R).support → z=v := by
    intro z hzB hzC
    apply hB z hzB
    rw [←Walk.mem_verts_toSubgraph,←hRC,Walk.mem_verts_toSubgraph]
    exact hzC
  have hh := one_tail_last_neighbor_cover h R hR (Walk.adj_of_length_eq_one hl) ht
    A B hp hr hBC (by rw [hRC]; exact hdis) hnew
  apply maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  rw [one_tail_anchor_edges T r L hl,hP,Set.insert_union]
  simpa only [hRC] using hh

lemma maximum_one_tail_no_first_neighbor {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) {a v b : V}
    (A : G.Walk a v) (B : G.Walk v b) (hp : (A.append B).IsPath)
    (hP : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hr : r ∉ (A.append B).support)
    (hA : ∀ z ∈ A.support, z ∈ L.cycle.support → z=v) :
    ¬L.cycle.toSubgraph.Adj r v := by
  have hrev : B.reverse.append A.reverse=(A.append B).reverse := (Walk.reverse_append A B).symm
  exact maximum_one_tail_no_last_neighbor T hs hm r L hl j hij B.reverse A.reverse
    (by rw [hrev]; exact hp.reverse)
    (by rw [hrev,Walk.toSubgraph_reverse]; exact hP)
    (by simpa only [hrev,Walk.support_reverse,List.mem_reverse] using hr)
    (by intro z hz hzC; exact hA z (by simpa using hz) hzC)

lemma maximum_one_tail_no_one_touch {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) {a v b : V}
    (A : G.Walk a v) (B : G.Walk v b) (hp : (A.append B).IsPath)
    (hP : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hvr : v ≠ r) (hvC : v ∈ L.cycle.support)
    (hinter : ∀ z ∈ (A.append B).support, z ∈ L.cycle.support → z=v) : False := by
  have hd := T.disjoint hij
  dsimp only at hd
  rw [one_tail_anchor_edges T r L hl,hP] at hd
  obtain ⟨hnew,hdis⟩ := Set.disjoint_insert_left.mp hd
  have hh := one_tail_one_touch_cover L.cycle L.isCycle (Walk.adj_of_length_eq_one hl)
    (one_tail_finish_outside T r L hl) A B hp hvr hvC hinter hdis hnew
  apply maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  rw [one_tail_anchor_edges T r L hl,hP,Set.insert_union]
  exact hh

lemma maximum_one_tail_avoider_two_nonneighbors {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) (hr : r ∉ (T.walk j).support)
    (hhit : ∃ v ∈ (T.walk j).support, v ∈ L.cycle.support) :
    ∃ x y, x ≠ y ∧ x ≠ r ∧ y ≠ r ∧
      x ∈ L.cycle.support ∧ y ∈ L.cycle.support ∧
      x ∈ (T.walk j).support ∧ y ∈ (T.walk j).support ∧
      ¬L.cycle.toSubgraph.Adj r x ∧ ¬L.cycle.toSubgraph.Adj r y := by
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  obtain ⟨x,hxC,A,B,hP,hA⟩ := QuadrilateralAbsorption.first_hit_split (T.walk j) {z | z ∈ L.cycle.support} hhit
  obtain ⟨y,hyC,Q,E,hB,hE⟩ := CycleDefect.last_hit_split B {z | z ∈ L.cycle.support}
    ⟨x,B.start_mem_support,hxC⟩
  have hxP : x ∈ (T.walk j).support := by
    rw [hP,Walk.mem_support_append_iff]
    exact Or.inl A.end_mem_support
  have hyP : y ∈ (T.walk j).support := by
    rw [hP,hB,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
    exact Or.inr (Or.inr E.start_mem_support)
  have hxr : x ≠ r := fun hh ↦ hr (hh ▸ hxP)
  have hyr : y ≠ r := fun hh ↦ hr (hh ▸ hyP)
  have hnX := maximum_one_tail_no_first_neighbor T hs hm r L hl j hij A B
    (hP ▸ hp) (congrArg Walk.toSubgraph hP) (hP ▸ hr) hA
  have hPE : T.walk j=(A.append Q).append E := by rw [hP,hB,Walk.append_assoc]
  have hnY := maximum_one_tail_no_last_neighbor T hs hm r L hl j hij (A.append Q) E
    (hPE ▸ hp) (congrArg Walk.toSubgraph hPE) (hPE ▸ hr) hE
  have hxy : x ≠ y := by
    intro he
    subst y
    have hQ : Q=Walk.nil := (Walk.isPath_iff_eq_nil Q).mp
      ((hB ▸ (hP ▸ hp).of_append_right).of_append_left)
    have hBE : B=E := by simpa only [hQ,Walk.nil_append] using hB
    apply maximum_one_tail_no_one_touch T hs hm r L hl j hij A B
      (hP ▸ hp) (congrArg Walk.toSubgraph hP) hxr hxC
    intro z hz hzC
    rcases (Walk.mem_support_append_iff A B).mp hz with hz|hz
    · exact hA z hz hzC
    · exact hE z (hBE ▸ hz) hzC
  exact ⟨x,y,hxy,hxr,hyr,hxC,hyC,hxP,hyP,hnX,hnY⟩

lemma cycle_two_nonneighbors_length_ge_five {r x y : V} (C : G.Walk r r)
    (hc : C.IsCycle) (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hxC : x ∈ C.support) (hyC : y ∈ C.support)
    (hx : ¬C.toSubgraph.Adj r x) (hy : ¬C.toSubgraph.Adj r y) :
    5 ≤ C.length := by
  have hrs := (C.toSubgraph_adj_snd hc.not_nil).ne
  have hrp := (C.toSubgraph_adj_penultimate hc.not_nil).ne.symm
  have hsp := hc.snd_ne_penultimate
  have hxs : x ≠ C.snd := fun h ↦ hx (h.symm ▸ C.toSubgraph_adj_snd hc.not_nil)
  have hxp : x ≠ C.penultimate := fun h ↦ hx (h.symm ▸ (C.toSubgraph_adj_penultimate hc.not_nil).symm)
  have hys : y ≠ C.snd := fun h ↦ hy (h.symm ▸ C.toSubgraph_adj_snd hc.not_nil)
  have hyp : y ≠ C.penultimate := fun h ↦ hy (h.symm ▸ (C.toSubgraph_adj_penultimate hc.not_nil).symm)
  let S : Set V := {r,C.snd,C.penultimate,x,y}
  have hSc : S.ncard=5 := by
    simp [S,Set.ncard_insert_of_notMem,hrs,hrp,hsp,hxr.symm,hyr.symm,hxs.symm,hxp.symm,
      hys.symm,hyp.symm,hxy]
  have hsub : S ⊆ C.toSubgraph.verts := by
    rintro z (rfl|rfl|rfl|rfl|rfl)
    · exact C.start_mem_verts_toSubgraph
    · exact C.mem_verts_toSubgraph.mpr (C.getVert_mem_support 1)
    · exact C.mem_verts_toSubgraph.mpr (C.getVert_mem_support (C.length-1))
    · exact C.mem_verts_toSubgraph.mpr hxC
    · exact C.mem_verts_toSubgraph.mpr hyC
  have hh := Set.ncard_le_ncard hsub
  rw [hSc,Walk.verts_toSubgraph,cycle_support_ncard hc] at hh
  exact hh

lemma maximum_one_tail_short_cycle_contains_root {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1) (hc : L.cycle.length ≤ 4)
    (j : Fin k) {v : V} (hvC : v ∈ L.cycle.support) (hvj : v ∈ (T.walk j).support) :
    r ∈ (T.walk j).support := by
  by_cases hji : j=L.index
  · subst j
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  · by_contra hr
    obtain ⟨x,y,hxy,hxr,hyr,hxC,hyC,_,_,hx,hy⟩ :=
      maximum_one_tail_avoider_two_nonneighbors T hs hm r L hl j (Ne.symm hji) hr ⟨v,hvj,hvC⟩
    have hh := cycle_two_nonneighbors_length_ge_five L.cycle L.isCycle hxy hxr hyr hxC hyC hx hy
    omega

lemma one_tail_short_cycle_degree_dominance {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1) (hc : L.cycle.length ≤ 4)
    (hq : T.quota r=1) {v : V} (hvC : v ∈ L.cycle.support) (hvr : v ≠ r) :
    Nat.card (G.neighborSet v)+T.quota v+1 ≤ Nat.card (G.neighborSet r) := by
  have hh := Erdos583ShortTriangleIncidenceDevelopment.rooted_support_degree_dominance
    T r hs L.hasRoot hvr
    (fun j hj ↦ maximum_one_tail_short_cycle_contains_root T hs hm r L hl hc j hvC hj)
  omega

open Erdos583UnifiedMinimalDefectDevelopment in
lemma odd_one_tail_short_cycle_root_degree_ge_seven (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1) (hc : D.rep.cycle.length ≤ 4) :
    7 ≤ Nat.card (F.graph.neighborSet D.root) := by
  have hq := Erdos583RootEndpointTailCapacityDevelopment.minimum_one_edge_tail_root_quota_one
    D.family D.score D.maximum D.root D.rep D.cycle_minimum hl
  have hvC : D.rep.cycle.snd ∈ D.rep.cycle.support := D.rep.cycle.getVert_mem_support 1
  have hvr : D.rep.cycle.snd ≠ D.root := (D.rep.cycle.adj_snd D.rep.isCycle.not_nil).ne.symm
  have hb := one_tail_short_cycle_degree_dominance D.family D.score D.maximum D.root D.rep hl hc hq hvC hvr
  have hlow := DegreeFourReduction.min_degree_five_of_odd_failure F.smaller ho F.connected F.failure D.rep.cycle.snd
  have hodd : Odd (Nat.card (F.graph.neighborSet D.root)) :=
    (QuotaParity.quota_odd_iff D.family D.root).mp (by rw [hq]; exact odd_one)
  obtain ⟨a,ha⟩ := hodd
  omega

open Erdos583UnifiedMinimalDefectDevelopment in
lemma odd_one_tail_degree_five_cycle_length_ge_five (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1) (hd : Nat.card (F.graph.neighborSet D.root) ≤ 5) :
    5 ≤ D.rep.cycle.length := by
  by_contra hh
  have hb := odd_one_tail_short_cycle_root_degree_ge_seven F D ho hl (by omega)
  omega

end Erdos583OneTailCycleBoundaryDevelopment
