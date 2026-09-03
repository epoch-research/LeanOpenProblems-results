import Submission.OneTailCycleBoundary
import Submission.CyclePrefixEndpointObstruction

/-! Four cycle visits are forced for an ordinary root-avoiding path in a
maximum one-edge-tail defect. This is a local restriction, not Gallai's bound. -/
namespace Erdos583OneTailCycleVisitsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.TriangleAbsorption Erdos583Work.ShortLollipop
open Erdos583OneTailCycleBoundaryDevelopment
open Erdos583CyclePrefixEndpointObstructionDevelopment
open Erdos583TailPrefixRunFreshnessDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma one_tail_first_arc_cover {r x t a b : V}
    (X : G.Walk r x) (Y : G.Walk x r) (hc : (X.append Y).IsCycle)
    (hxr : x ≠ r) (g : G.Adj r t) (ht : t ∉ (X.append Y).support)
    (A : G.Walk a x) (B : G.Walk x b) (hp : (A.append B).IsPath)
    (hA : ∀ z ∈ A.support, z ∈ (X.append Y).support → z=x)
    (hX : ∀ z ∈ X.support, z ∈ (A.append B).support → z=x)
    (hd : Disjoint (X.append Y).toSubgraph.edgeSet (A.append B).toSubgraph.edgeSet)
    (he : s(r,t) ∉ (A.append B).toSubgraph.edgeSet) :
    TwoPathCover (G := G)
      (insert s(r,t) ((X.append Y).toSubgraph.edgeSet ∪ (A.append B).toSubgraph.edgeSet)) := by
  apply tail_edge_attach_two_cycle_arcs (X.append Y) hc A B hp Y.reverse X
    (hc.isPath_of_append_right (Walk.not_nil_of_ne hxr.symm)).reverse
    (hc.isPath_of_append_left (Walk.not_nil_of_ne hxr))
  · simp only [Walk.toSubgraph_reverse,Walk.toSubgraph_append,Subgraph.edgeSet_sup,Set.union_comm]
  · intro z hzY hzA
    exact hA z hzA ((Walk.mem_support_append_iff X Y).mpr (Or.inr (by simpa using hzY)))
  · intro z hzX hzB
    exact hX z hzX ((Walk.mem_support_append_iff A B).mpr (Or.inr hzB))
  · exact g
  · exact ht
  · exact hd
  · exact he
  · simp only [Walk.length_append,Walk.length_reverse,Nat.add_comm]
  · intro z hzY
    exact (Walk.mem_support_append_iff X Y).mpr (Or.inr (by simpa using hzY))
  · intro z hzX
    exact (Walk.mem_support_append_iff X Y).mpr (Or.inl hzX)

lemma maximum_one_tail_first_arc_hit {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) {a x b : V}
    (A : G.Walk a x) (B : G.Walk x b) (hp : (A.append B).IsPath)
    (hP : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hxr : x ≠ r) (X : G.Walk r x) (Y : G.Walk x r) (hC : L.cycle=X.append Y)
    (hA : ∀ z ∈ A.support, z ∈ L.cycle.support → z=x) :
    ∃ z ∈ X.support, z ∈ (A.append B).support ∧ z ≠ x := by
  by_contra hn
  have hX : ∀ z ∈ X.support, z ∈ (A.append B).support → z=x := by
    intro z hzX hzP
    by_contra hzx
    exact hn ⟨z,hzX,hzP,hzx⟩
  have hd := T.disjoint hij
  dsimp only at hd
  rw [one_tail_anchor_edges T r L hl,hP,hC] at hd
  obtain ⟨he,hd⟩ := Set.disjoint_insert_left.mp hd
  have hh := one_tail_first_arc_cover X Y (hC ▸ L.isCycle) hxr
    (Walk.adj_of_length_eq_one hl) (hC ▸ one_tail_finish_outside T r L hl)
    A B hp (by simpa only [←hC] using hA) hX hd he
  apply maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  rw [one_tail_anchor_edges T r L hl,hP,hC,Set.insert_union]
  exact hh

omit [Fintype V] in
def reverseCycleRep {k : ℕ} (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    RootedCycleRep T r :=
  ⟨L.index,L.finish,L.start_eq,L.finish_eq,L.cycle.reverse,L.tail,L.isCycle.reverse,L.isPath,
    by intro z hz ht; exact L.inter z (by simpa using hz) ht,
    by simpa only [Walk.toSubgraph_append,Walk.toSubgraph_reverse] using L.subgraph⟩

lemma maximum_one_tail_last_arc_hit {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) {a x b : V}
    (A : G.Walk a x) (B : G.Walk x b) (hp : (A.append B).IsPath)
    (hP : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hxr : x ≠ r) (X : G.Walk r x) (Y : G.Walk x r) (hC : L.cycle=X.append Y)
    (hB : ∀ z ∈ B.support, z ∈ L.cycle.support → z=x) :
    ∃ z ∈ Y.support, z ∈ (A.append B).support ∧ z ≠ x := by
  have he : B.reverse.append A.reverse=(A.append B).reverse := (Walk.reverse_append A B).symm
  obtain ⟨z,hzY,hzP,hzx⟩ := maximum_one_tail_first_arc_hit T hs hm r (reverseCycleRep T r L)
    hl j hij B.reverse A.reverse (by rw [he]; exact hp.reverse)
    (by rw [he,Walk.toSubgraph_reverse]; exact hP) hxr Y.reverse X.reverse
    (by simp only [reverseCycleRep,hC,Walk.reverse_append])
    (by intro z hzB hzC; exact hB z (by simpa using hzB) (by simpa [reverseCycleRep] using hzC))
  exact ⟨z,by simpa using hzY,by simpa only [he,Walk.support_reverse,List.mem_reverse] using hzP,hzx⟩

lemma ordered_boundary_four_visits {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) (hr : r ∉ (T.walk j).support)
    {x y : V} (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (A : G.Walk (T.start j) x) (B : G.Walk x (T.finish j)) (hP : T.walk j=A.append B)
    (Q : G.Walk (T.start j) y) (E : G.Walk y (T.finish j)) (hP' : T.walk j=Q.append E)
    (hA : ∀ z ∈ A.support, z ∈ L.cycle.support → z=x)
    (hE : ∀ z ∈ E.support, z ∈ L.cycle.support → z=y)
    (X : G.Walk r x) (Y : G.Walk x y) (Z : G.Walk y r)
    (hC : L.cycle=(X.append Y).append Z) :
    ∃ u v, ({x,y,u,v} : Set V).ncard=4 ∧
      {x,y,u,v} ⊆ L.cycle.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts := by
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  obtain ⟨u,huX,huP,hux⟩ := maximum_one_tail_first_arc_hit T hs hm r L hl j hij A B
    (hP ▸ hp) (congrArg Walk.toSubgraph hP) hxr X (Y.append Z)
    (by simpa only [Walk.append_assoc] using hC) hA
  obtain ⟨v,hvZ,hvP,hvy⟩ := maximum_one_tail_last_arc_hit T hs hm r L hl j hij Q E
    (hP' ▸ hp) (congrArg Walk.toSubgraph hP') hyr (X.append Y) Z hC hE
  have huP' : u ∈ (T.walk j).support := hP.symm ▸ huP
  have hvP' : v ∈ (T.walk j).support := hP'.symm ▸ hvP
  have hur : u ≠ r := fun h ↦ hr (h ▸ huP')
  have hvr : v ≠ r := fun h ↦ hr (h ▸ hvP')
  have hc := hC ▸ L.isCycle
  have hXY := hc.isPath_of_append_left (Walk.not_nil_of_ne hyr)
  have hYZ : (Y.append Z).IsPath :=
    (show (X.append (Y.append Z)).IsCycle by simpa only [Walk.append_assoc] using hc).isPath_of_append_right
      (Walk.not_nil_of_ne hxr.symm)
  have huy : u ≠ y := by
    intro he
    have hh := path_append_support_inter X Y hXY huX (he ▸ Y.end_mem_support)
    exact hux hh
  have hvx : v ≠ x := by
    intro he
    have hh := path_append_support_inter Y Z hYZ (he ▸ Y.start_mem_support) hvZ
    exact hvy hh
  have huv : u ≠ v := by
    intro he
    have hh := cycle_append_support_inter X (Y.append Z)
      (by simpa only [Walk.append_assoc] using hc) huX
      ((Walk.mem_support_append_iff Y Z).mpr (Or.inr (he.symm ▸ hvZ)))
    exact hh.elim hur hux
  have hxC : x ∈ L.cycle.support := by
    rw [hC,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
    exact Or.inl (Or.inl X.end_mem_support)
  have hyC : y ∈ L.cycle.support := by
    rw [hC,Walk.mem_support_append_iff]
    exact Or.inr Z.start_mem_support
  have huC : u ∈ L.cycle.support := by
    rw [hC,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
    exact Or.inl (Or.inl huX)
  have hvC : v ∈ L.cycle.support := by
    rw [hC,Walk.mem_support_append_iff]
    exact Or.inr hvZ
  have hxP : x ∈ (T.walk j).support := by
    rw [hP,Walk.mem_support_append_iff]
    exact Or.inl A.end_mem_support
  have hyP : y ∈ (T.walk j).support := by
    rw [hP',Walk.mem_support_append_iff]
    exact Or.inr E.start_mem_support
  refine ⟨u,v,?_,?_⟩
  · simp [Set.ncard_insert_of_notMem,hxy,hux.symm,hvx.symm,huy.symm,hvy.symm,huv]
  · rintro z (rfl|rfl|rfl|rfl)
    · exact ⟨L.cycle.mem_verts_toSubgraph.mpr hxC,(T.walk j).mem_verts_toSubgraph.mpr hxP⟩
    · exact ⟨L.cycle.mem_verts_toSubgraph.mpr hyC,(T.walk j).mem_verts_toSubgraph.mpr hyP⟩
    · exact ⟨L.cycle.mem_verts_toSubgraph.mpr huC,(T.walk j).mem_verts_toSubgraph.mpr huP'⟩
    · exact ⟨L.cycle.mem_verts_toSubgraph.mpr hvC,(T.walk j).mem_verts_toSubgraph.mpr hvP'⟩

lemma maximum_one_tail_four_cycle_visits {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) (hr : r ∉ (T.walk j).support)
    (hhit : ∃ v ∈ (T.walk j).support, v ∈ L.cycle.support) :
    4 ≤ (L.cycle.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  obtain ⟨x,hxC,A,B,hP,hA⟩ := QuadrilateralAbsorption.first_hit_split
    (T.walk j) {z | z ∈ L.cycle.support} hhit
  obtain ⟨y,hyC,M,E,hB,hE⟩ := CycleDefect.last_hit_split B {z | z ∈ L.cycle.support}
    ⟨x,B.start_mem_support,hxC⟩
  have hxP : x ∈ (T.walk j).support := by
    rw [hP,Walk.mem_support_append_iff]
    exact Or.inl A.end_mem_support
  have hyP : y ∈ (T.walk j).support := by
    rw [hP,hB,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
    exact Or.inr (Or.inr E.start_mem_support)
  have hxr : x ≠ r := fun hh ↦ hr (hh ▸ hxP)
  have hyr : y ≠ r := fun hh ↦ hr (hh ▸ hyP)
  have hPE : T.walk j=(A.append M).append E := by rw [hP,hB,Walk.append_assoc]
  have hxy : x ≠ y := by
    intro he
    subst y
    have hM : M=Walk.nil := (Walk.isPath_iff_eq_nil M).mp
      ((hB ▸ (hP ▸ hp).of_append_right).of_append_left)
    have hBE : B=E := by simpa only [hM,Walk.nil_append] using hB
    apply maximum_one_tail_no_one_touch T hs hm r L hl j hij A B
      (hP ▸ hp) (congrArg Walk.toSubgraph hP) hxr hxC
    intro z hz hzC
    rcases (Walk.mem_support_append_iff A B).mp hz with hz|hz
    · exact hA z hz hzC
    · exact hE z (hBE ▸ hz) hzC
  obtain ⟨X,Y,hC⟩ := L.cycle.mem_support_iff_exists_append.mp hxC
  have hyXY : y ∈ (X.append Y).support := hC ▸ hyC
  rcases (Walk.mem_support_append_iff X Y).mp hyXY with hyX|hyY
  · obtain ⟨U,W,hX⟩ := X.mem_support_iff_exists_append.mp hyX
    have hCr : (reverseCycleRep T r L).cycle=(Y.reverse.append W.reverse).append U.reverse := by
      simp only [reverseCycleRep,hC,hX,Walk.reverse_append,Walk.append_assoc]
    obtain ⟨u,v,hcard,hsub⟩ := ordered_boundary_four_visits T hs hm r (reverseCycleRep T r L)
      hl j hij hr hxy hxr hyr A B hP (A.append M) E hPE
      (by intro z hz hzC; exact hA z hz (by simpa [reverseCycleRep] using hzC))
      (by intro z hz hzC; exact hE z hz (by simpa [reverseCycleRep] using hzC))
      Y.reverse W.reverse U.reverse hCr
    have hh := Set.ncard_le_ncard hsub
    simpa only [hcard,reverseCycleRep,Walk.toSubgraph_reverse] using hh
  · obtain ⟨U,W,hY⟩ := Y.mem_support_iff_exists_append.mp hyY
    obtain ⟨u,v,hcard,hsub⟩ := ordered_boundary_four_visits T hs hm r L
      hl j hij hr hxy hxr hyr A B hP (A.append M) E hPE hA hE X U W
      (by simp only [hC,hY,Walk.append_assoc])
    have hh := Set.ncard_le_ncard hsub
    rwa [hcard] at hh

lemma maximum_one_tail_pentagon_avoider_contains {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1) (hc : L.cycle.length=5)
    (j : Fin k) (hij : L.index ≠ j) (hr : r ∉ (T.walk j).support)
    (hhit : ∃ v ∈ (T.walk j).support, v ∈ L.cycle.support) :
    ∀ v ∈ L.cycle.support, v ≠ r → v ∈ (T.walk j).support := by
  have hfour := maximum_one_tail_four_cycle_visits T hs hm r L hl j hij hr hhit
  have hcard : (L.cycle.toSubgraph.verts \ {r}).ncard=4 := by
    rw [Set.ncard_diff_singleton_of_mem L.cycle.start_mem_verts_toSubgraph,
      Walk.verts_toSubgraph,cycle_support_ncard L.isCycle,hc]
  have hsub : L.cycle.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts ⊆
      L.cycle.toSubgraph.verts \ {r} := by
    intro v hv
    refine ⟨hv.1,?_⟩
    intro he
    have he : v=r := he
    exact hr (he ▸ (T.walk j).mem_verts_toSubgraph.mp hv.2)
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega)
  intro v hv hvr
  have hvm : v ∈ L.cycle.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts := by
    rw [heq]
    exact ⟨L.cycle.mem_verts_toSubgraph.mpr hv,hvr⟩
  exact (T.walk j).mem_verts_toSubgraph.mp hvm.2

end Erdos583OneTailCycleVisitsDevelopment
