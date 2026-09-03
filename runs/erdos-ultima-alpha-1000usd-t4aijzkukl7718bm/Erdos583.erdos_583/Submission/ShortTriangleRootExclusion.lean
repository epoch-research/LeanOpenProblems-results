import Submission.TriangleTailPentagonTransfer

/-! A two-edge tail at a shortest rooted triangle cannot have another root endpoint in a smallest failure. -/
namespace Erdos583ShortTriangleRootExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583TriangleTailRootTemplatesDevelopment Erdos583TriangleTailPentagonTransferDevelopment
open Erdos583LollipopEndpointRotationDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

def swapFrame {V : Type*} {G : SimpleGraph V} {r x y s t : V}
    (F : Frame G r x y s t) : Frame G r y x s t :=
  ⟨F.ry,F.xy.symm,F.rx,F.rs,F.st,F.tr,F.sy,F.sx,F.ty,F.tx⟩

lemma swapFrame_edges {V : Type*} {G : SimpleGraph V} {r x y s t : V}
    (F : Frame G r x y s t) : (swapFrame F).edges=F.edges := by
  ext e
  simp only [Frame.edges,Set.mem_insert_iff,Set.mem_singleton_iff,
    Sym2.eq_swap (a := y) (b := x)]
  tauto

lemma triangle_two_tail_root_path_gives_pentagon {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ u : V, ∀ M : RootedCycleRep W u,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hcycle : L.cycle.length=3) (htail : L.tail.length=2)
    (j : Fin k) (hij : L.index ≠ j) {b : V}
    (P : G.Walk r b) (hp : P.IsPath) (hj : (T.walk j).toSubgraph=P.toSubgraph) :
    ∃ U : TrailFamily G k, ∃ C : G.Walk r r,
      U.score=T.score ∧ C.IsCycle ∧ C.length=5 ∧ (U.walk L.index).toSubgraph=C.toSubgraph := by
  classical
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hcycle
  obtain ⟨s,hrs,hst,hS⟩ := TriangleTailTwo.two_edge_form L.tail htail
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have hsS : s ∈ L.tail.support := by rw [hS]; simp
  have htS : L.finish ∈ L.tail.support := L.tail.end_mem_support
  have hsx : s ≠ x := by intro he; exact hrx.ne (L.inter x hxC (he ▸ hsS)).symm
  have hsy : s ≠ y := by intro he; exact hyr.ne (L.inter y hyC (he ▸ hsS))
  have htx : L.finish ≠ x := by intro he; exact hrx.ne (L.inter x hxC (he ▸ htS)).symm
  have hty : L.finish ≠ y := by intro he; exact hyr.ne (L.inter y hyC (he ▸ htS))
  have htr : L.finish ≠ r := by
    intro he
    have hh := (Walk.cons_isPath_iff hrs _).mp (hS ▸ L.isPath) |>.2
    exact hh (by simp [he])
  let F : Frame G r x y s L.finish := ⟨hrx,hxy,hyr.symm,hrs,hst,htr,hsx,hsy,htx,hty⟩
  have hframe : (T.walk L.index).toSubgraph.edgeSet=F.edges := by
    rw [L.subgraph,hC,hS]
    ext e
    simp only [Frame.edges,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,Walk.edges_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := y) (b := r)]
    tauto
  have hxAdj : L.cycle.toSubgraph.Adj r x := by
    change s(r,x) ∈ L.cycle.toSubgraph.edgeSet
    rw [hC]; simp
  have hyAdj : L.cycle.toSubgraph.Adj r y := by
    change s(r,y) ∈ L.cycle.toSubgraph.edgeSet
    rw [hC]; simp [Sym2.eq_swap]
  have htailSup : L.tail.support=[r,s,L.finish] := by rw [hS]; rfl
  have hmem (v : V) (hv : L.cycle.toSubgraph.Adj r v) : v ∈ P.support := by
    obtain ⟨w,A,f,B,hform,_,_⟩ := minimum_lollipop_root_path_predecessor T hm r L hmin j hij hv P hp hj
    rw [hform]; simp
  rcases two_visits_in_one_order P (hmem x hxAdj) (hmem y hyAdj) with ⟨A,B,D,hP⟩ | ⟨A,B,D,hP⟩
  · exact ordered_triangle_tail_pentagon_transfer T hs hm r L hmin F hxAdj hyAdj htailSup hframe
      j hij A B D (hP ▸ hp) (hj.trans (congrArg Walk.toSubgraph hP))
  · exact ordered_triangle_tail_pentagon_transfer T hs hm r L hmin (swapFrame F) hyAdj hxAdj htailSup
      (hframe.trans (swapFrame_edges F).symm) j hij A B D (hP ▸ hp) (hj.trans (congrArg Walk.toSubgraph hP))

lemma failure_short_triangle_no_other_root_endpoint {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ u : Fin n, ∀ M : RootedCycleRep W u,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hcycle : L.cycle.length=3) (htail : L.tail.length=2) :
    ∀ j, j ≠ L.index → T.start j ≠ r ∧ T.finish j ≠ r := by
  intro j hji
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hji
  have hno {a b : Fin n} (P : G.Walk a b) (hP : P.IsPath)
      (hj : (T.walk j).toSubgraph=P.toSubgraph) : a ≠ r := by
    rintro rfl
    obtain ⟨U,C,hUs,hC,hCl,hUi⟩ := triangle_two_tail_root_path_gives_pentagon T hs hm a L hmin hcycle htail j hji.symm P hP hj
    exact PentagonExclusion.failure_no_whole_pentagon hsmall hG hfail U (by omega)
      (fun W ↦ by rw [hUs]; exact hm W) L.index C hC hCl hUi
  exact ⟨hno (T.walk j) hp rfl,hno (T.walk j).reverse hp.reverse (Walk.toSubgraph_reverse _).symm⟩

lemma failure_two_tail_triangle_root_quota_one {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ u : Fin n, ∀ M : RootedCycleRep W u,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hcycle : L.cycle.length=3) (htail : L.tail.length=2) : T.quota r=1 := by
  classical
  have hn : ¬L.tail.Nil := fun h ↦ by have := Walk.nil_iff_length_eq.mp h; omega
  have hbr := (ContiguousRegion.path_ends_ne L.tail L.isPath hn).symm
  have hother := failure_short_triangle_no_other_root_endpoint hsmall hG hfail T hs hm r L hmin hcycle htail
  rw [quota_eq_sum_endpoints,Finset.sum_eq_single L.index]
  · simp [L.start_eq,L.finish_eq,hbr]
  · intro j _ hji
    simp only [if_neg (hother j hji).1,if_neg (hother j hji).2,add_zero]
  · simp

end Erdos583ShortTriangleRootExclusionDevelopment
