import Submission.NoPrismSecondRightCover

/-!
For a graph with unique triangles through edges, every triangle in its
biclique right adjoint consists either entirely of stars or entirely of
nonstars. This isolates the nonstar part of the second-right covering
problem; no cover of that remaining part is asserted.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595MixedStarTriangle
open Erdos595Work Erdos595ArcAdjoint Erdos595ArcRoundTrip Erdos595MatchingBundle
variable {V : Type*} (H : SimpleGraph V)

lemma left_independent (hu : UniqueTriangleEdge H)
    {p : Biclique H} (hp : ¬Star H p) {a b c : V}
    (ha : a ∈ Left H p) (hb : b ∈ Left H p) (hc : c ∈ Right H p) : ¬H.Adj a b := by
  intro hab
  apply hp
  right
  refine ⟨c,Set.eq_singleton_iff_unique_mem.mpr ⟨hc,?_⟩⟩
  intro d hd
  exact hu hab (p.property _ ha _ hd) (p.property _ hb _ hd)
    (p.property _ ha _ hc) (p.property _ hb _ hc)

lemma right_independent (hu : UniqueTriangleEdge H)
    {p : Biclique H} (hp : ¬Star H p) {a b c : V}
    (ha : a ∈ Right H p) (hb : b ∈ Right H p) (hc : c ∈ Left H p) : ¬H.Adj a b := by
  intro hab
  apply hp
  left
  refine ⟨c,Set.eq_singleton_iff_unique_mem.mpr ⟨hc,?_⟩⟩
  intro d hd
  exact hu hab (p.property _ hd _ ha).symm (p.property _ hd _ hb).symm
    (p.property _ hc _ ha).symm (p.property _ hc _ hb).symm

/-- In the nonstar case, the two witness triangles of a right-adjoint
triangle are disjoint. In particular the associated prism is genuine. -/
lemma disjoint_of_nonstar (hu : UniqueTriangleEdge H)
    {p q r : Biclique H} (s : Six H p q r) (hp : ¬Star H p) :
    Disjoint ({s.x,s.y,s.z} : Set V) {s.x',s.y',s.z'} := by
  by_contra hd
  have ht := s.tri H
  have ht' := s.tri' H
  have hxx' := q.property _ s.hx.2 _ s.hx'.1
  have hyy' := r.property _ s.hy.2 _ s.hy'.1
  have hzz' := p.property _ s.hz.2 _ s.hz'.1
  have he := Erdos595NoPrismRight.matched_equal_of_overlap H hu
    ht.1 ht.2.1 ht.2.2 ht'.1 ht'.2.1 ht'.2.2 hxx' hyy' hzz' hd
  have hx' : s.x' ∈ ({s.x,s.y,s.z} : Set V) := by rw [he]; simp
  have hz' : s.z' ∈ ({s.x,s.y,s.z} : Set V) := by rw [he]; simp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx' hz'
  have hxe : s.x' = s.z := by
    rcases hx' with hx' | hx' | hx'
    · exact (hxx'.ne hx'.symm).elim
    · exact (left_independent H hu hp s.hz.2 s.hx'.2 s.hx.1
        (hx'.symm ▸ ht.2.2.symm)).elim
    · exact hx'
  have hze : s.z' = s.x := by
    rcases hz' with hz' | hz' | hz'
    · exact hz'
    · exact (right_independent H hu hp s.hx.1 s.hz'.1 s.hz.2
        (hz'.symm ▸ ht.1)).elim
    · exact (hzz'.ne hz'.symm).elim
  have hxy' : H.Adj s.x s.y' := by simpa only [hze] using ht'.2.2.symm
  have hzy' : H.Adj s.z s.y' := by simpa only [hxe] using ht'.1
  exact hyy'.ne (hu ht.2.1 ht.1 ht.2.2.symm hxy' hzy')

lemma star_of_star (hu : UniqueTriangleEdge H)
    {p q r : Biclique H} (s : Six H p q r) (hq : Star H q) : Star H p := by
  by_contra hp
  have hd := disjoint_of_nonstar H hu s hp
  rcases hq with ⟨a,ha⟩ | ⟨a,ha⟩
  · have hx : s.x = a := by simpa only [ha,Set.mem_singleton_iff] using s.hx.2
    have hy : s.y' = a := by simpa only [ha,Set.mem_singleton_iff] using s.hy'.2
    exact Set.disjoint_left.mp hd (by simp : s.x ∈ ({s.x,s.y,s.z} : Set V))
      (by simp [hx,hy])
  · have hx : s.x' = a := by simpa only [ha,Set.mem_singleton_iff] using s.hx'.1
    have hy : s.y = a := by simpa only [ha,Set.mem_singleton_iff] using s.hy.1
    exact Set.disjoint_left.mp hd (by simp : s.y ∈ ({s.x,s.y,s.z} : Set V))
      (by simp [hx,hy])

lemma star_iff (hu : UniqueTriangleEdge H) {p q r : Biclique H}
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hqr : (right H).Adj q r) : Star H p ↔ Star H q :=
  ⟨star_of_star H hu (six H hpq.symm hqr hpr),
    star_of_star H hu (six H hpq hpr hqr)⟩

noncomputable def kind (p : Biclique H) : Bool := by
  classical
  exact decide (Star H p)

lemma triangles_in_kinds (hu : UniqueTriangleEdge H) :
    Erdos595TriangleFiber.TrianglesInFibers (right H) (kind H) := by
  intro p q r hpq hpr hqr
  simp only [kind,decide_eq_decide]
  exact ⟨star_iff H hu hpq hpr hqr,star_iff H hu hpr hpq hqr.symm⟩

abbrev nonstars := (right H).induce {p | ¬Star H p}

/-- Once the first right stage is covered, only its nonstar part can
obstruct covering the second stage. No no-prism hypothesis is used. -/
theorem second_cover_iff (hu : UniqueTriangleEdge H)
    (hc : IsCountableUnionOfTriangleFree (right H)) :
    IsCountableUnionOfTriangleFree (right (right H)) ↔
      IsCountableUnionOfTriangleFree (right (nonstars H)) := by
  constructor
  · intro h
    exact countable_union_of_hom
      (Erdos595RightFiber.rightHom
        (SimpleGraph.Embedding.induce {p | ¬Star H p}).toHom) h
  · intro h
    apply Erdos595RightFiber.cover_of_fibers (right H) (kind H) (triangles_in_kinds H hu)
    intro i
    cases i
    · have he : {p : Biclique H | kind H p = false} = {p | ¬Star H p} := by
        ext p
        simp [kind]
      rw [he]
      exact h
    · have he : {p : Biclique H | kind H p = true} = {p | Star H p} := by
        ext p
        simp [kind]
      rw [he]
      apply countable_union_of_hom
        (Erdos595RightFiber.rightHom (Erdos595NoPrismSecondRight.starHom H))
      exact Erdos595CartesianBoolRight.right_cover H hc

#print axioms disjoint_of_nonstar
#print axioms star_iff
#print axioms second_cover_iff
end Erdos595MixedStarTriangle
