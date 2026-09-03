import Submission.ArcRoundTrip
import Submission.MatchingBundleRightCover
import Submission.NegativeInner

/-!
If triangles through edges are unique and two disjoint triangles cannot be
joined by a perfect matching, the biclique right adjoint is countably covered.
The hypotheses here are not asserted for arbitrary K4-free graphs.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NoPrismRight
open Erdos595Work Erdos595ArcAdjoint Erdos595ArcRoundTrip
open Erdos595MatchingBundle
variable {V : Type*} (H : SimpleGraph V)

/-- A triangular prism, not necessarily induced, with disjoint triangle sides. -/
def NoPrism : Prop :=
  ∀ x y z a b c, H.Adj x y → H.Adj x z → H.Adj y z →
    H.Adj a b → H.Adj a c → H.Adj b c →
    H.Adj x a → H.Adj y b → H.Adj z c →
    Disjoint ({x,y,z} : Set V) {a,b,c} → False

private lemma shared_match (hU : UniqueTriangleEdge H)
    {x y z a c : V} (hxy : H.Adj x y) (hxz : H.Adj x z) (hyz : H.Adj y z)
    (hax : H.Adj a x) (hac : H.Adj a c) (hxc : H.Adj x c) (hzc : H.Adj z c) :
    a = z ∧ c = y := by
  have hyc := hU hxz hxy hyz.symm hxc hzc
  subst c
  have hza := hU hxy hxz hyz hax.symm hac.symm
  exact ⟨hza.symm,rfl⟩

/-- In a locally matching graph, matched triangles which overlap are identical. -/
lemma matched_equal_of_overlap (hU : UniqueTriangleEdge H)
    {x y z a b c : V} (hxy : H.Adj x y) (hxz : H.Adj x z) (hyz : H.Adj y z)
    (hab : H.Adj a b) (hac : H.Adj a c) (hbc : H.Adj b c)
    (hxa : H.Adj x a) (hyb : H.Adj y b) (hzc : H.Adj z c)
    (hd : ¬Disjoint ({x,y,z} : Set V) {a,b,c}) :
    ({x,y,z} : Set V) = {a,b,c} := by
  obtain ⟨t,ht,hs⟩ := Set.not_disjoint_iff.mp hd
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht hs
  rcases ht with rfl | rfl | rfl
  · rcases hs with rfl | rfl | rfl
    · exact (hxa.ne rfl).elim
    · obtain ⟨rfl,rfl⟩ := shared_match H hU hxy hxz hyz hab hac hbc hzc
      ext t
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    · obtain ⟨rfl,rfl⟩ := shared_match H hU hxz hxy hyz.symm hac hab hbc.symm hyb
      ext t
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
  · rcases hs with rfl | rfl | rfl
    · obtain ⟨rfl,rfl⟩ := shared_match H hU hxy.symm hyz hxz hab.symm hbc hac hzc
      ext t
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    · exact (hyb.ne rfl).elim
    · obtain ⟨rfl,rfl⟩ := shared_match H hU hyz hxy.symm hxz.symm hbc hab.symm hac.symm hxa
      ext t
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
  · rcases hs with rfl | rfl | rfl
    · obtain ⟨rfl,rfl⟩ := shared_match H hU hxz.symm hyz.symm hxy hac.symm hbc.symm hab hyb
      ext t
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    · obtain ⟨rfl,rfl⟩ := shared_match H hU hyz.symm hxz.symm hxy.symm hbc.symm hac.symm hab.symm hxa
      ext t
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    · exact (hzc.ne rfl).elim

lemma matched_equal (hU : UniqueTriangleEdge H) (hP : NoPrism H)
    {x y z a b c : V} (hxy : H.Adj x y) (hxz : H.Adj x z) (hyz : H.Adj y z)
    (hab : H.Adj a b) (hac : H.Adj a c) (hbc : H.Adj b c)
    (hxa : H.Adj x a) (hyb : H.Adj y b) (hzc : H.Adj z c) :
    ({x,y,z} : Set V) = {a,b,c} :=
  matched_equal_of_overlap H hU hxy hxz hyz hab hac hbc hxa hyb hzc
    (hP x y z a b c hxy hxz hyz hab hac hbc hxa hyb hzc)

private lemma nonstar_left_independent (hU : UniqueTriangleEdge H)
    {p : Biclique H} (hp : ¬Star H p) {a b c : V}
    (ha : a ∈ Left H p) (hb : b ∈ Left H p) (hc : c ∈ Right H p) : ¬H.Adj a b := by
  intro hab
  apply hp
  right
  refine ⟨c,Set.eq_singleton_iff_unique_mem.mpr ⟨hc,?_⟩⟩
  intro d hd
  exact hU hab (p.property _ ha _ hd) (p.property _ hb _ hd)
    (p.property _ ha _ hc) (p.property _ hb _ hc)

private lemma nonstar_right_independent (hU : UniqueTriangleEdge H)
    {p : Biclique H} (hp : ¬Star H p) {a b c : V}
    (ha : a ∈ Right H p) (hb : b ∈ Right H p) (hc : c ∈ Left H p) : ¬H.Adj a b := by
  intro hab
  apply hp
  left
  refine ⟨c,Set.eq_singleton_iff_unique_mem.mpr ⟨hc,?_⟩⟩
  intro d hd
  exact hU hab (p.property _ hd _ ha).symm (p.property _ hd _ hb).symm
    (p.property _ hc _ ha).symm (p.property _ hc _ hb).symm

/-- Every vertex of a right-adjoint triangle has a singleton side. -/
theorem triangle_star (hU : UniqueTriangleEdge H) (hP : NoPrism H)
    {p q r : Biclique H} (hpq : (right H).Adj p q)
    (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) : Star H p := by
  classical
  by_contra hp
  let s := six H hpq hpr hqr
  have ht := s.tri H
  have ht' := s.tri' H
  have hxx' := q.property _ s.hx.2 _ s.hx'.1
  have hyy' := r.property _ s.hy.2 _ s.hy'.1
  have hzz' := p.property _ s.hz.2 _ s.hz'.1
  have he := matched_equal H hU hP ht.1 ht.2.1 ht.2.2 ht'.1 ht'.2.1 ht'.2.2
    hxx' hyy' hzz'
  have hx' : s.x' ∈ ({s.x,s.y,s.z} : Set V) := by rw [he]; simp
  have hz' : s.z' ∈ ({s.x,s.y,s.z} : Set V) := by rw [he]; simp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx' hz'
  have hxe : s.x' = s.z := by
    rcases hx' with hx' | hx' | hx'
    · exact (hxx'.ne hx'.symm).elim
    · exact (nonstar_left_independent H hU hp s.hz.2 s.hx'.2 s.hx.1
        (hx'.symm ▸ ht.2.2.symm)).elim
    · exact hx'
  have hze : s.z' = s.x := by
    rcases hz' with hz' | hz' | hz'
    · exact hz'
    · exact (nonstar_right_independent H hU hp s.hx.1 s.hz'.1 s.hz.2
        (hz'.symm ▸ ht.1)).elim
    · exact (hzz'.ne hz'.symm).elim
  have hxy' : H.Adj s.x s.y' := by simpa only [hze] using ht'.2.2.symm
  have hzy' : H.Adj s.z s.y' := by simpa only [hxe] using ht'.1
  have hye := hU ht.2.1 ht.1 ht.2.2.symm hxy' hzy'
  exact hyy'.ne hye

/-- Adjacent stars on a triangle have adjacent centers in the original graph. -/
lemma centers_adj {p q r : Biclique H} (s : Six H p q r)
    (hp : Star H p) (hq : Star H q) : H.Adj (center H p hp) (center H q hq) := by
  have ht := s.tri H
  have hn := centers_ne H s hp hq
  rcases center_spec H p hp with hp' | hp' <;>
    rcases center_spec H q hq with hq' | hq'
  · have hz : s.z = center H p hp := by simpa only [hp',Set.mem_singleton_iff] using s.hz.2
    have hx : s.x = center H q hq := by simpa only [hq',Set.mem_singleton_iff] using s.hx.2
    simpa only [hz,hx] using ht.2.1.symm
  · have hz : s.z = center H p hp := by simpa only [hp',Set.mem_singleton_iff] using s.hz.2
    have hy : s.y = center H q hq := by simpa only [hq',Set.mem_singleton_iff] using s.hy.1
    simpa only [hz,hy] using ht.2.2.symm
  · have hx : s.x = center H p hp := by simpa only [hp',Set.mem_singleton_iff] using s.hx.1
    have hx' : s.x = center H q hq := by simpa only [hq',Set.mem_singleton_iff] using s.hx.2
    exact (hn (hx.symm.trans hx')).elim
  · have hx : s.x = center H p hp := by simpa only [hp',Set.mem_singleton_iff] using s.hx.1
    have hy : s.y = center H q hq := by simpa only [hq',Set.mem_singleton_iff] using s.hy.1
    simpa only [hx,hy] using ht.1

/-- Mapping triangles is enough; no assertion about other edges is needed. -/
theorem cover_of_star_triangles
    (hs : ∀ {p q r : Biclique H}, (right H).Adj p q → (right H).Adj p r →
      (right H).Adj q r → Star H p)
    (hH : IsCountableUnionOfTriangleFree H) : IsCountableUnionOfTriangleFree (right H) := by
  classical
  obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring H).mp hH
  letI : LinearOrder (Biclique H) := IsWellOrder.linearOrder WellOrderingRel
  let code (p q : Biclique H) : ℕ :=
    if hp : Star H p then if hq : Star H q then c s(center H p hp,center H q hq) else 0 else 0
  apply Erdos595NegativeInner.cover_of_ordered_patterns (right H) code
  intro p q r _ _ hpq hpr hqr hm
  have hp := hs hpq hpr hqr
  have hq := hs hpq.symm hqr hpr
  have hr := hs hpr.symm hqr.symm hpq
  simp only [code,dif_pos hp,dif_pos hq,dif_pos hr] at hm
  exact hc (center H p hp) (center H q hq) (center H r hr)
    (centers_adj H (six H hpq hpr hqr) hp hq)
    (centers_adj H (six H hpr hpq hqr.symm) hp hr)
    (centers_adj H (six H hqr hpq.symm hpr.symm) hq hr) hm

/-- The original graph is covered because every edge has at most one triangle. -/
theorem base_cover (hU : UniqueTriangleEdge H) : IsCountableUnionOfTriangleFree H := by
  apply countable_union_of_countable_common_neighbors
  intro a b hab
  apply Set.Subsingleton.countable
  intro x hx y hy
  exact hU hab hx.1 hx.2 hy.1 hy.2

theorem right_cover (hU : UniqueTriangleEdge H) (hP : NoPrism H) :
    IsCountableUnionOfTriangleFree (right H) :=
  cover_of_star_triangles H (triangle_star H hU hP) (base_cover H hU)

#print axioms matched_equal_of_overlap
#print axioms triangle_star
#print axioms cover_of_star_triangles
#print axioms right_cover
end Erdos595NoPrismRight
