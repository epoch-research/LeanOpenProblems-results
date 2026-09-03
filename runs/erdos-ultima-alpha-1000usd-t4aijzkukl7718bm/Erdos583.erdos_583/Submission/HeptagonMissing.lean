import Submission.Work
import Submission.HeptagonCoordinates
import Submission.HeptagonPieceSystem
import Submission.PathRestoreIntersection
import Submission.HeptagonExceptional

/-! A seven-cycle and an intersecting path are absorbable if a cycle vertex is missing. -/
namespace Erdos583HeptagonMissingDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583Work.PathIntervals Erdos583Work.OrderedPathPieces
open Erdos583HeptagonRoutesDevelopment Erdos583HeptagonCoordinatesDevelopment
open Erdos583HeptagonPieceSystemDevelopment Erdos583PathRestoreIntersectionDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {r a b : V}

lemma ordered_first_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support)
    (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc)
    (hfirst : adjacent (p 0) (p 1)) : TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  have h01 : h 0 ≤ h 1 := hh.monotone (by decide)
  have hform := split_interval P h01 (hb 1)
  have hA : ∀ x ∈ (P.take (h 0)).support, x ∈ C.support → x=P.getVert (h 0) := by
    intro x hx hxC
    obtain ⟨m,hm,hxm⟩ := (take_support P (hb 0) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp hmiss h p hpinj hb hc
      (hm.trans (hb 0)) (hxm ▸ hxC)
    have hlo := hh.monotone (Fin.zero_le j)
    have hm0 : m=h 0 := by omega
    exact hm0 ▸ hxm
  have hB : ∀ x ∈ (interval P (h 0) (h 1) h01).support, x ∈ C.support →
      x=P.getVert (h 0) ∨ x=P.getVert (h 1) := by
    intro x hx hxC
    obtain ⟨m,hm0,hm1,hxm⟩ := (interval_support P h01 (hb 1) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp hmiss h p hpinj hb hc
      (hm1.trans (hb 1)) (hxm ▸ hxC)
    have hj1 : j ≤ (1 : Fin 6) := hh.le_iff_le.mp (by omega)
    have hvj : j.val ≤ 1 := hj1
    by_cases hj0 : j.val=0
    · have he : j=0 := Fin.ext hj0
      exact Or.inl (by rwa [hj,he] at hxm)
    · have he : j=1 := Fin.ext (show j.val=1 by omega)
      exact Or.inr (by rwa [hj,he] at hxm)
  have hadj : C.toSubgraph.Adj (P.getVert (h 0)) (P.getVert (h 1)) := by
    rw [hc 0,hc 1]
    exact coordinates_cycle_adj C hl _ _ hfirst
  have hcover := CycleFirstVisits.cycle_adjacent_first_absorption C hC (P.take (h 0))
    (interval P (h 0) (h 1) h01) (P.drop (h 1)) (hform ▸ hp) hA hB hadj (hform ▸ hd.symm)
  simpa only [←hform,Set.union_comm] using hcover

lemma nonabsorbable_outer_chords (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hno : ¬TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet))
    (hmiss : r ∉ P.support)
    (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc) :
    ¬adjacent (p 0) (p 1) ∧ ¬adjacent (p 4) (p 5) := by
  constructor
  · exact fun ha ↦ hno (ordered_first_absorption C hC hl P hp hd hmiss h p hh hpinj hb hc ha)
  · intro ha
    let h' (i : Fin 6) := P.length-h i.rev
    let p' (i : Fin 6) := p i.rev
    have hh' : StrictMono h' := by
      intro i j hij
      have hlt := hh (Fin.rev_lt_rev.mpr hij)
      have hi := hb i.rev
      have hj := hb j.rev
      change P.length-h i.rev < P.length-h j.rev
      omega
    have hp' : Function.Injective p' := hpinj.comp Fin.rev_injective
    have hb' (i : Fin 6) : h' i ≤ P.reverse.length := by simp only [h',Walk.length_reverse]; omega
    have hc' (i : Fin 6) : P.reverse.getVert (h' i)=coordinates C (p' i).castSucc := by
      rw [Walk.getVert_reverse]
      have he : P.length-h' i=h i.rev := by dsimp [h']; have hi := hb i.rev; omega
      rw [he]
      exact hc i.rev
    have ha' : adjacent (p' 0) (p' 1) := by
      change adjacent (p 5) (p 4)
      exact ha.elim Or.inr Or.inl
    have he := ordered_first_absorption C hC hl P.reverse hp.reverse (by simpa using hd) (by simpa using hmiss)
      h' p' hh' hp' hb' hc' ha'
    exact hno (by simpa using he)

lemma six_visit_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support) (hvisit : ∀ i : Fin 6, coordinates C i.castSucc ∈ P.support) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  by_contra hno
  have hf := coordinates_injective C hC hl
  obtain ⟨h,p,hh,hpinj,hb,hc⟩ := HexagonExcursionCoordinates.ordered_vertices P
    (fun i : Fin 6 ↦ coordinates C i.castSucc) (hf.comp (Fin.castSucc_injective 6)) hvisit
  obtain ⟨hfirst,hlast⟩ := nonabsorbable_outer_chords C hC hl P hp hd hno hmiss h p hh hpinj hb hc
  by_cases hex : Exceptional p
  · exact (hno (Erdos583HeptagonExceptionalDevelopment.exceptional_absorption C hC hl P hp hd hmiss
      h p hh hpinj hb hc hex)).elim
  have ha := coordinates_adj C hl
  have hmiss' : coordinates C 6 ∉ P.support := by rwa [coordinates_last C hl]
  have havoid (i : Fin 7) : s(coordinates C i,coordinates C (next i)) ∉ P.edges := by
    intro he
    have heC : s(coordinates C i,coordinates C (next i)) ∈ C.toSubgraph.edgeSet := by
      rw [coordinates_edges C hl]
      exact Set.mem_iUnion.mpr ⟨i,rfl⟩
    exact Set.disjoint_left.mp hd heC (P.mem_edges_toSubgraph.mpr he)
  obtain ⟨X,Y,hX,hY,hXY,hE,hXs,hYs⟩ := ordered_absorption p (coordinates C) P h hh hc ha
    hmiss' hpinj hf hp hfirst hlast hex hb havoid
  have hCe : cycleEdges (coordinates C)=C.toSubgraph.edgeSet := (coordinates_edges C hl).symm
  rw [hCe] at hE
  let X' := X.copy (hc 0).symm rfl
  let Y' := Y.copy (hc 5).symm rfl
  have hXe : X'.toSubgraph=X.toSubgraph := NormalTrailSystem.walk_copy_subgraph X _ _
  have hYe : Y'.toSubgraph=Y.toSubgraph := NormalTrailSystem.walk_copy_subgraph Y _ _
  apply hno
  apply restore_two_on_path P hp (hh.monotone (Fin.zero_le _)) (hb 5) X' Y'
    (by simpa only [X',Walk.isPath_copy] using hX) (by simpa only [Y',Walk.isPath_copy] using hY)
    (by simpa only [hXe,hYe] using hXY) C.toSubgraph.edgeSet hd
    (by simpa only [hXe,hYe] using hE)
  · simpa only [X',Walk.support_copy] using hXs
  · simpa only [Y',Walk.support_copy] using hYs

lemma missing_start_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support) (hinter : ∃ x ∈ P.support, x ∈ C.support) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  by_cases hsmall : (C.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 5
  · exact CycleIntersectionSix.five_intersection_absorption C hC (by omega) P hp hsmall hinter hd
  apply six_visit_absorption C hC hl P hp hd hmiss
  intro i
  by_contra himiss
  have hir : coordinates C i.castSucc ≠ r := by
    intro he
    have hh := coordinates_injective C hC hl (he.trans (coordinates_last C hl).symm)
    have hv := congrArg Fin.val hh
    norm_num at hv
    omega
  have hd' : Disjoint (C.toSubgraph.verts ∩ P.toSubgraph.verts) {r,coordinates C i.castSucc} := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases (show x=r ∨ x=coordinates C i.castSucc by simpa using hy) with rfl|rfl
    · exact hmiss (P.mem_verts_toSubgraph.mp hx.2)
    · exact himiss (P.mem_verts_toSubgraph.mp hx.2)
  have hsub : (C.toSubgraph.verts ∩ P.toSubgraph.verts) ∪ {r,coordinates C i.castSucc} ⊆ C.toSubgraph.verts := by
    intro x hx
    rcases hx with hx|hx
    · exact hx.1
    · rcases (show x=r ∨ x=coordinates C i.castSucc by simpa using hx) with rfl|rfl
      · exact C.start_mem_verts_toSubgraph
      · exact C.mem_verts_toSubgraph.mpr (C.getVert_mem_support _)
  have hc := Set.ncard_mono hsub
  rw [Set.ncard_union_eq hd',Set.ncard_pair hir.symm,Walk.verts_toSubgraph,cycle_support_ncard hC,hl] at hc
  simp only [Walk.verts_toSubgraph] at hsmall hc
  omega

lemma missing_vertex_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath)
    (hmiss : ∃ x ∈ C.support, x ∉ P.support) (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨x,hxC,hxP⟩ := hmiss
  let D := C.rotate hxC
  have hD : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hxC
  have hDl : D.length=7 := by
    have hh := congrArg Walk.length (C.take_spec hxC)
    simpa only [D,Walk.rotate,Walk.length_append,hl,Nat.add_comm] using hh
  have hint : ∃ y ∈ P.support, y ∈ D.support := by
    obtain ⟨y,hyP,hyC⟩ := hinter
    exact ⟨y,hyP,by rwa [←Walk.mem_verts_toSubgraph,hD,Walk.mem_verts_toSubgraph]⟩
  have hh := missing_start_absorption D (hC.rotate hxC) hDl P hp (by rw [hD]; exact hd) hxP hint
  simpa only [hD] using hh

lemma small_intersection_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath)
    (hsmall : (C.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 6)
    (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  apply missing_vertex_absorption C hC hl P hp _ hinter hd
  by_contra! hall
  have hsub : C.toSubgraph.verts ⊆ P.toSubgraph.verts := by
    intro x hx
    exact P.mem_verts_toSubgraph.mpr (hall x (C.mem_verts_toSubgraph.mp hx))
  rw [Set.inter_eq_left.mpr hsub,Walk.verts_toSubgraph,cycle_support_ncard hC,hl] at hsmall
  omega

end Erdos583HeptagonMissingDevelopment
