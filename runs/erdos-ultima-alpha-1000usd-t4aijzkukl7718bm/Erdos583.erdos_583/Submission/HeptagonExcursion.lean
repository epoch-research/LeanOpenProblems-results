import Submission.Work
import Submission.HeptagonExcursionCoordinates
import Submission.HeptagonExcursionPieceSystem
import Submission.CycleIntersectionSeven

/-! A nonabsorbable seven-cycle carrier cannot have an internal excursion. -/
namespace Erdos583HeptagonExcursionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.TriangleAbsorption
open Erdos583Work.PathIntervals Erdos583Work.PathIntervalRestore
open Erdos583Work.OrderedPathPieces Erdos583HeptagonExcursionRoutesDevelopment
open Erdos583HeptagonExcursionCoordinatesDevelopment Erdos583HeptagonExcursionPieceSystemDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {r a b : V}

lemma ordered_first_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (h : Fin 7 → ℕ) (p : Fin 7 → Fin 7) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i))
    (hfirst : adjacent (p 0) (p 1)) : TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  have h01 : h 0 ≤ h 1 := hh.monotone (by decide)
  have hform := split_interval P h01 (hb 1)
  have hA : ∀ x ∈ (P.take (h 0)).support, x ∈ C.support → x=P.getVert (h 0) := by
    intro x hx hxC
    obtain ⟨m,hm,hxm⟩ := (take_support P (hb 0) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp h p hpinj hb hc
      (hm.trans (hb 0)) (hxm ▸ hxC)
    have hlo := hh.monotone (Fin.zero_le j)
    have hm0 : m=h 0 := by omega
    exact hm0 ▸ hxm
  have hB : ∀ x ∈ (interval P (h 0) (h 1) h01).support, x ∈ C.support →
      x=P.getVert (h 0) ∨ x=P.getVert (h 1) := by
    intro x hx hxC
    obtain ⟨m,hm0,hm1,hxm⟩ := (interval_support P h01 (hb 1) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp h p hpinj hb hc
      (hm1.trans (hb 1)) (hxm ▸ hxC)
    have hj1 : j ≤ (1 : Fin 7) := hh.le_iff_le.mp (by omega)
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
    (h : Fin 7 → ℕ) (p : Fin 7 → Fin 7) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i)) :
    ¬adjacent (p 0) (p 1) ∧ ¬adjacent (p 5) (p 6) := by
  constructor
  · exact fun ha ↦ hno (ordered_first_absorption C hC hl P hp hd h p hh hpinj hb hc ha)
  · intro ha
    let h' (i : Fin 7) := P.length-h i.rev
    let p' (i : Fin 7) := p i.rev
    have hh' : StrictMono h' := by
      intro i j hij
      have hlt := hh (Fin.rev_lt_rev.mpr hij)
      have hi := hb i.rev
      have hj := hb j.rev
      change P.length-h i.rev < P.length-h j.rev
      omega
    have hp' : Function.Injective p' := hpinj.comp Fin.rev_injective
    have hb' (i : Fin 7) : h' i ≤ P.reverse.length := by simp only [h',Walk.length_reverse]; omega
    have hc' (i : Fin 7) : P.reverse.getVert (h' i)=coordinates C (p' i) := by
      rw [Walk.getVert_reverse]
      have he : P.length-h' i=h i.rev := by dsimp [h']; have hi := hb i.rev; omega
      rw [he]
      exact hc i.rev
    have ha' : adjacent (p' 0) (p' 1) := by
      change adjacent (p 6) (p 5)
      exact ha.elim Or.inr Or.inl
    have he := ordered_first_absorption C hC hl P.reverse hp.reverse (by simpa using hd)
      h' p' hh' hp' hb' hc' ha'
    exact hno (by simpa using he)

omit [Fintype V] in
lemma ordered_gap_outside (C : G.Walk r r) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath)
    (h : Fin 7 → ℕ) (p : Fin 7 → Fin 7) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i))
    (d : Fin 6) {m : ℕ} (hmlo : h d.castSucc < m) (hmhi : m < h d.succ) :
    P.getVert m ∉ C.support := by
  intro hx
  obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp h p hpinj hb hc
    (hmhi.le.trans (hb d.succ)) hx
  have hlo : d.castSucc < j := hh.lt_iff_lt.mp (by omega)
  have hhi : j < d.succ := hh.lt_iff_lt.mp (by omega)
  have h1 : d.val < j.val := hlo
  have h2 : j.val < d.val+1 := hhi
  omega

omit [Fintype V] in
lemma adjacent_gap_has_outside_position (C : G.Walk r r) (hl : C.length=7)
    (P : G.Walk a b) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (h : Fin 7 → ℕ) (p : Fin 7 → Fin 7) (hh : StrictMono h)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i))
    (d : Fin 6) (ha : adjacent (p d.castSucc) (p d.succ)) :
    ∃ m, h d.castSucc < m ∧ m < h d.succ := by
  have hlt := hh (a := d.castSucc) (b := d.succ) Fin.castSucc_lt_succ
  have hne : h d.castSucc+1 ≠ h d.succ := by
    intro he
    have heC : C.toSubgraph.Adj (P.getVert (h d.castSucc)) (P.getVert (h d.succ)) := by
      rw [hc d.castSucc,hc d.succ]
      exact coordinates_cycle_adj C hl _ _ ha
    have heP : s(P.getVert (h d.castSucc),P.getVert (h d.succ)) ∈ P.toSubgraph.edgeSet := by
      rw [Walk.mem_edges_toSubgraph,edges_positions]
      exact ⟨h d.castSucc,hlt.trans_le (hb d.succ),by rw [he]⟩
    exact Set.disjoint_left.mp hd heC heP
  exact ⟨h d.castSucc+1,by omega,by omega⟩

lemma ordered_no_excursion (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hno : ¬TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet))
    (h : Fin 7 → ℕ) (p : Fin 7 → Fin 7) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i)) :
    ∀ x ∈ (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).support, x ∈ C.support := by
  intro x hx
  by_contra hxC
  obtain ⟨m,hm0,hm4,hxm⟩ := (interval_support P _ (hb 6) x).mp hx
  have hmnot (j : Fin 7) : m ≠ h j := by
    intro he
    apply hxC
    rw [hxm,he,hc j]
    exact C.getVert_mem_support _
  have hm4' : m < h 6 := by have hne := hmnot 6; omega
  obtain ⟨d0,hdlo,hdhi⟩ := between_indices h hm0 hm4'
  have hdlo' : h d0.castSucc < m := by have hne := hmnot d0.castSucc; omega
  let d := chosenGap p d0
  have hg : GoodGap p d := chosenGap_good p d0
  have hex : ∃ m', h d.castSucc < m' ∧ m' < h d.succ ∧ P.getVert m' ∉ C.support := by
    rcases chosenGap_spec p d0 with he|ha
    · exact ⟨m,by simpa only [d,he] using hdlo',by simpa only [d,he] using hdhi,
        fun hx ↦ hxC (hxm.symm ▸ hx)⟩
    · obtain ⟨m',hmlo,hmhi⟩ := adjacent_gap_has_outside_position C hl P hd h p hh hb hc d ha
      exact ⟨m',hmlo,hmhi,ordered_gap_outside C hl P hp h p hh hpinj hb hc d hmlo hmhi⟩
  obtain ⟨m',hmlo,hmhi,hmout⟩ := hex
  let x' := P.getVert m'
  let h' := insertCut h d m'
  let f : Fin 8 → V := Fin.lastCases x' (coordinates C)
  have hh' : StrictMono h' := insertCut_strictMono h hh d m' hmlo hmhi
  have hb' : ∀ i, h' i ≤ P.length := insertCut_bound h d m' P.length hb (hmhi.le.trans (hb d.succ))
  have hc' : ∀ i, P.getVert (h' i)=f (extended p d i) :=
    inserted_coordinates P (coordinates C) h p hc d m' x' rfl
  have hf : Function.Injective f := extend_injective (coordinates C) (coordinates_injective C hC hl) x'
    (fun i he ↦ hmout (by change x' ∈ C.support; rw [he]; exact C.getVert_mem_support _))
  have ha : ∀ i : Fin 7, G.Adj (f i.castSucc) (f (next i).castSucc) := by
    intro i
    simpa only [f,Fin.lastCases_castSucc,next] using coordinates_adj C hl i
  have hCe : cycleEdges f=C.toSubgraph.edgeSet := by
    rw [coordinates_edges C hl]
    simp only [cycleEdges,f,Fin.lastCases_castSucc,next]
  have havoid (i : Fin 7) : s(f i.castSucc,f (next i).castSucc) ∉ P.edges := by
    intro he
    have hCedge : s(f i.castSucc,f (next i).castSucc) ∈ C.toSubgraph.edgeSet := by
      rw [←hCe]
      exact Set.mem_iUnion.mpr ⟨i,rfl⟩
    exact Set.disjoint_left.mp hd hCedge (P.mem_edges_toSubgraph.mpr he)
  obtain ⟨hf1,hf2⟩ := nonabsorbable_outer_chords C hC hl P hp hd hno h p hh hpinj hb hc
  obtain ⟨X,Y,hX,hY,hdXY,heXY,hsX,hsY⟩ := ordered_absorption p d f P h' hh' hc' ha
    hg hpinj hf hp hf1 hf2 hb' havoid
  have hstart : f (p 0).castSucc=P.getVert (h 0) := by simpa only [f,Fin.lastCases_castSucc] using (hc 0).symm
  have hfinish : f (p 6).castSucc=P.getVert (h 6) := by simpa only [f,Fin.lastCases_castSucc] using (hc 6).symm
  let X' := X.copy hstart rfl
  let Y' := Y.copy hfinish rfl
  have hXe : X'.toSubgraph=X.toSubgraph := NormalTrailSystem.walk_copy_subgraph X _ _
  have hYe : Y'.toSubgraph=Y.toSubgraph := NormalTrailSystem.walk_copy_subgraph Y _ _
  have hmidE := interval_edges_congr P (hh'.monotone (Fin.zero_le (7 : Fin 8)))
    (hh.monotone (Fin.zero_le (6 : Fin 7))) (insertCut_zero h d m') (insertCut_last h d m')
  have hmidS := interval_support_congr P (hh'.monotone (Fin.zero_le (7 : Fin 8)))
    (hh.monotone (Fin.zero_le (6 : Fin 7))) (insertCut_zero h d m') (insertCut_last h d m')
  rw [hmidE,hCe] at heXY
  rw [hmidS] at hsX hsY
  apply hno
  apply restore_two P hp (hh.monotone (Fin.zero_le _)) (hb 6) X' Y'
    (by simpa only [X',Walk.isPath_copy] using hX) (by simpa only [Y',Walk.isPath_copy] using hY)
    (by simpa only [hXe,hYe] using hdXY) C.toSubgraph.edgeSet hd
    (by simpa only [hXe,hYe] using heXY)
  · simpa only [X',Walk.support_copy] using hsX
  · simpa only [Y',Walk.support_copy] using hsY

lemma nonabsorbable_contiguous (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hno : ¬TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet))
    (hvisit : ∀ x ∈ C.support, x ∈ P.support) :
    ∃ u v : V, ∃ A : G.Walk a u, ∃ Q : G.Walk u v, ∃ B : G.Walk v b,
      P=A.append (Q.append B) ∧ Q.IsPath ∧ Q.toSubgraph.verts=C.toSubgraph.verts ∧ Q.length=6 ∧
      (∀ x ∈ A.support, x ∈ C.support → x=u) ∧
      (∀ x ∈ B.support, x ∈ C.support → x=v) := by
  obtain ⟨h,p,hh,hpinj,hb,hc⟩ := ordered_vertices P (coordinates C) (coordinates_injective C hC hl)
    (fun i ↦ hvisit _ (C.getVert_mem_support _))
  let Q := interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))
  have hQ : Q.IsPath := interval_isPath P hp _
  have hinside := ordered_no_excursion C hC hl P hp hd hno h p hh hpinj hb hc
  have hverts : Q.toSubgraph.verts=C.toSubgraph.verts := by
    ext x
    rw [Walk.mem_verts_toSubgraph,Walk.mem_verts_toSubgraph]
    constructor
    · exact hinside x
    · intro hx
      obtain ⟨i,hi⟩ := (coordinates_support C hl x).mp hx
      obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hpinj) i
      apply (interval_support P _ (hb 6) x).mpr
      exact ⟨h j,hh.monotone (Fin.zero_le _),hh.monotone (Fin.le_last _),by rw [hc j,hj,hi]⟩
  have hlen : Q.length=6 := by
    have hv := (QuotaSurgery.walk_vertex_ncard_eq_iff Q).mpr hQ
    rw [hverts,Walk.verts_toSubgraph,cycle_support_ncard hC,hl] at hv
    omega
  refine ⟨P.getVert (h 0),P.getVert (h 6),P.take (h 0),Q,P.drop (h 6),
    split_interval P _ (hb 6),hQ,hverts,hlen,?_,?_⟩
  · intro x hx hxC
    obtain ⟨m,hm,hxm⟩ := (take_support P (hb 0) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp h p hpinj hb hc (hm.trans (hb 0)) (hxm ▸ hxC)
    have hlo := hh.monotone (Fin.zero_le j)
    have hm0 : m=h 0 := by omega
    exact hm0 ▸ hxm
  · intro x hx hxC
    obtain ⟨m,hm4,hm,hxm⟩ := (drop_support P (hb 6) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp h p hpinj hb hc hm (hxm ▸ hxC)
    have hhi := hh.monotone (Fin.le_last j)
    change h j ≤ h 6 at hhi
    have hm4' : m=h 6 := by omega
    exact hm4' ▸ hxm

lemma maximum_carrier_contiguous {k : ℕ} (T : QuotaTrails.TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : QuotaTrails.TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hhit : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    ∃ u v : V, ∃ A : G.Walk (T.start j) u, ∃ Q : G.Walk u v, ∃ B : G.Walk v (T.finish j),
      T.walk j=A.append (Q.append B) ∧ Q.IsPath ∧ Q.toSubgraph.verts=C.toSubgraph.verts ∧ Q.length=6 ∧
      (∀ x ∈ A.support, x ∈ C.support → x=u) ∧
      (∀ x ∈ B.support, x ∈ C.support → x=v) := by
  have hp := (T.one_defect_other_paths hs i (CycleEar.cycle_member_not_path T i C hC hi)).2 j hij.symm
  apply nonabsorbable_contiguous C hC hl (T.walk j) hp
    (by rw [←hi]; exact T.disjoint hij)
    (PentagonIntersection.maximal_cycle_not_absorbable T hm i j hij C hC hi hp)
  exact Erdos583CycleIntersectionSevenDevelopment.maximum_heptagon_carrier_contains T hs hm i j hij C hC hl hi hhit

end Erdos583HeptagonExcursionDevelopment
