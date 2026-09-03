import Submission.HeptagonCoordinates
import Submission.HeptagonSplitPieceSystem

/-! Absorbing the exceptional seven-cycle orders using a forced outside path vertex. -/
namespace Erdos583HeptagonExceptionalDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583Work.PathIntervals Erdos583Work.PathRestoreIntersection
open Erdos583HeptagonRoutesDevelopment (Exceptional)
open Erdos583HeptagonCoordinatesDevelopment
open Erdos583HeptagonSplitRoutesDevelopment Erdos583HeptagonSplitPieceSystemDevelopment
open Erdos583Work.HexagonExcursionCoordinates (insertCut insertCut_strictMono insertCut_bound insertCut_zero insertCut_last)
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {r a b : V}

lemma exceptional_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support)
    (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc)
    (hex : Exceptional p) : TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  have hgap := (finite_certificate p hpinj hex).1
  have hlt : h 1 < h 2 := hh (by decide)
  have hne : h 1+1 ≠ h 2 := by
    intro he
    have heC : C.toSubgraph.Adj (P.getVert (h 1)) (P.getVert (h 2)) := by
      rw [hc 1,hc 2]
      exact coordinates_cycle_adj C hl _ _ hgap
    have heP : s(P.getVert (h 1),P.getVert (h 2)) ∈ P.toSubgraph.edgeSet := by
      rw [Walk.mem_edges_toSubgraph,edges_positions]
      exact ⟨h 1,hlt.trans_le (hb 2),by rw [he]⟩
    exact Set.disjoint_left.mp hd heC heP
  let m := h 1+1
  have hmlo : h 1 < m := by omega
  have hmhi : m < h 2 := by omega
  have hmout : P.getVert m ∉ C.support := by
    intro hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp hmiss h p hpinj hb hc
      (hmhi.le.trans (hb 2)) hx
    have hlo : (1 : Fin 6) < j := hh.lt_iff_lt.mp (by omega)
    have hhi : j < (2 : Fin 6) := hh.lt_iff_lt.mp (by omega)
    have h1 : 1 < j.val := hlo
    have h2 : j.val < 2 := hhi
    omega
  let z := P.getVert m
  let h' := insertCut h 1 m
  let f : Fin 8 → V := Fin.lastCases z (coordinates C)
  have hh' : StrictMono h' := insertCut_strictMono h hh 1 m hmlo hmhi
  have hb' : ∀ i, h' i ≤ P.length := insertCut_bound h 1 m P.length hb (hmhi.le.trans (hb 2))
  have hc' : ∀ i, P.getVert (h' i)=f (extended p i) :=
    inserted_coordinates P (coordinates C) h p hc m z rfl
  have hf : Function.Injective f := extend_injective (coordinates C) (coordinates_injective C hC hl) z
    (fun i he ↦ hmout (by change z ∈ C.support; rw [he]; exact C.getVert_mem_support _))
  have hmiss' : f 6 ∉ P.support := by
    change coordinates C 6 ∉ P.support
    rwa [coordinates_last C hl]
  have ha : ∀ i : Fin 7, G.Adj (f i.castSucc) (f (next i).castSucc) := by
    intro i
    simpa only [f,Fin.lastCases_castSucc,next,Erdos583HeptagonRoutesDevelopment.next] using coordinates_adj C hl i
  have hCe : cycleEdges f=C.toSubgraph.edgeSet := by
    rw [coordinates_edges C hl]
    simp only [cycleEdges,f,Fin.lastCases_castSucc,next,Erdos583HeptagonRoutesDevelopment.next]
  have havoid (i : Fin 7) : s(f i.castSucc,f (next i).castSucc) ∉ P.edges := by
    intro he
    have hCedge : s(f i.castSucc,f (next i).castSucc) ∈ C.toSubgraph.edgeSet := by
      rw [←hCe]
      exact Set.mem_iUnion.mpr ⟨i,rfl⟩
    exact Set.disjoint_left.mp hd hCedge (P.mem_edges_toSubgraph.mpr he)
  obtain ⟨X,Y,hX,hY,hdXY,heXY,hsX,hsY⟩ := ordered_absorption p f P h' hh' hc' ha
    hex hmiss' hpinj hf hp hb' havoid
  have hstart : f (p 0).castSucc.castSucc=P.getVert (h 0) := by
    simpa only [f,Fin.lastCases_castSucc] using (hc 0).symm
  have hfinish : f (p 5).castSucc.castSucc=P.getVert (h 5) := by
    simpa only [f,Fin.lastCases_castSucc] using (hc 5).symm
  let X' := X.copy hstart rfl
  let Y' := Y.copy hfinish rfl
  have hXe : X'.toSubgraph=X.toSubgraph := NormalTrailSystem.walk_copy_subgraph X _ _
  have hYe : Y'.toSubgraph=Y.toSubgraph := NormalTrailSystem.walk_copy_subgraph Y _ _
  have hmidE := interval_edges_congr P (hh'.monotone (Fin.zero_le (6 : Fin 7)))
    (hh.monotone (Fin.zero_le (5 : Fin 6))) (insertCut_zero h 1 m) (insertCut_last h 1 m)
  have hmidS := interval_support_congr P (hh'.monotone (Fin.zero_le (6 : Fin 7)))
    (hh.monotone (Fin.zero_le (5 : Fin 6))) (insertCut_zero h 1 m) (insertCut_last h 1 m)
  rw [hmidE,hCe] at heXY
  rw [hmidS] at hsX hsY
  apply restore_two_on_path P hp (hh.monotone (Fin.zero_le _)) (hb 5) X' Y'
    (by simpa only [X',Walk.isPath_copy] using hX) (by simpa only [Y',Walk.isPath_copy] using hY)
    (by simpa only [hXe,hYe] using hdXY) C.toSubgraph.edgeSet hd
    (by simpa only [hXe,hYe] using heXY)
  · simpa only [X',Walk.support_copy] using hsX
  · simpa only [Y',Walk.support_copy] using hsY

end Erdos583HeptagonExceptionalDevelopment
