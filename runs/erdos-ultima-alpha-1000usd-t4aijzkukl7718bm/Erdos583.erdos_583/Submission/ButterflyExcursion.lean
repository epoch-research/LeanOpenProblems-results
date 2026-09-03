import Submission.ButterflyMissing

/-! An internal excursion through a fresh sixth vertex absorbs the two triangles. -/
namespace Erdos583ButterflyExcursionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyOrderedAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma butterfly_excursion_absorption {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (f : Fin 6 → V) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (Excursion.source i)) (f (Excursion.target i)))
    (P : G.Walk a b) (hP : P.IsPath)
    (hmiss : f 0 ∉ P.support) (hvisit : ∀ i : Fin 5, f i.succ ∈ P.support)
    {j : ℕ} (hj : P.getVert j=f 5)
    (hleft : ∃ i : ℕ, ∃ u : Fin 5, i < j ∧ P.getVert i=f u.castSucc)
    (hright : ∃ k : ℕ, ∃ v : Fin 5, j < k ∧ k ≤ P.length ∧ P.getVert k=f v.castSucc)
    (havoid : ∀ i, s(f (Excursion.source i),f (Excursion.target i)) ∉ P.edges) :
    TwoPathCover (G := G) (coreEdges Excursion.source Excursion.target f ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨il,u,hil,hilu⟩ := hleft
  obtain ⟨ir,v,hjr,hir,hirv⟩ := hright
  have hjb : j ≤ P.length := by omega
  obtain ⟨h,p,hh,hpi,hb,hc⟩ := PentagonCoordinates.ordered_vertices P (fun i : Fin 5 ↦ f i.succ)
    (hf.comp (Fin.succ_injective 5)) hvisit
  let q : Fin 5 → Fin 6 := Fin.succ ∘ p
  have hqi : Function.Injective q := (Fin.succ_injective 5).comp hpi
  have hq0 (i : Fin 5) : q i ≠ 0 := by simp [q,Function.comp_def]
  have hmarked : ∀ x : Fin 6, f x ∈ P.support → ∃ i, q i=x := by
    refine Fin.cases ?_ ?_
    · intro h; exact (hmiss h).elim
    · intro x _
      obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp hpi) x
      exact ⟨i,congrArg Fin.succ hi⟩
  have hfirst : q 0 ≠ 5 := by
    intro h0
    have hpos : h 0=j := hP.getVert_injOn (hb 0) hjb (by
      rw [hc 0,hj]; exact congrArg f h0)
    have huP : f u.castSucc ∈ P.support := hilu ▸ P.getVert_mem_support il
    obtain ⟨l,hl⟩ := hmarked u.castSucc huP
    have hpl : h l=il := hP.getVert_injOn (hb l) (show il ≤ P.length by omega) (by
      rw [hc l,hilu]; exact congrArg f hl)
    have hle := hh.monotone (Fin.zero_le l)
    omega
  have hlast : q 4 ≠ 5 := by
    intro h4
    have hpos : h 4=j := hP.getVert_injOn (hb 4) hjb (by
      rw [hc 4,hj]; exact congrArg f h4)
    have hvP : f v.castSucc ∈ P.support := hirv ▸ P.getVert_mem_support ir
    obtain ⟨l,hl⟩ := hmarked v.castSucc hvP
    have hpl : h l=ir := hP.getVert_injOn (hb l) hir (by
      rw [hc l,hirv]; exact congrArg f hl)
    have hle := hh.monotone (Fin.le_last l)
    change h l ≤ h 4 at hle
    omega
  exact ordered_excursion_absorption q hqi hq0 hfirst hlast f hf ha P hP h hh hb hc hmarked havoid

end Erdos583ButterflyExcursionDevelopment
