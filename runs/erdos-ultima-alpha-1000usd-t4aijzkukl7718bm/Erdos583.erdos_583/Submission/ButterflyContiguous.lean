import Submission.ButterflyExcursion

/-! A nonabsorbable path must traverse the four outer vertices consecutively. -/
namespace Erdos583ButterflyContiguousDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyMissingDevelopment Erdos583ButterflyExcursionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma snoc_injective {N : ℕ} {V : Type*} (f : Fin N → V) (hf : Function.Injective f)
    (x : V) (hx : ∀ i, x ≠ f i) : Function.Injective (Fin.snoc f x) := by
  intro i
  refine Fin.lastCases ?_ ?_ i
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · intro _; rfl
    · intro j hj
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hj
      exact (hx j hj).elim
  · intro i j
    refine Fin.lastCases ?_ ?_ j
    · intro hi
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hi
      exact (hx i hi.symm).elim
    · intro j hij
      simp only [Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc (hf hij)

lemma outer_injective : Function.Injective outer := by
  intro i j hij
  have hval := congrArg Fin.val hij
  exact Fin.ext (by dsimp [outer] at hval; omega)

lemma outer_surjective_away_zero (p : Fin 4 → Fin 4) (hp : Function.Injective p)
    {x : Fin 5} (hx : x ≠ 0) : ∃ i, outer (p i)=x := by
  have hpos : 0 < x.val := by by_contra hn; exact hx (Fin.ext (by omega))
  let j : Fin 4 := ⟨x.val-1,by have h := x.isLt; omega⟩
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp hp) j
  refine ⟨i,?_⟩
  rw [hi]
  apply Fin.ext
  dsimp [outer,j]
  omega

lemma butterfly_nonabsorbable_contiguous {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (f : Fin 5 → V) (hf : Function.Injective f) (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (P : G.Walk a b) (hP : P.IsPath) (hmiss0 : f 0 ∉ P.support)
    (htouch : ∃ i, f i ∈ P.support)
    (havoid : ∀ i, s(f (baseSource i),f (baseTarget i)) ∉ P.edges)
    (hno : ¬TwoPathCover (G := G) (coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet)) :
    ∃ p : Fin 4 → Fin 4, ∃ h : Fin 4 → ℕ,
      Function.Injective p ∧ StrictMono h ∧ (∀ i, h i ≤ P.length) ∧
      (∀ i, P.getVert (h i)=f (outer (p i))) ∧
      (∀ i : Fin 3, h i.succ=h i.castSucc+1) := by
  classical
  have hvisit (i : Fin 4) : f (outer i) ∈ P.support := by
    by_contra hi
    have hi0 : outer i ≠ 0 := by intro he; have hv := congrArg Fin.val he; dsimp [outer] at hv; omega
    exact hno (butterfly_missing_vertex_absorption f hf ha P hP hmiss0 ⟨outer i,hi0,hi⟩ htouch havoid)
  obtain ⟨h,p,hh,hpi,hb,hc⟩ := PentagonCoordinates.ordered_vertices P (f ∘ outer)
    (hf.comp outer_injective) hvisit
  refine ⟨p,h,hpi,hh,hb,hc,?_⟩
  intro d
  have hlt := hh (show d.castSucc < d.succ from Fin.castSucc_lt_succ)
  by_contra hgap
  let j := h d.castSucc+1
  have hjl : h d.castSucc < j := by dsimp [j]; omega
  have hjr : j < h d.succ := by dsimp [j]; omega
  have hjb : j ≤ P.length := by have hh := hb d.succ; omega
  have hout (u : Fin 5) : P.getVert j ≠ f u := by
    intro he
    by_cases hu : u=0
    · subst u
      exact hmiss0 (he ▸ P.getVert_mem_support j)
    obtain ⟨l,hl⟩ := outer_surjective_away_zero p hpi hu
    have hpos : h l=j := hP.getVert_injOn (hb l) hjb (by
      rw [hc l,he]
      exact congrArg f hl)
    have hdl : d.castSucc < l := hh.lt_iff_lt.mp (by omega)
    have hld : l < d.succ := hh.lt_iff_lt.mp (by omega)
    have h1 : d.val < l.val := hdl
    have h2 : l.val < d.val+1 := hld
    omega
  let g : Fin 6 → V := Fin.snoc f (P.getVert j)
  have hgi : Function.Injective g := snoc_injective f hf (P.getVert j) hout
  have hga (i : Fin 6) : G.Adj (g (Excursion.source i)) (g (Excursion.target i)) := by
    simpa only [g,Excursion.source,Excursion.target,Function.comp_apply,Fin.snoc_castSucc] using ha i
  have hgmiss : g 0 ∉ P.support := by
    change g ((0 : Fin 5).castSucc) ∉ P.support
    simpa only [g,Fin.snoc_castSucc] using hmiss0
  have hgvisit (i : Fin 5) : g i.succ ∈ P.support := by
    refine Fin.lastCases ?_ ?_ i
    · change g (Fin.last 5) ∈ P.support
      simpa only [g,Fin.snoc_last] using P.getVert_mem_support j
    · intro i
      rw [Fin.succ_castSucc]
      simpa only [g,Fin.snoc_castSucc] using hvisit i
  have hgj : P.getVert j=g 5 := by simp only [g,show (5 : Fin 6)=Fin.last 5 from rfl,Fin.snoc_last]
  have hgl : ∃ i : ℕ, ∃ u : Fin 5, i < j ∧ P.getVert i=g u.castSucc := by
    exact ⟨h d.castSucc,outer (p d.castSucc),hjl,by simpa only [g,Fin.snoc_castSucc] using hc d.castSucc⟩
  have hgr : ∃ k : ℕ, ∃ v : Fin 5, j < k ∧ k ≤ P.length ∧ P.getVert k=g v.castSucc := by
    exact ⟨h d.succ,outer (p d.succ),hjr,hb d.succ,by simpa only [g,Fin.snoc_castSucc] using hc d.succ⟩
  have hgavoid (i : Fin 6) : s(g (Excursion.source i),g (Excursion.target i)) ∉ P.edges := by
    simpa only [g,Excursion.source,Excursion.target,Function.comp_apply,Fin.snoc_castSucc] using havoid i
  have hcov := butterfly_excursion_absorption g hgi hga P hP hgmiss hgvisit hgj hgl hgr hgavoid
  have hcore : coreEdges Excursion.source Excursion.target g=coreEdges baseSource baseTarget f := by
    simp only [coreEdges,g,Excursion.source,Excursion.target,Function.comp_apply,Fin.snoc_castSucc]
  exact hno (hcore ▸ hcov)

end Erdos583ButterflyContiguousDevelopment
