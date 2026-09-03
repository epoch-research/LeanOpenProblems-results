import Submission.QuotaSurgery

/-! One-defect normalization with a forest of zero-baseline vertices.
This is an auxiliary normalization theorem, not the unrestricted Gallai bound. -/
open SimpleGraph Erdos583Work
open Erdos583DistinctTailsDevelopment Erdos583QuotaTrailsDevelopment
open Erdos583QuotaRootedDevelopment Erdos583QuotaSurgeryDevelopment
namespace Erdos583ForestZeroNormalizationDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- If the zero-baseline vertices induce a forest, a deficit-one rooted trail
family can be normalized without changing its number of indexed members.
The baseline endpoint quotas stay fixed; one extra endpoint pair may relocate. -/
lemma normalize_one_defect_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (c : V → ℕ) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hforest : (G.induce {v | c v=0}).IsAcyclic) :
    ∃ r' : V, ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
  classical
  by_contra hn
  let W (a : V) : Prop := ∃ U : TrailFamily G k, U.score=T.score ∧
    (∀ v, U.quota v=c v+2*(if a=v then 1 else 0)) ∧ HasRoot U a
  have hw : ∃ a, W a := ⟨r,T,rfl,hquota,hroot⟩
  have hnext (a : V) (ha : W a) : ∃ x y, x ≠ y ∧ G.Adj a x ∧ G.Adj a y ∧
      x ∈ ({v | c v=0} : Set V) ∧ y ∈ ({v | c v=0} : Set V) ∧ W x ∧ W y := by
    obtain ⟨U,hUs,hUq,A,R,ρ,hρ,hRn⟩ := ha
    have hscoreU : U.score+1=G.edgeSet.ncard+k := by omega
    obtain ⟨B,_,x,y,hxy,hax,hay,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hRn
    have hreach (z : V) (hzB : z ∉ B) (hE : ExposedRoot U a A B z) : c z=0 ∧ W z := by
      have hz0 : c z=0 := by
        by_contra hzne
        have hpos : 0 < U.quota z := by rw [hUq]; omega
        obtain ⟨P,hPq,hP⟩ := exposedRoot_repair_of_positive hE hscoreU hzB hpos
        exact hn ⟨a,P,fun v ↦ (hPq v).trans (hUq v),hP⟩
      have hpos : 2 ≤ U.quota a := by rw [hUq]; simp
      obtain ⟨P,hPq,hP⟩ := exposedRoot_move_pair_or_repair hE hscoreU hpos
      have hnewq (v : V) : P.quota v=c v+2*(if z=v then 1 else 0) := by
        have hh := hPq v
        rw [hUq] at hh
        omega
      rcases hP with hP | ⟨hPs,hPr⟩
      · exact (hn ⟨z,P,hnewq,hP⟩).elim
      · exact ⟨hz0,P,hPs.trans hUs,hnewq,hPr⟩
    obtain ⟨hx0,hWx⟩ := hreach x hxB hEx
    obtain ⟨hy0,hWy⟩ := hreach y hyB hEy
    exact ⟨x,y,hxy,hax,hay,hx0,hy0,hWx,hWy⟩
  exact cycle_of_two_zero_successors G {v | c v=0} W hw hnext hforest

/-- In particular, one simple cycle together with simple paths can be
normalized at the same member count when the zero-baseline graph is a forest. -/
lemma normalize_one_cycle_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) (c : V → ℕ) (r : V)
    (ha : T.start i=r) (hb : T.finish i=r)
    (C : G.Walk r r) (hc : C.IsCycle) (he : (T.walk i).toSubgraph=C.toSubgraph)
    (hothers : ∀ j, j ≠ i → (T.walk j).IsPath)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hforest : (G.induce {v | c v=0}).IsAcyclic) :
    ∃ r' : V, ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ ∀ j, (P.walk j).IsPath := by
  classical
  have hlen : (T.walk i).length=C.length := by
    rw [← trail_edgeSet_ncard _ (T.isTrail i),he,trail_edgeSet_ncard _ hc.isTrail]
  have hverts : (T.walk i).toSubgraph.verts.ncard=C.length := by
    rw [he,Walk.verts_toSubgraph]
    exact cycle_support_ncard hc
  have hdi : T.defect i=1 := by
    change (T.walk i).length+1-(T.walk i).toSubgraph.verts.ncard=1
    rw [hlen,hverts]
    omega
  have hsum : ∑ j, T.defect j=1 := by
    rw [Finset.sum_eq_single i,hdi]
    · intro j _ hji
      exact (T.defect_eq_zero_iff j).mpr (hothers j hji)
    · simp
  have hs : T.score+1=G.edgeSet.ncard+k := by
    have hh := T.sum_defect_add_score
    rw [hsum] at hh
    omega
  have hroot : HasRoot T r := by
    cases hform : C with
    | nil => exact (hc.not_nil (hform ▸ Walk.Nil.nil)).elim
    | @cons _ x _ h q =>
      exact hasRoot_of_rep T i ha hb h q (he.trans (congrArg Walk.toSubgraph hform))
        (hform ▸ hc.isTrail) q.end_mem_support
  exact normalize_one_defect_forest T c r hs hquota hroot hforest

end Erdos583ForestZeroNormalizationDevelopment
