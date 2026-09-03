import Submission.NormalQuotaPurification

/-! Localized normalization: only the chosen zero-quota region needs to be
acyclic. This does not assert that such a region always exists. -/
namespace Erdos583LocalZeroNormalizationDevelopment
open SimpleGraph Erdos583Work Erdos583NormalForestRestorationDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.DistinctTails
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma normalize_in_zero_region {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (c : V → ℕ) (r : V) (Z : Set V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hrZ : r ∈ Z)
    (hclosed : ∀ a ∈ Z, ∀ z, G.Adj a z → c z=0 → z ∈ Z)
    (hforest : (G.induce Z).IsAcyclic) :
    ∃ r' : V, r' ∈ Z ∧ c r'=0 ∧ ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
  classical
  by_contra hn
  let W (a : V) : Prop := a ∈ Z ∧ c a=0 ∧ ∃ U : TrailFamily G k, U.score=T.score ∧
    (∀ v, U.quota v=c v+2*(if a=v then 1 else 0)) ∧ HasRoot U a
  have hw : ∃ a, W a := ⟨r,hrZ,hr0,T,rfl,hquota,hroot⟩
  have hnext (a : V) (ha : W a) : ∃ x y, x ≠ y ∧ G.Adj a x ∧ G.Adj a y ∧
      x ∈ Z ∧ y ∈ Z ∧ W x ∧ W y := by
    obtain ⟨haZ,ha0,U,hUs,hUq,A,R,ρ,hρ,hRn⟩ := ha
    have hscoreU : U.score+1=G.edgeSet.ncard+k := by omega
    obtain ⟨B,_,x,y,hxy,hax,hay,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hRn
    have hreach (z : V) (haz : G.Adj a z) (hzB : z ∉ B) (hE : ExposedRoot U a A B z) : z ∈ Z ∧ W z := by
      have hz0 : c z=0 := by
        by_contra hzne
        have hpos : 0 < U.quota z := by rw [hUq]; omega
        obtain ⟨P,hPq,hP⟩ := exposedRoot_repair_of_positive hE hscoreU hzB hpos
        exact hn ⟨a,haZ,ha0,P,fun v ↦ (hPq v).trans (hUq v),hP⟩
      have hzZ : z ∈ Z := hclosed a haZ z haz hz0
      have hpos : 2 ≤ U.quota a := by rw [hUq]; simp
      obtain ⟨P,hPq,hP⟩ := exposedRoot_move_pair_or_repair hE hscoreU hpos
      have hnewq (v : V) : P.quota v=c v+2*(if z=v then 1 else 0) := by
        have hh := hPq v
        rw [hUq] at hh
        omega
      rcases hP with hP | ⟨hPs,hPr⟩
      · exact (hn ⟨z,hzZ,hz0,P,hnewq,hP⟩).elim
      · exact ⟨hzZ,hzZ,hz0,P,hPs.trans hUs,hnewq,hPr⟩
    obtain ⟨hx0,hWx⟩ := hreach x hax hxB hEx
    obtain ⟨hy0,hWy⟩ := hreach y hay hyB hEy
    exact ⟨x,y,hxy,hax,hay,hx0,hy0,hWx,hWy⟩
  exact cycle_of_two_zero_successors G Z W hw hnext hforest



/-- At most one zero-quota neighbor of the root permits repair without moving
any endpoint quotas. There is no hypothesis on zero vertices elsewhere. -/
lemma repair_of_subsingleton_zero_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hr : HasRoot T r)
    (hfew : {x | G.Adj r x ∧ T.quota x=0}.Subsingleton) :
    ∃ P : TrailFamily G k, (∀ x, P.quota x=T.quota x) ∧ ∀ i, (P.walk i).IsPath := by
  obtain ⟨A,R,ρ,hρ,hRn⟩ := hr
  obtain ⟨B,_,x,y,hxy,hax,hay,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hRn
  by_cases hx : T.quota x=0
  · have hy : 0 < T.quota y := by
      by_contra hn
      exact hxy (hfew ⟨hax,hx⟩ ⟨hay,by omega⟩)
    exact exposedRoot_repair_of_positive hEy hs hyB hy
  · exact exposedRoot_repair_of_positive hEx hs hxB (Nat.pos_of_ne_zero hx)

/-- The localized normalization can retain exact quotas in a nonempty-member
normal decomposition. In particular, all positive baseline labels stay active. -/
lemma normalize_region_partition {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hsupp : ∀ x, x ∈ G.support)
    (T : TrailFamily G k) (c : V → ℕ) (r : V) (Z : Set V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hrZ : r ∈ Z)
    (hc : ∀ x, c x ≤ 2)
    (hclosed : ∀ a ∈ Z, ∀ z, G.Adj a z → c z=0 → z ∈ Z)
    (hforest : (G.induce Z).IsAcyclic) :
    ∃ r' ∈ Z, c r'=0 ∧ ∃ D : Finset G.Subgraph,
      GoodDecomposition G D ∧ D.card=k ∧ (∀ H ∈ D, H.edgeSet.Nonempty) ∧
      ∀ x, endpointMultiplicity D x=c x+2*(if r'=x then 1 else 0) := by
  obtain ⟨s,hsZ,hs0,P,hPq,hP⟩ := normalize_in_zero_region T c r Z hs hquota hroot hr0 hrZ hclosed hforest
  have hPb (x : V) : P.quota x ≤ 2 := by
    rw [hPq]
    by_cases hsx : s=x
    · subst x; simp [hs0]
    · simpa [hsx] using hc x
  obtain ⟨D,hD,hDc,hDn,hDq⟩ :=
    Erdos583NormalQuotaPurificationDevelopment.path_family_partition_quota_exact hsupp P hP hPb
  exact ⟨s,hsZ,hs0,D,hD,hDc,hDn,fun x ↦ (hDq x).trans (hPq x)⟩

/-- A new edge can be appended without a path-count increase whenever the new
end has no inactive neighbor in the original path family. Exact endpoint
transport is retained, not merely an upper bound on the number of paths. -/
lemma append_edge_away_from_inactive {V : Type*} [Fintype V] {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (T : TrailFamily H k) (hp : ∀ i, (T.walk i).IsPath)
    (i : Fin k) {u v : V} (hi : u=T.start i ∨ u=T.finish i)
    (h : G.Adj v u) (hnew : s(v,u) ∉ H.edgeSet)
    (hcover : G.edgeSet=insert s(v,u) H.edgeSet)
    (havoid : ∀ x, G.Adj v x → T.quota x ≠ 0) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧
      ∀ x, P.quota x+(if u=x then 1 else 0)=T.quota x+(if v=x then 1 else 0) := by
  classical
  obtain ⟨U,hs,hq,_,hr⟩ := DeletionEndpoint.append_new_edge_tracked hHG T hp i hi h hnew hcover
  by_cases hP : ∀ i, (U.walk i).IsPath
  · exact ⟨U,hP,hq⟩
  have hscore : U.score+1=G.edgeSet.ncard+k := by
    have hupper := U.score_le_edges_add
    have hne := U.score_eq_edges_add_iff.not.mpr hP
    omega
  have hzero (x : V) (hvx : G.Adj v x) (hx : U.quota x=0) : x=u := by
    by_contra hxu
    have hh := hq x
    have hn := havoid x hvx
    simp only [hx,Ne.symm hxu,↓reduceIte,zero_add] at hh
    omega
  have hfew : {x | G.Adj v x ∧ U.quota x=0}.Subsingleton := by
    intro x hx y hy
    exact (hzero x hx.1 hx.2).trans (hzero y hy.1 hy.2).symm
  obtain ⟨P,hPq,hP⟩ := repair_of_subsingleton_zero_neighbors U v hscore (hr hP) hfew
  exact ⟨P,hP,fun x ↦ by rw [hPq]; exact hq x⟩

end Erdos583LocalZeroNormalizationDevelopment
