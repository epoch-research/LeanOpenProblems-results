import Submission.LocalZeroNormalization

/-! Strict score improvement with a movable endpoint pair, allowing arbitrary
other defects.  The conclusions deliberately do not assert an all-path family. -/
namespace Erdos583MultiDefectForestImprovementDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.TrailNormalization Erdos583Work.DistinctTails
open Erdos583LocalZeroNormalizationDevelopment
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma improve_at_outside_start {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support) (havoid : T.start i ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, (∀ x, U.quota x = T.quota x) ∧ U.score=T.score+1 := by
  classical
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet := by
    rw [← he]; exact T.disjoint hij
  obtain ⟨hp',hq',hd',hu,_,_⟩ := trail_endpoint_slide h p (T.walk j) hp (T.isTrail j) hd hv
  obtain ⟨U,_,_,_,_,_,hscore,hquota⟩ := replace_two_starts_general T i j hij
    (T.start j) (T.start i) p (Walk.cons h (T.walk j)) hp' hq' hd' (by rw [he]; exact hu.symm)
  have hV : (T.walk i).toSubgraph.verts.ncard = p.toSubgraph.verts.ncard := by
    rw [he,cons_ncard_of_mem h p hv]
  have hW : (Walk.cons h (T.walk j)).toSubgraph.verts.ncard = (T.walk j).toSubgraph.verts.ncard + 1 :=
    cons_ncard_of_notMem h (T.walk j) havoid
  have hgain : U.score = T.score + 1 := by rw [hW,← hV] at hscore; omega
  refine ⟨U,fun x ↦ ?_,hgain⟩
  have hh := hquota x
  omega

lemma improve_at_outside_start_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k)
    (i j : Fin k) (hij : i ≠ j) {a x b : V}
    (hai : T.start i=a) (haj : T.start j=x) (hbi : T.finish i=b)
    (h : G.Adj a x) (p : G.Walk x b) (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hv : a ∈ p.support) (havoid : a ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) ∧ U.score=T.score+1 := by
  subst a x b
  exact improve_at_outside_start T i j hij h p hp he hv havoid

lemma exposedRoot_improve_positive {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r z : V} {A : Finset (Fin k)} {B : Finset V}
    (hE : ExposedRoot T r A B z)
    (hz : z ∉ B) (hpos : 0 < T.quota z) :
    ∃ P : TrailFamily G k, (∀ v, P.quota v=T.quota v) ∧ P.score=T.score+1 := by
  classical
  obtain ⟨U,hscore,hquota,Q,hB,ρ,hρ,hAdj⟩ := hE
  obtain ⟨i,b,h,p,hi,hends,hp,he,hv⟩ := rooted_exposed_rep Q ρ hρ hAdj
  have hposU : 0 < U.quota z := by rw [hquota]; exact hpos
  obtain ⟨s,hsend,hsA,havoid⟩ := Q.outside_endpoint B hB hz hposU
  let j := s.1
  have hij : i ≠ j := by
    intro hh
    apply hsA
    change j ∈ A
    rw [← hh]
    exact hi
  obtain ⟨S,hSs,hSq,hSa,hSb,hSrest,hSparts⟩ := orient_endpoint_pair U i r b hends
  have hjend : z=S.start j ∨ z=S.finish j := by
    obtain ⟨hja,hjb⟩ := hSrest j hij.symm
    rw [hja,hjb]
    rcases s with ⟨j,c⟩
    cases c
    · exact Or.inr hsend.symm
    · exact Or.inl hsend.symm
  obtain ⟨R,hRs,hRq,hRj,hRrest,hRparts⟩ := orient_endpoint_start S j z hjend
  obtain ⟨hRia,hRib⟩ := hRrest i hij
  have hRi : (R.walk i).toSubgraph=(Walk.cons h p).toSubgraph :=
    (hRparts i).trans ((hSparts i).trans he)
  have hRa : r ∉ (R.walk j).support := by
    rw [← Walk.mem_verts_toSubgraph,hRparts,hSparts,Walk.mem_verts_toSubgraph]
    exact havoid
  obtain ⟨P,hPq,hP⟩ := improve_at_outside_start_endpoints R i j hij
    (hRia.trans hSa) hRj (hRib.trans hSb) h p hp hRi hv hRa
  exact ⟨P,fun v ↦ (hPq v).trans ((hRq v).trans ((hSq v).trans (hquota v))),by omega⟩

lemma move_pair_score_or_root {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k)
    (i j : Fin k) (hij : i ≠ j) (hj : T.start j=T.start i)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hv : T.start i ∈ p.support) :
    ∃ U : TrailFamily G k,
      (∀ v, U.quota v + 2*(if T.start i=v then 1 else 0) =
        T.quota v + 2*(if x=v then 1 else 0)) ∧
      (U.score=T.score+1 ∨ (U.score=T.score ∧ HasRoot U x)) := by
  classical
  let q := (T.walk j).copy hj rfl
  have hq : q.IsTrail := by simpa only [q,Walk.isTrail_copy] using T.isTrail j
  have hqeq : q.toSubgraph=(T.walk j).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    rw [← he,hqeq]; exact T.disjoint hij
  obtain ⟨_,hnewTrail,hd',hunion⟩ := MobileDefect.same_root_transfer_data h p q hp hq hd
  obtain ⟨U,hUi,hUj,_,hstarts,hfinish,hscore,hquota⟩ := replace_two_starts_general T i j hij
    x x p (Walk.cons h.symm q) hp.of_cons hnewTrail hd' (by rw [hunion,← he,hqeq])
  have hquot (v : V) : U.quota v + 2*(if T.start i=v then 1 else 0) =
      T.quota v + 2*(if x=v then 1 else 0) := by
    have hh := hquota v
    rw [hj] at hh
    omega
  have hV : (T.walk i).toSubgraph.verts.ncard=p.toSubgraph.verts.ncard := by
    rw [he,cons_ncard_of_mem h p hv]
  refine ⟨U,hquot,?_⟩
  by_cases hx : x ∈ q.support
  · have hW : (Walk.cons h.symm q).toSubgraph.verts.ncard=(T.walk j).toSubgraph.verts.ncard := by
      rw [cons_ncard_of_mem h.symm q hx,hqeq]
    have hsU : U.score=T.score := by rw [hW,← hV] at hscore; omega
    have hja : U.start j=x := by rw [hstarts]; simp [hij.symm]
    have hjb : U.finish j=T.finish j := by rw [hfinish]
    exact Or.inr ⟨hsU,hasRoot_of_rep U j hja hjb h.symm q hUj hnewTrail hx⟩
  · have hW : (Walk.cons h.symm q).toSubgraph.verts.ncard=(T.walk j).toSubgraph.verts.ncard+1 := by
      rw [cons_ncard_of_notMem h.symm q hx,hqeq]
    have hsU : U.score=T.score+1 := by rw [hW,← hV] at hscore; omega
    exact Or.inl hsU

lemma move_pair_score_or_root_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k)
    (i j : Fin k) (hij : i ≠ j) {a x b : V}
    (hai : T.start i=a) (haj : T.start j=a) (hbi : T.finish i=b)
    (h : G.Adj a x) (p : G.Walk x b) (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hv : a ∈ p.support) :
    ∃ U : TrailFamily G k,
      (∀ v, U.quota v+2*(if a=v then 1 else 0)=T.quota v+2*(if x=v then 1 else 0)) ∧
      (U.score=T.score+1 ∨ (U.score=T.score ∧ HasRoot U x)) := by
  subst a b
  exact move_pair_score_or_root T i j hij haj h p hp he hv

lemma exposedRoot_move_pair_score_or_root {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r z : V} {A : Finset (Fin k)} {B : Finset V}
    (hE : ExposedRoot T r A B z)
    (hpos : 2 ≤ T.quota r) :
    ∃ P : TrailFamily G k,
      (∀ v, P.quota v+2*(if r=v then 1 else 0)=T.quota v+2*(if z=v then 1 else 0)) ∧
      (P.score=T.score+1 ∨ (P.score=T.score ∧ HasRoot P z)) := by
  classical
  obtain ⟨U,hscore,hquota,Q,_,ρ,hρ,hAdj⟩ := hE
  obtain ⟨i,b,h,p,_,hends,hp,he,hv⟩ := rooted_exposed_rep Q ρ hρ hAdj
  obtain ⟨S,hSs,hSq,hSa,hSb,_,hSparts⟩ := orient_endpoint_pair U i r b hends
  have hposS : 2 ≤ S.quota r := by rw [hSq,hquota]; exact hpos
  by_cases ho : ∃ j, j ≠ i ∧ (r=S.start j ∨ r=S.finish j)
  · obtain ⟨j,hji,hjend⟩ := ho
    obtain ⟨R,hRs,hRq,hRj,hRrest,hRparts⟩ := orient_endpoint_start S j r hjend
    obtain ⟨hRia,hRib⟩ := hRrest i hji.symm
    have hRi : (R.walk i).toSubgraph=(Walk.cons h p).toSubgraph :=
      (hRparts i).trans ((hSparts i).trans he)
    obtain ⟨P,hPq,hP⟩ := move_pair_score_or_root_endpoints R i j hji.symm
      (hRia.trans hSa) hRj (hRib.trans hSb) h p hp hRi hv
    refine ⟨P,fun v ↦ ?_,?_⟩
    · have hh := hPq v
      rw [hRq,hSq,hquota] at hh
      exact hh
    · rcases hP with hP | ⟨hPs,hroot⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega,hroot⟩
  · have honly : ∀ j, j ≠ i → r ≠ S.start j ∧ r ≠ S.finish j := by
      intro j hji
      exact ⟨fun hh ↦ ho ⟨j,hji,Or.inl hh⟩,fun hh ↦ ho ⟨j,hji,Or.inr hh⟩⟩
    have hbroot : S.finish i=r := finish_eq_root_of_only_root_member S i r hSa hposS honly
    have hbr : b=r := hSb.symm.trans hbroot
    clear hSb
    subst b
    have hzmem : z ∈ (Walk.cons h p).support := List.mem_cons_of_mem _ p.start_mem_support
    obtain ⟨P,hPs,hroot,hPq⟩ := reroot_closed_member S i hSa hbroot (Walk.cons h p) hp
      (by simp) ((hSparts i).trans he).symm hzmem
    refine ⟨P,fun v ↦ ?_,Or.inr ⟨by omega,hroot⟩⟩
    have hh := hPq v
    rw [hSq,hquota] at hh
    exact hh


/-- A zero-baseline pair can be moved within a zero-closed forest until the
score increases by one. Other defects may remain, and the improved family is
not asserted to have a rooted defect. -/
lemma improve_in_zero_region {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (c : V → ℕ) (r : V) (Z : Set V)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hrZ : r ∈ Z)
    (hclosed : ∀ a ∈ Z, ∀ z, G.Adj a z → c z=0 → z ∈ Z)
    (hforest : (G.induce Z).IsAcyclic) :
    ∃ r' : V, r' ∈ Z ∧ c r'=0 ∧ ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ P.score=T.score+1 := by
  classical
  by_contra hn
  let W (a : V) : Prop := a ∈ Z ∧ c a=0 ∧ ∃ U : TrailFamily G k, U.score=T.score ∧
    (∀ v, U.quota v=c v+2*(if a=v then 1 else 0)) ∧ HasRoot U a
  have hw : ∃ a, W a := ⟨r,hrZ,hr0,T,rfl,hquota,hroot⟩
  have hnext (a : V) (ha : W a) : ∃ x y, x ≠ y ∧ G.Adj a x ∧ G.Adj a y ∧
      x ∈ Z ∧ y ∈ Z ∧ W x ∧ W y := by
    obtain ⟨haZ,ha0,U,hUs,hUq,A,R,ρ,hρ,hRn⟩ := ha
    obtain ⟨B,_,x,y,hxy,hax,hay,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hRn
    have hreach (z : V) (haz : G.Adj a z) (hzB : z ∉ B) (hE : ExposedRoot U a A B z) : z ∈ Z ∧ W z := by
      have hz0 : c z=0 := by
        by_contra hzne
        have hpos : 0 < U.quota z := by rw [hUq]; omega
        obtain ⟨P,hPq,hPs⟩ := exposedRoot_improve_positive hE hzB hpos
        exact hn ⟨a,haZ,ha0,P,fun v ↦ (hPq v).trans (hUq v),by omega⟩
      have hzZ : z ∈ Z := hclosed a haZ z haz hz0
      have hpos : 2 ≤ U.quota a := by rw [hUq]; simp
      obtain ⟨P,hPq,hP⟩ := exposedRoot_move_pair_score_or_root hE hpos
      have hnewq (v : V) : P.quota v=c v+2*(if z=v then 1 else 0) := by
        have hh := hPq v
        rw [hUq] at hh
        omega
      rcases hP with hP | ⟨hPs,hPr⟩
      · exact (hn ⟨z,hzZ,hz0,P,hnewq,by omega⟩).elim
      · exact ⟨hzZ,hzZ,hz0,P,hPs.trans hUs,hnewq,hPr⟩
    obtain ⟨hx0,hWx⟩ := hreach x hax hxB hEx
    obtain ⟨hy0,hWy⟩ := hreach y hay hyB hEy
    exact ⟨x,y,hxy,hax,hay,hx0,hy0,hWx,hWy⟩
  exact cycle_of_two_zero_successors G Z W hw hnext hforest

lemma improve_pair_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (c : V → ℕ) (r : V)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hf : (G.induce {x | c x=0}).IsAcyclic) :
    ∃ r' : V, ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ P.score=T.score+1 := by
  classical
  obtain ⟨A,R,ρ,hρ,hRn⟩ := hroot
  obtain ⟨B,_,x,_,_,_,_,hxB,_,hEx,_⟩ := R.two_root_exposures ρ hρ hRn
  by_cases hx : c x=0
  · have hpos : 2 ≤ T.quota r := by rw [hquota]; simp
    obtain ⟨P,hPq,hP⟩ := exposedRoot_move_pair_score_or_root hEx hpos
    have hnewq (v : V) : P.quota v=c v+2*(if x=v then 1 else 0) := by
      have hh := hPq v
      rw [hquota] at hh
      omega
    rcases hP with hP | ⟨hPs,hPr⟩
    · exact ⟨x,P,hnewq,hP⟩
    · obtain ⟨r',_,_,U,hUq,hUs⟩ := improve_in_zero_region P c x {z | c z=0}
        hnewq hPr hx hx (fun _ _ _ _ hz ↦ hz) hf
      exact ⟨r',U,hUq,by omega⟩
  · have hpos : 0 < T.quota x := by rw [hquota]; omega
    obtain ⟨P,hPq,hPs⟩ := exposedRoot_improve_positive hEx hxB hpos
    exact ⟨r,P,fun v ↦ (hPq v).trans (hquota v),hPs⟩

/-- The even-forest condition forces strict improvement at every rooted
endpoint pair, for any total defect and any number of slots. -/
lemma improve_root_pair_of_even_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hr : HasRoot T r) (hpos : 2 ≤ T.quota r)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic) :
    ∃ P : TrailFamily G k, P.score=T.score+1 := by
  classical
  let c (x : V) := if r=x then T.quota x-2 else T.quota x
  have hquota (x : V) : T.quota x=c x+2*(if r=x then 1 else 0) := by
    by_cases hx : r=x
    · subst x; simp only [c,↓reduceIte,mul_one]; omega
    · simp only [c,hx,↓reduceIte,mul_zero,add_zero]
  have hsub : {x | c x=0} ⊆ {x | Even (Nat.card (G.neighborSet x))} := by
    intro x hx
    apply (QuotaParity.quota_even_iff T x).mp
    have hh := hquota x
    change c x=0 at hx
    rw [hx,zero_add] at hh
    rw [hh]
    exact even_two.mul_right _
  have hfc := hf.comap (G.induceHomOfLE hsub).toHom (G.induceHomOfLE hsub).injective
  obtain ⟨_,P,_,hPs⟩ := improve_pair_forest T c r hquota hr hfc
  exact ⟨P,hPs⟩

/-- At an unrestricted score maximum on an even-forest graph, every rooted
repetition has quota exactly one and occurs at an odd-degree vertex. No
single-defect or Gallai-budget hypothesis is needed. -/
lemma maximum_root_quota_one_of_even_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x))}).IsAcyclic) :
    T.quota r=1 ∧ Odd (Nat.card (G.neighborSet r)) := by
  have hp := RootEnergy.root_quota_pos hr
  have hb : T.quota r < 2 := by
    by_contra hn
    obtain ⟨P,hP⟩ := improve_root_pair_of_even_forest T r hr (by omega) hf
    have hh := hm P
    omega
  have hq : T.quota r=1 := by omega
  refine ⟨hq,(QuotaParity.quota_odd_iff T r).mp ?_⟩
  rw [hq]
  exact odd_one

end Erdos583MultiDefectForestImprovementDevelopment
