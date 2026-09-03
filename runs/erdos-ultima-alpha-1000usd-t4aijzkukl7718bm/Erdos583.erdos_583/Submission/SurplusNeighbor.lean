import Submission.Work

/-! A three-member endpoint-pair transfer through an exposed defect edge.
The two normal members may have arbitrary intersections. This is a local
exchange, not a proof that an exchange reaching a surplus always exists. -/

open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
namespace Erdos583SurplusNeighborDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

lemma exchange_first_edges_data {V : Type*} {G : SimpleGraph V} {r w x b c : V}
    (h : G.Adj r x) (f : G.Adj w x) (p : G.Walk x b) (q : G.Walk x c)
    (hp : (Walk.cons h p).IsTrail) (hq : (Walk.cons f q).IsTrail)
    (hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (Walk.cons f q).toSubgraph.edgeSet) :
    (Walk.cons f p).IsTrail ∧ (Walk.cons h q).IsTrail ∧
      Disjoint (Walk.cons f p).toSubgraph.edgeSet (Walk.cons h q).toSubgraph.edgeSet ∧
      (Walk.cons f p).toSubgraph.edgeSet ∪ (Walk.cons h q).toSubgraph.edgeSet =
        (Walk.cons h p).toSubgraph.edgeSet ∪ (Walk.cons f q).toSubgraph.edgeSet := by
  have hs : Disjoint (insert s(r,x) p.toSubgraph.edgeSet) (insert s(w,x) q.toSubgraph.edgeSet) := by
    simpa only [Walk.toSubgraph,Subgraph.edgeSet_sup,edgeSet_subgraphOfAdj,
      Set.singleton_union] using hd
  have hfnot : s(w,x) ∉ p.edges := by
    intro he
    exact Set.disjoint_left.mp hs (Set.mem_insert_of_mem _ (p.mem_edges_toSubgraph.mpr he))
      (Set.mem_insert _ _)
  have hhnot : s(r,x) ∉ q.edges := by
    intro he
    exact Set.disjoint_left.mp hs (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (q.mem_edges_toSubgraph.mpr he))
  refine ⟨hp.of_cons.cons f hfnot,hq.of_cons.cons h hhnot,?_,?_⟩
  · simp only [Walk.toSubgraph,Subgraph.edgeSet_sup,edgeSet_subgraphOfAdj,
      Set.singleton_union]
    apply Set.disjoint_left.mpr
    intro e he he'
    rcases he with he | he <;> rcases he' with he' | he'
    · exact Set.disjoint_left.mp hs (Or.inl he') (Or.inl he)
    · exact (Walk.isTrail_cons f q).mp hq |>.2
        (q.mem_edges_toSubgraph.mp (he ▸ he'))
    · exact (Walk.isTrail_cons h p).mp hp |>.2
        (p.mem_edges_toSubgraph.mp (he' ▸ he))
    · exact Set.disjoint_left.mp hs (Or.inr he) (Or.inr he')
  · ext e
    simp only [Walk.toSubgraph,Subgraph.edgeSet_sup,edgeSet_subgraphOfAdj,
      Set.singleton_union,Set.mem_union,Set.mem_insert_iff]
    tauto

/-- Exchange `r-x` and `w-x` at the fronts of two members, then pass `w-x`
to a third member starting at `w`. Only the first outside member must avoid
`r`; no restriction is imposed on the intersection of the last two members. -/
lemma transfer_data {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hr : T.start i ∈ p.support)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsPath)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : T.start i ∉ (T.walk j).support)
    (hl : T.start l=T.start j) :
    ∃ U : TrailFamily G k,
      (∀ v, U.quota v+2*(if T.start j=v then 1 else 0)=
        T.quota v+2*(if x=v then 1 else 0)) ∧
      U.score=T.score+(if x ∈ (T.walk l).support then 0 else 1) ∧
      (x ∈ (T.walk l).support → HasRoot U x) ∧
      (U.walk i).toSubgraph=p.toSubgraph ∧
      (U.walk j).toSubgraph=(Walk.cons h q).toSubgraph ∧
      ∀ a, a ≠ i → a ≠ j → a ≠ l →
        (U.walk a).toSubgraph=(T.walk a).toSubgraph := by
  classical
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (Walk.cons f q).toSubgraph.edgeSet := by
    rw [←hi,←hj]; exact T.disjoint hij
  obtain ⟨hfp,hhq,hd',hu⟩ := exchange_first_edges_data h f p q hp hq.isTrail hd
  obtain ⟨R,hRi,hRj,hRrest,hRa,hRb,hRs,hRq⟩ :=
    replace_two_starts_general T i j hij (T.start j) (T.start i)
      (Walk.cons f p) (Walk.cons h q) hfp hhq hd' (by rw [hu,←hi,←hj])
  have hRia : R.start i=T.start j := by rw [hRa]; simp
  have hRla : R.start l=T.start j := by rw [hRa]; simp [hil.symm,hjl.symm,hl]
  let p' := p.copy rfl (congrFun hRb i).symm
  let z := (T.walk l).copy (hl.trans hRia.symm) (congrFun hRb l).symm
  have hpe : p'.toSubgraph=p.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hze : z.toSubgraph=(T.walk l).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hz : z.IsTrail := by simpa only [z,Walk.isTrail_copy] using T.isTrail l
  have f' : G.Adj (R.start i) x := hRia.symm ▸ f
  have hcon : (Walk.cons f' p').toSubgraph=(Walk.cons f p).toSubgraph := by
    simp only [Walk.toSubgraph,hpe]
    congr 1
    ext a b <;> simp [subgraphOfAdj,hRia]
  have hfp' : (Walk.cons f' p').IsTrail := by
    rw [Walk.isTrail_cons]
    constructor
    · simpa only [p',Walk.isTrail_copy] using hp.of_cons
    · simpa only [p',Walk.edges_copy,hRia] using (Walk.isTrail_cons f p).mp hfp |>.2
  have hdis : Disjoint (Walk.cons f' p').toSubgraph.edgeSet z.toSubgraph.edgeSet := by
    rw [hcon,←hRi,hze,←hRrest l hil.symm hjl.symm]
    exact R.disjoint hil
  obtain ⟨_,hnew,hnewdis,hnewunion⟩ := MobileDefect.same_root_transfer_data f' p' z hfp' hz hdis
  obtain ⟨U,hUi,hUl,hUrest,hUa,hUb,hUs,hUq⟩ :=
    replace_two_starts_general R i l hil x x p' (Walk.cons f'.symm z)
      (by simpa only [p',Walk.isTrail_copy] using hp.of_cons) hnew hnewdis
      (by rw [hnewunion,hcon,←hRi,hze,←hRrest l hil.symm hjl.symm])
  have hquot (v : V) : U.quota v+2*(if T.start j=v then 1 else 0)=
      T.quota v+2*(if x=v then 1 else 0) := by
    have h1 := hRq v
    have h2 := hUq v
    rw [hRia,hRla] at h2
    omega
  have hrq : T.start i ∉ q.support := by
    intro hv
    apply havoid
    rw [←Walk.mem_verts_toSubgraph,hj,Walk.mem_verts_toSubgraph]
    exact List.mem_cons_of_mem _ hv
  have hwq : T.start j ∉ q.support := (Walk.cons_isPath_iff f q).mp hq |>.2
  have hpc : (T.walk i).toSubgraph.verts.ncard=p.toSubgraph.verts.ncard := by
    rw [hi,cons_ncard_of_mem h p hr]
  have hqc : (T.walk j).toSubgraph.verts.ncard=q.toSubgraph.verts.ncard+1 := by
    rw [hj,cons_ncard_of_notMem f q hwq]
  have hnc : (Walk.cons h q).toSubgraph.verts.ncard=q.toSubgraph.verts.ncard+1 :=
    cons_ncard_of_notMem h q hrq
  have hRc : (R.walk l).toSubgraph=(T.walk l).toSubgraph := hRrest l hil.symm hjl.symm
  have hnewc : (Walk.cons f'.symm z).toSubgraph.verts.ncard=
      (T.walk l).toSubgraph.verts.ncard+(if x ∈ (T.walk l).support then 0 else 1) := by
    by_cases hx : x ∈ (T.walk l).support
    · rw [if_pos hx,add_zero,cons_ncard_of_mem f'.symm z (by simpa only [z,Walk.support_copy] using hx),hze]
    · rw [if_neg hx,cons_ncard_of_notMem f'.symm z (by simpa only [z,Walk.support_copy] using hx),hze]
  have hscore : U.score=T.score+(if x ∈ (T.walk l).support then 0 else 1) := by
    rw [hRi,hRc,hpe,hnewc] at hUs
    rw [hpc,hqc,hnc] at hRs
    omega
  refine ⟨U,hquot,hscore,?_,hUi.trans hpe,(hUrest j hij.symm hjl).trans hRj,?_⟩
  · intro hx
    apply hasRoot_of_rep U l (by rw [hUa]; simp [hil.symm])
      (by rw [hUb]) f'.symm z hUl hnew
    simpa only [z,Walk.support_copy] using hx
  · intro a hai haj hal
    exact (hUrest a hai hal).trans (hRrest a hai haj)

lemma maximum_transfer {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : T.start i ∈ p.support)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : T.start i ∉ (T.walk j).support) (hl : T.start l=T.start j) :
    x ∈ (T.walk l).support ∧ ∃ U : TrailFamily G k, U.score=T.score ∧ HasRoot U x ∧
      ∀ v, U.quota v+2*(if T.start j=v then 1 else 0)=
        T.quota v+2*(if x=v then 1 else 0) := by
  have hother := (simple_tail_of_one_defect_rep T hs i h p hp hi hr).2.2
  have hqp : (Walk.cons f q).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ hq (hother j hij.symm) hj.symm
  obtain ⟨U,hUq,hUs,hUr,_⟩ := transfer_data T i j l hij hil hjl h p hp hi hr f q hqp hj havoid hl
  have hx : x ∈ (T.walk l).support := by
    by_contra hx
    rw [if_neg hx] at hUs
    have hh := hm U
    omega
  exact ⟨hx,U,by simpa only [if_pos hx,add_zero] using hUs,hUr hx,hUq⟩

/-- A receiver can be oriented from either of its endpoints without changing
any quota. This wrapper keeps the two supplied first-edge representatives. -/
lemma maximum_transfer_endpoint {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : T.start i ∈ p.support)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : T.start i ∉ (T.walk j).support)
    (hl : T.start j=T.start l ∨ T.start j=T.finish l) :
    x ∈ (T.walk l).support ∧ ∃ U : TrailFamily G k, U.score=T.score ∧ HasRoot U x ∧
      ∀ v, U.quota v+2*(if T.start j=v then 1 else 0)=
        T.quota v+2*(if x=v then 1 else 0) := by
  obtain ⟨R,hRs,hRq,hRl,hRrest,hparts⟩ := orient_endpoint_start T l (T.start j) hl
  obtain ⟨hai,hbi⟩ := hRrest i hil
  obtain ⟨haj,hbj⟩ := hRrest j hjl
  let p' := p.copy rfl hbi.symm
  let q' := q.copy rfl hbj.symm
  have h' : G.Adj (R.start i) x := hai.symm ▸ h
  have f' : G.Adj (R.start j) x := haj.symm ▸ f
  have hpi : Walk.cons h' p'=(Walk.cons h p).copy hai.symm hbi.symm :=
    cons_copy_vertices h p hai.symm rfl hbi.symm h'
  have hqj : Walk.cons f' q'=(Walk.cons f q).copy haj.symm hbj.symm :=
    cons_copy_vertices f q haj.symm rfl hbj.symm f'
  have hip : (R.walk i).toSubgraph=(Walk.cons h' p').toSubgraph := by
    rw [hpi,NormalTrailSystem.walk_copy_subgraph,hparts,hi]
  have hjq : (R.walk j).toSubgraph=(Walk.cons f' q').toSubgraph := by
    rw [hqj,NormalTrailSystem.walk_copy_subgraph,hparts,hj]
  have hav : R.start i ∉ (R.walk j).support := by
    rw [hai,←Walk.mem_verts_toSubgraph,hparts,Walk.mem_verts_toSubgraph]
    exact havoid
  obtain ⟨hx,U,hUs,hUr,hUq⟩ := maximum_transfer R (by omega) (fun U ↦ by rw [hRs]; exact hm U)
    i j l hij hil hjl h' p' (by rw [hpi]; simpa only [Walk.isTrail_copy] using hp) hip
    (by simpa only [p',Walk.support_copy,hai] using hr)
    f' q' (by rw [hqj]; simpa only [Walk.isTrail_copy] using hq) hjq hav (hRl.trans haj.symm)
  refine ⟨?_,U,hUs.trans hRs,hUr,?_⟩
  · rwa [←Walk.mem_verts_toSubgraph,hparts,Walk.mem_verts_toSubgraph] at hx
  · intro v
    simpa only [haj,hRq] using hUq v

/-- A same-score rooted transfer into a zero quota cannot remove a pair from
quota at least three at a minimum of quota-square energy. -/
lemma terminal_quota_le_two {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : T.start i ∈ p.support)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : T.start i ∉ (T.walk j).support)
    (hl : T.start j=T.start l ∨ T.start j=T.finish l)
    (hx : T.quota x=0)
    (hmin : ∀ (U : TrailFamily G k) (r : V), U.score=T.score → HasRoot U r →
      RootEnergy.quotaEnergy T ≤ RootEnergy.quotaEnergy U) : T.quota (T.start j) ≤ 2 := by
  obtain ⟨_,U,hUs,hUr,hUq⟩ := maximum_transfer_endpoint T hs hm i j l hij hil hjl
    h p hp hi hr f q hq hj havoid hl
  have hbalance := RootEnergy.pair_energy_balance T.quota U.quota (T.start j) x f.ne hx hUq
  have hbound := hmin U x hUs hUr
  change RootEnergy.quotaEnergy U+4*T.quota (T.start j)=RootEnergy.quotaEnergy T+8 at hbalance
  omega

lemma third_endpoint_of_quota_ge_three {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j) (w : V)
    (hi : T.start i ≠ w) (hj : T.finish j ≠ w) (hw : 3 ≤ T.quota w) :
    ∃ l, l ≠ i ∧ l ≠ j ∧ (T.start l=w ∨ T.finish l=w) := by
  classical
  by_contra! hn
  have hb (l : Fin k) : ((if T.start l=w then 1 else 0)+(if T.finish l=w then 1 else 0) : ℕ) ≤
      (if l=i then 1 else 0)+(if l=j then 1 else 0) := by
    by_cases hli : l=i
    · subst l
      simp only [if_neg hij,if_neg hi,zero_add,add_zero]
      split_ifs <;> omega
    · by_cases hlj : l=j
      · subst l
        simp only [if_neg hij.symm,if_neg hj,add_zero,zero_add]
        split_ifs <;> omega
      · obtain ⟨ha,hb⟩ := hn l hli hlj
        simp only [if_neg hli,if_neg hlj,if_neg ha,if_neg hb,add_zero,le_refl]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun l _ ↦ hb l)
  rw [←quota_eq_sum_endpoints T w] at hh
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hh
  omega

/-- An outside path ending immediately beside a zero-quota exposed vertex
has starting quota at most two in a rooted energy minimum. The other endpoint
needed for the transfer is obtained from the quota count; no assumption about
its path's intersections is required. -/
lemma outside_terminal_quota_le_two {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : T.start i ∈ p.support)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : T.start i ∉ (T.walk j).support) (hx : T.quota x=0)
    (hmin : ∀ (U : TrailFamily G k) (r : V), U.score=T.score → HasRoot U r →
      RootEnergy.quotaEnergy T ≤ RootEnergy.quotaEnergy U) : T.quota (T.start j) ≤ 2 := by
  by_contra! hlarge
  have hother := (simple_tail_of_one_defect_rep T hs i h p hp hi hr).2.2
  have hqp : (Walk.cons f q).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ hq (hother j hij.symm) hj.symm
  have hrw : T.start i ≠ T.start j := fun he ↦ havoid (he.symm ▸ (T.walk j).start_mem_support)
  have hjw : T.finish j ≠ T.start j := by
    intro he
    have hnot := (Walk.cons_isPath_iff f q).mp hqp |>.2
    exact hnot (he ▸ q.end_mem_support)
  obtain ⟨l,hli,hlj,hl⟩ := third_endpoint_of_quota_ge_three T i j hij (T.start j) hrw hjw (by omega)
  have hb := terminal_quota_le_two T hs hm i j l hij hli.symm hlj.symm
    h p hp hi hr f q hq hj havoid (hl.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)) hx hmin
  omega

/-- Swapping the exposed leading edge with the leading edge of an outside
path either raises the incidence score or relocates the root to that path's
starting vertex. At a maximum only the latter is possible, and all quotas
are preserved. -/
lemma swap_to_outside_terminal {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : T.start i ∈ p.support)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsPath)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : T.start i ∉ (T.walk j).support) :
    T.start j ∈ p.support ∧ ∃ U : TrailFamily G k,
      U.score=T.score ∧ (∀ v, U.quota v=T.quota v) ∧ HasRoot U (T.start j) ∧
      (U.walk i).toSubgraph=(Walk.cons f p).toSubgraph ∧
      (U.walk j).toSubgraph=(Walk.cons h q).toSubgraph ∧
      U.start i=T.start j ∧ U.finish i=T.finish i ∧
      ∀ l, l ≠ i → l ≠ j → (U.walk l).toSubgraph=(T.walk l).toSubgraph := by
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (Walk.cons f q).toSubgraph.edgeSet := by
    rw [←hi,←hj]; exact T.disjoint hij
  obtain ⟨hfp,hhq,hd',hu⟩ := exchange_first_edges_data h f p q hp hq.isTrail hd
  obtain ⟨U,hUi,hUj,hrest,hUa,hUb,hUs,hUq⟩ := replace_two_starts_general T i j hij
    (T.start j) (T.start i) (Walk.cons f p) (Walk.cons h q) hfp hhq hd'
    (by rw [hu,←hi,←hj])
  have hrq : T.start i ∉ q.support := by
    intro hx
    apply havoid
    rw [←Walk.mem_verts_toSubgraph,hj,Walk.mem_verts_toSubgraph]
    exact List.mem_cons_of_mem _ hx
  have hwq : T.start j ∉ q.support := (Walk.cons_isPath_iff f q).mp hq |>.2
  rw [hi,hj,cons_ncard_of_mem h p hr,cons_ncard_of_notMem f q hwq,
    cons_ncard_of_notMem h q hrq] at hUs
  have hw : T.start j ∈ p.support := by
    by_contra hw
    rw [cons_ncard_of_notMem f p hw] at hUs
    have hh := hm U
    omega
  rw [cons_ncard_of_mem f p hw] at hUs
  refine ⟨hw,U,by omega,?_,?_,hUi,hUj,by rw [hUa]; simp,congrFun hUb i,hrest⟩
  · intro v
    have hh := hUq v
    omega
  · exact hasRoot_of_rep U i (by rw [hUa]; simp) (by rw [hUb]) f p hUi hfp hw

/-- In particular, the starting quota of the outside path is at most two.
Unlike the earlier three-member corollary, this needs neither a second path
with that endpoint nor a zero quota at the common neighbor. -/
lemma outside_terminal_quota_le_two_any {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : T.start i ∈ p.support)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : T.start i ∉ (T.walk j).support)
    (hmin : ∀ (U : TrailFamily G k) (r : V), U.score=T.score → HasRoot U r →
      RootEnergy.quotaEnergy T ≤ RootEnergy.quotaEnergy U) : T.quota (T.start j) ≤ 2 := by
  have hother := (simple_tail_of_one_defect_rep T hs i h p hp hi hr).2.2
  have hqp : (Walk.cons f q).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ hq (hother j hij.symm) hj.symm
  obtain ⟨_,U,hUs,hUq,hUr,_⟩ := swap_to_outside_terminal T hm i j hij h p hp hi hr f q hqp hj havoid
  have he : RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T := by
    simp only [RootEnergy.quotaEnergy,hUq]
  have hb := RootEnergy.root_quota_le_two_of_minimum_energy U (T.start j) (by omega)
    (fun R ↦ by rw [hUs]; exact hm R) hUr (fun R r hRs hRr ↦ by
      rw [he]
      exact hmin R r (hRs.trans hUs) hRr)
  rwa [hUq] at hb

end Erdos583SurplusNeighborDevelopment
