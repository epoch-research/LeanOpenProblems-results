import Submission.Work

/-! A tracked three-member transfer of a rooted trail defect.
This is a local exchange, not an existence theorem for the exchange. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
namespace Erdos583ThreeTransferDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma quota_balance_one_slot {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T S : TrailFamily G k) (j : Fin k)
    (hrest : ∀ i, i ≠ j → S.start i=T.start i ∧ S.finish i=T.finish i) (v : V) :
    S.quota v + (if T.start j=v then 1 else 0) + (if T.finish j=v then 1 else 0) =
      T.quota v + (if S.start j=v then 1 else 0) + (if S.finish j=v then 1 else 0) := by
  classical
  have hsum : (∑ i ∈ Finset.univ.erase j,
      ((if S.start i=v then 1 else 0)+(if S.finish i=v then 1 else 0) : ℕ)) =
      ∑ i ∈ Finset.univ.erase j,
        ((if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0) : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨ha,hb⟩ := hrest i (Finset.mem_erase.mp hi).1
    rw [ha,hb]
  have hS := Finset.sum_erase_add (Finset.univ : Finset (Fin k))
    (fun i ↦ ((if S.start i=v then 1 else 0)+(if S.finish i=v then 1 else 0) : ℕ))
    (Finset.mem_univ j)
  have hT := Finset.sum_erase_add (Finset.univ : Finset (Fin k))
    (fun i ↦ ((if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0) : ℕ))
    (Finset.mem_univ j)
  rw [←quota_eq_sum_endpoints S v] at hS
  rw [←quota_eq_sum_endpoints T v] at hT
  dsimp only at hS hT
  omega

lemma relocate_nil_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (j : Fin k) (hj : (T.walk j).Nil) (x : V) :
    ∃ S : TrailFamily G k, S.score=T.score ∧ S.start j=x ∧ S.finish j=x ∧
      (S.walk j).Nil ∧
      (∀ i, i ≠ j → S.start i=T.start i ∧ S.finish i=T.finish i ∧
        (S.walk i).toSubgraph=(T.walk i).toSubgraph) ∧
      ∀ v, S.quota v+2*(if T.finish j=v then 1 else 0) =
        T.quota v+2*(if x=v then 1 else 0) := by
  classical
  obtain ⟨S,hs,ha,hb,hn,hrest⟩ := NilSlot.relocate_nil T j hj x
  refine ⟨S,hs,ha,hb,hn,hrest,?_⟩
  intro v
  have h := quota_balance_one_slot T S j (fun i hi ↦ ⟨(hrest i hi).1,(hrest i hi).2.1⟩) v
  have hab : T.start j=T.finish j := hj.eq
  rw [hab,ha,hb] at h
  omega

lemma hasRoot_of_append_rep {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {a w b : V}
    (ha : T.start i=a) (hb : T.finish i=b)
    (p : G.Walk a w) (q : G.Walk w b) (hp : ¬p.Nil)
    (ht : (p.append q).IsTrail) (hv : a ∈ q.support)
    (he : (T.walk i).toSubgraph=(p.append q).toSubgraph) : HasRoot T a := by
  cases p with
  | nil => exact (hp Walk.Nil.nil).elim
  | cons h p =>
    apply hasRoot_of_rep T i ha hb h (p.append q)
    · simpa only [Walk.cons_append] using he
    · simpa only [Walk.cons_append] using ht
    · rw [Walk.mem_support_append_iff]
      exact Or.inr hv

/-- A merge with two common vertices creates a nil slot, losing one incidence.
The merge retains a repeated start and preserves every endpoint quota. -/
lemma merge_two_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (j l : Fin k) (hjl : j ≠ l)
    (hjoin : T.finish j=T.start l) (hn : ¬(T.walk j).Nil)
    (hv : T.start j ∈ (T.walk l).support)
    (hint : ((T.walk j).toSubgraph.verts ∩ (T.walk l).toSubgraph.verts).ncard=2) :
    ∃ S : TrailFamily G k, S.score+1=T.score ∧ (∀ v, S.quota v=T.quota v) ∧
      S.start j=T.finish j ∧ S.finish j=T.finish j ∧ (S.walk j).Nil ∧
      S.start l=T.start j ∧ S.finish l=T.finish l ∧
      (S.walk l).toSubgraph=(T.walk j).toSubgraph ⊔ (T.walk l).toSubgraph ∧
      HasRoot S (T.start j) ∧
      ∀ i, i ≠ j → i ≠ l → S.start i=T.start i ∧ S.finish i=T.finish i ∧
        (S.walk i).toSubgraph=(T.walk i).toSubgraph := by
  classical
  let q := (T.walk l).copy hjoin.symm rfl
  let r := (T.walk j).append q
  let p : G.Walk (T.finish j) (T.finish j) := Walk.nil
  have hq : q.IsTrail := by simpa [q] using T.isTrail l
  have hqe : q.toSubgraph=(T.walk l).toSubgraph :=
    NormalTrailSystem.walk_copy_subgraph _ _ _
  have hr : r.IsTrail := trail_append_of_disjoint (T.isTrail j) hq (by rw [hqe]; exact T.disjoint hjl)
  have hre : r.toSubgraph=(T.walk j).toSubgraph ⊔ (T.walk l).toSubgraph := by
    simp only [r,Walk.toSubgraph_append,hqe]
  obtain ⟨S,hSj,hSl,hparts,hstarts,hfinish,hscore,hquota⟩ :=
    replace_two_starts_general T j l hjl (T.finish j) (T.start j) p r Walk.IsTrail.nil hr
      (by simp [p]) (by simp [p,hre])
  have hsa : S.start j=T.finish j := by rw [hstarts]; simp
  have hsb : S.finish j=T.finish j := congrFun hfinish j
  have hla : S.start l=T.start j := by rw [hstarts]; simp [hjl.symm]
  have hlb : S.finish l=T.finish l := congrFun hfinish l
  have hSn : (S.walk j).Nil := by
    apply Walk.nil_iff_length_eq.mpr
    rw [←trail_edgeSet_ncard _ (S.isTrail j),hSj]
    simp [p]
  have hcard := Set.ncard_union_add_ncard_inter (T.walk j).toSubgraph.verts (T.walk l).toSubgraph.verts
  rw [hint] at hcard
  rw [hre,Subgraph.verts_sup,show p.toSubgraph.verts.ncard=1 by simp [p]] at hscore
  refine ⟨S,by omega,?_,hsa,hsb,hSn,hla,hlb,hSl.trans hre,?_,?_⟩
  · intro v
    have h := hquota v
    rw [←hjoin] at h
    omega
  · apply hasRoot_of_append_rep S l hla hlb (T.walk j) q hn hr _ hSl
    simpa only [q,Walk.support_copy] using hv
  · intro i hij hil
    exact ⟨by rw [hstarts]; simp [hij,hil],congrFun hfinish i,hparts i hij hil⟩

/-- Splitting the first edge from a repeated-start representative into an
already relocated nil slot gains one incidence and preserves all quotas. -/
lemma split_nil_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support) (hj : (T.walk j).Nil) (hbj : T.finish j=x) :
    ∃ U : TrailFamily G k, U.score=T.score+1 ∧ (∀ v, U.quota v=T.quota v) ∧
      (U.walk i).toSubgraph=p.toSubgraph ∧
      (U.walk j).toSubgraph=(Walk.cons h Walk.nil).toSubgraph ∧
      ∀ l, l ≠ i → l ≠ j → U.start l=T.start l ∧ U.finish l=T.finish l ∧
        (U.walk l).toSubgraph=(T.walk l).toSubgraph := by
  classical
  let L : G.Walk (T.start i) x := Walk.cons h Walk.nil
  let q := L.copy rfl hbj.symm
  have hq : q.IsTrail := by
    dsimp only [q]
    rw [Walk.isTrail_copy]
    exact Walk.IsTrail.nil.cons h (by simp)
  have hqe : q.toSubgraph=L.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hpart : L.append p=Walk.cons h p := rfl
  have hdp : Disjoint p.toSubgraph.edgeSet L.toSubgraph.edgeSet :=
    (append_trail_disjoint (hpart.symm ▸ hp)).symm
  have hnil : (T.walk j).toSubgraph.edgeSet=∅ := by
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_eq_nil.mpr hj,List.not_mem_nil,Set.mem_empty_iff_false]
  have hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [he,←hpart,Walk.toSubgraph_append,Subgraph.edgeSet_sup,hnil,Set.union_empty,hqe]
    exact Set.union_comm _ _
  obtain ⟨U,hUi,hUj,hparts,hstarts,hfinish,hscore,hquota⟩ :=
    replace_two_starts_general T i j hij x (T.start i) p q hp.of_cons hq (by rw [hqe]; exact hdp) hu
  have hcard : L.toSubgraph.verts.ncard=2 := by
    rw [cons_ncard_of_notMem h Walk.nil (by simpa using h.ne)]
    simp
  rw [he,cons_ncard_of_mem h p hv,NilSlot.nil_vertex_ncard hj,hqe,hcard] at hscore
  refine ⟨U,by omega,?_,hUi,hUj.trans hqe,?_⟩
  · intro v
    have hh := hquota v
    rw [hj.eq,hbj] at hh
    omega
  · intro l hli hlj
    exact ⟨by rw [hstarts]; simp [hli,hlj],congrFun hfinish l,hparts l hli hlj⟩

/-- Splitting the old repeated start and merging two other members transfers
the defect at unchanged score. The shared endpoint loses a pair and the split
vertex gains a pair. The second common vertex must be an endpoint of the merge,
so the new defect is rooted. -/
lemma three_member_transfer {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (hjoin : T.finish j=T.start l) (hn : ¬(T.walk j).Nil)
    (hrep : T.start j ∈ (T.walk l).support)
    (hint : ((T.walk j).toSubgraph.verts ∩ (T.walk l).toSubgraph.verts).ncard=2) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ HasRoot U (T.start j) ∧
      ∀ v, U.quota v+2*(if T.finish j=v then 1 else 0) =
        T.quota v+2*(if x=v then 1 else 0) := by
  classical
  obtain ⟨S,hSs,hSq,_,hSjb,hSjn,hSla,hSlb,hSl,_,hSrest⟩ :=
    merge_two_tracked T j l hjl hjoin hn hrep hint
  obtain ⟨R,hRs,_,hRjb,hRjn,hRrest,hRq⟩ := relocate_nil_tracked S j hSjn x
  obtain ⟨hRia,hRib,hRi⟩ := hRrest i hij
  obtain ⟨hSia,hSib,hSi⟩ := hSrest i hij hil
  have ha : R.start i=T.start i := hRia.trans hSia
  have hb : R.finish i=T.finish i := hRib.trans hSib
  let h' : G.Adj (R.start i) x := ha.symm ▸ h
  let p' := p.copy rfl hb.symm
  have hp'e : p'.toSubgraph=p.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hc : (Walk.cons h' p').toSubgraph=(Walk.cons h p).toSubgraph := by
    change G.subgraphOfAdj h' ⊔ p'.toSubgraph=G.subgraphOfAdj h ⊔ p.toSubgraph
    rw [hp'e]
    congr 1
    ext u v <;> simp [SimpleGraph.subgraphOfAdj,ha]
  have hp' : (Walk.cons h' p').IsTrail := by
    rw [Walk.isTrail_cons]
    refine ⟨by simpa only [p',Walk.isTrail_copy] using hp.of_cons,?_⟩
    simpa only [p',Walk.edges_copy,ha] using (Walk.isTrail_cons h p).mp hp |>.2
  have hv' : R.start i ∈ p'.support := by simpa only [p',Walk.support_copy,ha] using hv
  obtain ⟨U,hUs,hUq,_,_,hUrest⟩ := split_nil_tracked R i j hij h' p' hp'
    ((hRi.trans hSi).trans (he.trans hc.symm)) hv' hRjn hRjb
  refine ⟨U,by omega,?_,?_⟩
  · obtain ⟨hUla,hUlb,hUl⟩ := hUrest l hil.symm hjl.symm
    obtain ⟨hRla,hRlb,hRl⟩ := hRrest l hjl.symm
    let q := (T.walk l).copy hjoin.symm rfl
    have hqe : q.toSubgraph=(T.walk l).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
    have hqt : q.IsTrail := by simpa only [q,Walk.isTrail_copy] using T.isTrail l
    apply hasRoot_of_append_rep U l (hUla.trans (hRla.trans hSla))
      (hUlb.trans (hRlb.trans hSlb)) (T.walk j) q hn
    · exact trail_append_of_disjoint (T.isTrail j) hqt (by rw [hqe]; exact T.disjoint hjl)
    · simpa only [q,Walk.support_copy] using hrep
    · rw [hUl,hRl,hSl,Walk.toSubgraph_append,hqe]
  · intro v
    rw [hUq]
    have hh := hRq v
    rwa [hSjb,hSq] at hh

/-- At a rooted minimum of quota-square energy, any available three-member
transfer into a zero-quota split vertex must remove its pair from quota at most
two. No global existence of such a transfer is asserted. -/
lemma shared_endpoint_quota_le_two {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (hjoin : T.finish j=T.start l) (hn : ¬(T.walk j).Nil)
    (hrep : T.start j ∈ (T.walk l).support)
    (hint : ((T.walk j).toSubgraph.verts ∩ (T.walk l).toSubgraph.verts).ncard=2)
    (hx : T.quota x=0)
    (hmin : ∀ (U : TrailFamily G k) (r : V), U.score=T.score → HasRoot U r →
      RootEnergy.quotaEnergy T ≤ RootEnergy.quotaEnergy U) : T.quota (T.finish j) ≤ 2 := by
  by_contra! hlarge
  obtain ⟨U,hUs,hUr,hUq⟩ := three_member_transfer T i j l hij hil hjl h p hp he hv
    hjoin hn hrep hint
  have hwx : T.finish j ≠ x := by intro hh; rw [hh,hx] at hlarge; omega
  have henergy := RootEnergy.pair_energy_balance T.quota U.quota (T.finish j) x hwx hx hUq
  change RootEnergy.quotaEnergy U+4*T.quota (T.finish j)=RootEnergy.quotaEnergy T+8 at henergy
  have hbound := hmin U (T.start j) hUs hUr
  omega

end Erdos583ThreeTransferDevelopment
