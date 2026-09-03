import Submission.Work

/-! Endpoint-quota energy for a globally maximal rooted single defect.
The descent only bounds the quota at a defect root; it does not normalize
all endpoint quotas or repair the remaining single defect. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
namespace Erdos583RootEnergyDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

noncomputable def quotaEnergy {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : ℕ := ∑ v, (T.quota v)^2

lemma root_quota_pos {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} (hr : HasRoot T r) : 0 < T.quota r := by
  obtain ⟨A,R,ρ,hρ,_⟩ := hr
  apply Nat.card_pos_iff.mpr
  exact ⟨⟨⟨ρ.val,hρ⟩⟩,inferInstance⟩

lemma maximum_defect_no_paths {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (P : TrailFamily G k) :
    ¬∀ i, (P.walk i).IsPath := by
  intro hp
  have hh := P.score_eq_edges_add_iff.mpr hp
  have hbound := hm P
  omega

/-- Any exposed outside label has zero quota at a nonpath global maximum. -/
lemma exposed_quota_zero {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r z : V} {A : Finset (Fin k)} {B : Finset V}
    (hE : ExposedRoot T r A B z) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hz : z ∉ B) : T.quota z=0 := by
  by_contra hn
  have hp : 0 < T.quota z := Nat.pos_of_ne_zero hn
  obtain ⟨P,_,hP⟩ := exposedRoot_repair_of_positive hE hs hz hp
  exact maximum_defect_no_paths T hs hm P hP

lemma two_zero_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r) :
    ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧ T.quota x=0 ∧ T.quota y=0 := by
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  obtain ⟨B,_,x,y,hxy,hrx,hry,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hn
  exact ⟨x,y,hxy,hrx,hry,exposed_quota_zero hEx hs hm hxB,exposed_quota_zero hEy hs hm hyB⟩

/-- The exact square-energy balance for moving a pair into an empty quota. -/
lemma pair_energy_balance {V : Type*} [Fintype V] (q Q : V → ℕ) (r x : V)
    (hrx : r ≠ x) (hx : q x=0)
    (hbal : ∀ v, Q v+2*(if r=v then 1 else 0)=q v+2*(if x=v then 1 else 0)) :
    (∑ v, (Q v)^2) + 4*q r = (∑ v, (q v)^2)+8 := by
  classical
  have hQr : Q r+2=q r := by simpa only [if_pos rfl,if_neg hrx.symm,mul_one,mul_zero,add_zero] using hbal r
  have hQx : Q x=2 := by simpa only [if_neg hrx,if_pos rfl,mul_zero,mul_one,add_zero,hx,zero_add] using hbal x
  have hrest : ∑ v ∈ (Finset.univ.erase r).erase x, (Q v)^2 =
      ∑ v ∈ (Finset.univ.erase r).erase x, (q v)^2 := by
    apply Finset.sum_congr rfl
    intro v hv
    obtain ⟨hvx,hvr⟩ := Finset.mem_erase.mp hv
    have hvr' := (Finset.mem_erase.mp hvr).1
    have hh : Q v=q v := by
      simpa only [if_neg hvr'.symm,if_neg hvx.symm,mul_zero,add_zero] using hbal v
    rw [hh]
  rw [NormalTrailSystem.sum_extract_two (fun v ↦ (Q v)^2) r x hrx,
    NormalTrailSystem.sum_extract_two (fun v ↦ (q v)^2) r x hrx,hrest,hQx,hx]
  nlinarith

lemma root_quota_le_two_of_minimum_energy {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r)
    (hmin : ∀ (U : TrailFamily G k) (s : V), U.score=T.score → HasRoot U s →
      quotaEnergy T ≤ quotaEnergy U) : T.quota r ≤ 2 := by
  by_contra! hq
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  obtain ⟨B,_,x,_,_,hrx,_,hxB,_,hEx,_⟩ := R.two_root_exposures ρ hρ hn
  have hx0 : T.quota x=0 := exposed_quota_zero hEx hs hm hxB
  obtain ⟨U,hUq,hU⟩ := exposedRoot_move_pair_or_repair hEx hs (by omega)
  rcases hU with hP | ⟨hUs,hUr⟩
  · exact maximum_defect_no_paths T hs hm U hP
  · have hb := hmin U x hUs hUr
    have he := pair_energy_balance T.quota U.quota r x hrx.ne hx0 hUq
    change quotaEnergy U+4*T.quota r=quotaEnergy T+8 at he
    omega

lemma exists_minimum_root_energy {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V) (hr : HasRoot T r) :
    ∃ (S : TrailFamily G k) (s : V), S.score=T.score ∧ HasRoot S s ∧
      ∀ (U : TrailFamily G k) (u : V), U.score=T.score → HasRoot U u →
        quotaEnergy S ≤ quotaEnergy U := by
  classical
  let P (n : ℕ) := ∃ (S : TrailFamily G k) (s : V), S.score=T.score ∧ HasRoot S s ∧ quotaEnergy S=n
  have hex : ∃ n, P n := ⟨quotaEnergy T,T,r,rfl,hr,rfl⟩
  obtain ⟨S,s,hS,hroot,hE⟩ := Nat.find_spec hex
  refine ⟨S,s,hS,hroot,?_⟩
  intro U u hU hrootU
  rw [hE]
  exact Nat.find_min' hex ⟨U,u,hU,hrootU,rfl⟩

/-- A rooted single-defect maximum can be chosen with root quota one or two.
Other vertices are not asserted to have bounded endpoint quotas. -/
lemma exists_small_root_quota {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r) :
    ∃ (S : TrailFamily G k) (s : V), S.score=T.score ∧ HasRoot S s ∧
      (∀ U : TrailFamily G k, U.score ≤ S.score) ∧
      (S.quota s=1 ∨ S.quota s=2) ∧
      (∀ (U : TrailFamily G k) (u : V), U.score=S.score → HasRoot U u →
        quotaEnergy S ≤ quotaEnergy U) := by
  obtain ⟨S,s,hS,hroot,hmin⟩ := exists_minimum_root_energy T r hr
  have hSm (U : TrailFamily G k) : U.score ≤ S.score := by rw [hS]; exact hm U
  have hSmin (U : TrailFamily G k) (u : V) (hU : U.score=S.score) (hu : HasRoot U u) :
      quotaEnergy S ≤ quotaEnergy U := hmin U u (hU.trans hS) hu
  have hbound := root_quota_le_two_of_minimum_energy S s (by omega) hSm hroot hSmin
  have hpos := root_quota_pos hroot
  exact ⟨S,s,hS,hroot,hSm,by omega,hSmin⟩

/-- If every indexed member contains a rooted repetition, distinct final
edges of the non-root endpoint tails, together with the two closed-tail edges,
force a lower bound on the root degree. Duplicate endpoint labels are counted
as separate tails. -/
lemma degree_bound_of_all_members_contain_root {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V) (hr : HasRoot T r)
    (hall : ∀ i, r ∈ (T.walk i).support) :
    2*k-T.quota r+2 ≤ Nat.card (G.neighborSet r) := by
  classical
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  have hA : A=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    exact R.outside i hi (hall i)
  subst A
  let tail (s : Fin k × Bool) := R.tail ⟨s,Finset.mem_univ s.1⟩
  let N := {s : Fin k × Bool // T.endpoint s ≠ r}
  let C := (R.tail ρ).copy hρ rfl
  have hc : C.IsTrail := by simpa only [C,Walk.isTrail_copy] using R.trail ρ
  have hcn : ¬C.Nil := by simpa only [C,Walk.nil_copy] using hn
  have heC : C.toSubgraph=(R.tail ρ).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have htn (s : N) : ¬(tail s.val).Nil := Walk.not_nil_of_ne s.property
  let f (s : N) := (tail s.val).penultimate
  have hedge (s : N) : s(f s,r) ∈ (tail s.val).toSubgraph.edgeSet :=
    (tail s.val).toSubgraph_adj_penultimate (htn s)
  have hinj : Function.Injective f := by
    intro s t he
    by_contra hst
    have hslots : (⟨s.val,Finset.mem_univ s.val.1⟩ : {s : Fin k × Bool // s.1 ∈ Finset.univ}) ≠
        ⟨t.val,Finset.mem_univ t.val.1⟩ := by
      intro hh
      exact hst (Subtype.ext (congrArg (fun z : {s : Fin k × Bool // s.1 ∈ (Finset.univ : Finset (Fin k))} ↦ z.val) hh))
    have hdis := R.disjoint hslots
    have h1 := hedge s
    have h2 := hedge t
    rw [he] at h1
    exact Set.disjoint_left.mp hdis h1 h2
  have hdis (s : N) : Disjoint C.toSubgraph.edgeSet (tail s.val).toSubgraph.edgeSet := by
    rw [heC]
    apply R.disjoint
    intro he
    have hs : T.endpoint s.val=r := by
      rw [←congrArg Subtype.val he]
      exact hρ
    exact s.property hs
  let F := Finset.univ.image f
  have havoid (z : V) (hz : C.toSubgraph.Adj z r) : z ∉ F := by
    intro hmem
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hmem
    have he := hedge s
    rw [hs] at he
    exact Set.disjoint_left.mp (hdis s) hz he
  have hcs : C.snd ∉ F := havoid _ (C.toSubgraph_adj_snd hcn).symm
  have hcp : C.penultimate ∉ F := havoid _ (C.toSubgraph_adj_penultimate hcn)
  have hdf : Disjoint F {C.snd,C.penultimate} := by
    apply Finset.disjoint_left.mpr
    intro z hz hzp
    rcases (show z=C.snd ∨ z=C.penultimate by simpa using hzp) with rfl|rfl
    · exact hcs hz
    · exact hcp hz
  have hsub : F ∪ {C.snd,C.penultimate} ⊆ G.neighborFinset r := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hz
      exact (G.mem_neighborFinset r _).mpr ((tail s.val).adj_penultimate (htn s)).symm
    · rcases (show z=C.snd ∨ z=C.penultimate by simpa using hz) with rfl|rfl
      · exact (G.mem_neighborFinset r _).mpr (C.adj_snd hcn)
      · exact (G.mem_neighborFinset r _).mpr (C.adj_penultimate hcn).symm
  have hcap := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdf,Finset.card_pair
    (TrailNormalization.closed_trail_snd_ne_penultimate C hc hcn)] at hcap
  have hfcard : F.card=Fintype.card N := by simp only [F,Finset.card_image_of_injective _ hinj,Finset.card_univ]
  rw [hfcard,card_neighborFinset_eq_degree] at hcap
  have hN : Fintype.card N=2*k-T.quota r := by
    simpa only [N,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm,
      TrailFamily.quota,Nat.card_eq_fintype_card] using
      Fintype.card_subtype_compl (fun s : Fin k × Bool ↦ T.endpoint s=r)
  rw [hN] at hcap
  simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hcap

/-- At the conjectured budget a root of quota at most two has an outside
member. The statement does not assert that an endpoint of that member is
reachable by the rooted exchange procedure. -/
lemma exists_member_avoiding_small_quota_root {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V) (hr : HasRoot T r)
    (hq : T.quota r ≤ 2) (hk : Fintype.card V ≤ 2*k) :
    ∃ i, r ∉ (T.walk i).support := by
  classical
  by_contra! hall
  have hdeg := degree_bound_of_all_members_contain_root T r hr hall
  have hlt := G.degree_lt_card_verts r
  have hlt' : Nat.card (G.neighborSet r) < Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hlt
  omega

lemma sum_quota {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : ∑ v, T.quota v=2*k := by
  classical
  simp_rw [quota_eq_sum_endpoints]
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib,Nat.mul_comm]

/-- The budget and the two empty exposed quotas require an endpoint surplus
away from a small-quota root. This does not supply a transport to the defect. -/
lemma exists_other_surplus {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r)
    (hq : T.quota r ≤ 2) (hk : Fintype.card V ≤ 2*k) :
    ∃ w, w ≠ r ∧ 2 ≤ T.quota w := by
  classical
  obtain ⟨x,y,hxy,hrx,hry,hx,hy⟩ := two_zero_neighbors T r hs hm hr
  by_contra! hn
  have hb (v : V) : T.quota v+(if v=x then 1 else 0)+(if v=y then 1 else 0) ≤
      1+(if v=r then 1 else 0) := by
    by_cases hvx : v=x
    · subst v
      simp [hx,hxy,hrx.ne.symm]
    · by_cases hvy : v=y
      · subst v
        simp [hy,hxy.symm,hry.ne.symm]
      · by_cases hvr : v=r
        · subst v
          simpa only [if_neg hvx,if_neg hvy,if_pos rfl,add_zero] using hq
        · have hh := hn v hvr
          simp only [if_neg hvx,if_neg hvy,if_neg hvr,add_zero]
          omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦ hb v)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,sum_quota] at hh
  omega

/-- A root of quota two cannot have an acyclic zero-baseline graph. The
baseline removes its one movable pair and fixes every other endpoint quota. -/
lemma zero_baseline_not_acyclic {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r)
    (hq : T.quota r=2) : ¬(G.induce {v | T.quota v=0 ∨ v=r}).IsAcyclic := by
  classical
  intro hforest
  let c (v : V) := if v=r then 0 else T.quota v
  have hq' (v : V) : T.quota v=c v+2*(if r=v then 1 else 0) := by
    by_cases hv : v=r
    · subst v
      simp [c,hq]
    · simp [c,hv,Ne.symm hv]
  have hc : {v | c v=0}={v | T.quota v=0 ∨ v=r} := by
    ext v
    by_cases hv : v=r <;> simp [c,hv]
  have hforest' : (G.induce {v | c v=0}).IsAcyclic := by rwa [hc]
  obtain ⟨_,P,_,hP⟩ := ForestZeroNormalization.normalize_one_defect_forest T c r hs hq' hr hforest'
  exact maximum_defect_no_paths T hs hm P hP

end Erdos583RootEnergyDevelopment
