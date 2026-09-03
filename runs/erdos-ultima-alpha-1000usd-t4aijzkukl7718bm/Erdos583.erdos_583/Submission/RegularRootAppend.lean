import Submission.PathFamilyRootedCut
import Submission.AssembleRootedCutGraphs

/-! Appending a new edge to the same root preserves regular rooted cuts.
No all-path hypothesis is imposed on the intermediate family. -/
namespace Erdos583RegularRootAppendDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583RegularRootedCutDevelopment Erdos583RegularTailRearrangementDevelopment
open Erdos583RegularFlowerExposuresDevelopment Erdos583RootedFlowerSurgeryDevelopment
open Erdos583AssembleRootedCutGraphsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma regularTail_mapLe {V : Type*} {H G : SimpleGraph V} (hHG : H ≤ G)
    {a r : V} (p : H.Walk a r) (hp : RegularTail p) : RegularTail (p.mapLe hHG) := by
  rcases hp with hp|⟨ha,hc⟩
  · exact Or.inl (hp.mapLe hHG)
  · refine Or.inr ⟨ha,?_⟩
    simpa [Walk.mapLe] using hc

lemma quota_update_endpoint {V : Type*} {H G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily H k) (U : TrailFamily G k) (τ : Fin k × Bool) (r : V)
    (he : ∀ s, U.endpoint s=if s=τ then r else T.endpoint s) (v : V) :
    U.quota v+(if T.endpoint τ=v then 1 else 0)=T.quota v+(if r=v then 1 else 0) := by
  classical
  have hrest (i : Fin k) (hi : i ≠ τ.1) : U.start i=T.start i ∧ U.finish i=T.finish i := by
    have ht : (i,true) ≠ τ := fun hh ↦ hi (congrArg Prod.fst hh)
    have hf : (i,false) ≠ τ := fun hh ↦ hi (congrArg Prod.fst hh)
    exact ⟨by simpa only [if_neg ht,TrailFamily.endpoint,if_true] using he (i,true),
      by simpa only [if_neg hf,TrailFamily.endpoint,Bool.false_eq_true,if_false] using he (i,false)⟩
  have hb := DeletionEndpoint.quota_balance_one_slot_graphs T U τ.1 hrest v
  rcases τ with ⟨i,b⟩
  dsimp only [Prod.fst] at hb
  cases b
  · have hUs : U.start i=T.start i := by simpa [TrailFamily.endpoint] using he (i,true)
    have hUf : U.finish i=r := by simpa [TrailFamily.endpoint] using he (i,false)
    change U.quota v+(if T.finish i=v then 1 else 0)=_
    rw [hUs,hUf] at hb
    omega
  · have hUs : U.start i=r := by simpa [TrailFamily.endpoint] using he (i,true)
    have hUf : U.finish i=T.finish i := by simpa [TrailFamily.endpoint] using he (i,false)
    change U.quota v+(if T.start i=v then 1 else 0)=_
    rw [hUs,hUf] at hb
    omega

lemma regular_append_edge {V : Type*} {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (T : TrailFamily H k) (r : V) (A : Finset (Fin k))
    (R : RootedCut T r A) (hR : RegularCut R) (τ : Fin k × Bool)
    (h : G.Adj r (T.endpoint τ)) (hnew : s(r,T.endpoint τ) ∉ H.edgeSet)
    (hcover : G.edgeSet=insert s(r,T.endpoint τ) H.edgeSet) :
    ∃ U : TrailFamily G k, RegularlyRooted U r ∧
      ∀ v, U.quota v+(if T.endpoint τ=v then 1 else 0)=T.quota v+(if r=v then 1 else 0) := by
  classical
  let M := {s : Fin k × Bool // s.1 ∈ insert τ.1 A}
  let b : M := ⟨τ,Finset.mem_insert_self _ _⟩
  let c : M := ⟨(τ.1,!τ.2),Finset.mem_insert_self _ _⟩
  have hbc : b ≠ c := by
    intro hh
    have h' := congrArg (fun s : M ↦ s.val.2) hh
    change τ.2= !τ.2 at h'
    cases hbτ : τ.2 <;> simp [hbτ] at h'
  have hslot (s : M) (hs : s.val.1=τ.1) : s=b ∨ s=c := by
    have hh : s.val.2=τ.2 ∨ s.val.2= !τ.2 := by
      cases s.val.2 <;> cases τ.2 <;> simp
    exact hh.elim (fun ht ↦ Or.inl (Subtype.ext (Prod.ext hs ht)))
      (fun ht ↦ Or.inr (Subtype.ext (Prod.ext hs ht)))
  let J (s : M) : G.Subgraph := if hs : s.val.1 ∈ A then ((R.tail ⟨s.val,hs⟩).mapLe hHG).toSubgraph
    else if s=b then G.singletonSubgraph r else ((T.walk τ.1).mapLe hHG).toSubgraph
  have hJA (s : M) (hs : s.val.1 ∈ A) : J s=((R.tail ⟨s.val,hs⟩).mapLe hHG).toSubgraph := dif_pos hs
  have hJb (hj : τ.1 ∉ A) : J b=G.singletonSubgraph r := by simp [J,b,hj]
  have hJc (hj : τ.1 ∉ A) : J c=((T.walk τ.1).mapLe hHG).toSubgraph := by
    simp [J,c,hj,hbc.symm]
  have hJsub (s : M) : (J s).edgeSet ⊆ (T.walk s.val.1).toSubgraph.edgeSet := by
    by_cases hs : s.val.1 ∈ A
    · rw [hJA s hs]
      simpa [Walk.mapLe] using Subgraph.edgeSet_mono (R.tail_in_member ⟨s.val,hs⟩)
    · have hsj : s.val.1=τ.1 := (Finset.mem_insert.mp s.property).resolve_right hs
      have hj : τ.1 ∉ A := hsj ▸ hs
      rcases hslot s hsj with rfl|rfl
      · rw [hJb hj,edgeSet_singletonSubgraph]; exact Set.empty_subset _
      · change (J c).edgeSet ⊆ (T.walk τ.1).toSubgraph.edgeSet
        rw [hJc hj]; simp [Walk.mapLe]
  have hJD : Pairwise fun s t : M ↦ Disjoint (J s).edgeSet (J t).edgeSet := by
    intro s t hst
    by_cases hi : s.val.1=t.val.1
    · by_cases hs : s.val.1 ∈ A
      · have ht : t.val.1 ∈ A := hi ▸ hs
        rw [hJA s hs,hJA t ht]
        have hne : (⟨s.val,hs⟩ : {s : Fin k × Bool // s.1 ∈ A}) ≠ ⟨t.val,ht⟩ := by
          intro hh
          exact hst (Subtype.ext (congrArg (fun z : {s : Fin k × Bool // s.1 ∈ A} ↦ z.val) hh))
        simpa [Walk.mapLe] using R.disjoint hne
      · have hj : s.val.1=τ.1 := (Finset.mem_insert.mp s.property).resolve_right hs
        have hjA : τ.1 ∉ A := hj ▸ hs
        rcases hslot s hj with rfl|rfl
        · rw [hJb hjA,edgeSet_singletonSubgraph]; exact disjoint_bot_left
        · rcases hslot t (hi.symm.trans hj) with rfl|ht
          · rw [hJb hjA,edgeSet_singletonSubgraph]; exact disjoint_bot_right
          · exact (hst ht.symm).elim
    · exact (T.disjoint hi).mono (hJsub s) (hJsub t)
  have hJU (e : Sym2 V) : (∃ s : M, e ∈ (J s).edgeSet) ↔
      ∃ i ∈ insert τ.1 A, e ∈ (T.walk i).toSubgraph.edgeSet := by
    constructor
    · rintro ⟨s,hs⟩
      exact ⟨s.val.1,s.property,hJsub s hs⟩
    · rintro ⟨i,hi,hei⟩
      by_cases hiA : i ∈ A
      · rw [R.decomp i hiA,Subgraph.edgeSet_sup] at hei
        rcases hei with hei|hei
        · refine ⟨⟨(i,true),Finset.mem_insert_of_mem hiA⟩,?_⟩
          rw [hJA _ hiA]; simpa [Walk.mapLe] using hei
        · refine ⟨⟨(i,false),Finset.mem_insert_of_mem hiA⟩,?_⟩
          rw [hJA _ hiA]; simpa [Walk.mapLe] using hei
      · have hij := (Finset.mem_insert.mp hi).resolve_right hiA
        subst i
        refine ⟨c,?_⟩
        rw [hJc hiA]; simpa [Walk.mapLe] using hei
  let a : M := if τ.1 ∈ A then b else c
  let e := s(r,T.endpoint τ)
  let N (s : M) := if s=a then insert e (J s).edgeSet else (J s).edgeSet
  have hen (s : M) : e ∉ (J s).edgeSet := fun hh ↦ hnew
    ((T.walk s.val.1).toSubgraph.edgeSet_subset (hJsub s hh))
  have hND : Pairwise fun s t ↦ Disjoint (N s) (N t) := by
    intro s t hst
    by_cases hs : s=a
    · subst s
      simp only [N,if_pos rfl,if_neg hst.symm]
      exact Set.disjoint_insert_left.mpr ⟨hen t,hJD hst⟩
    · by_cases ht : t=a
      · subst t
        simp only [N,if_pos rfl,if_neg hs]
        exact Set.disjoint_insert_right.mpr ⟨hen s,hJD hst⟩
      · simpa only [N,if_neg hs,if_neg ht] using hJD hst
  have hNU (d : Sym2 V) : (∃ s, d ∈ N s) ↔ d=e ∨ ∃ s, d ∈ (J s).edgeSet := by
    constructor
    · rintro ⟨s,hs⟩
      by_cases hsa : s=a
      · simp only [N,if_pos hsa] at hs
        exact hs.elim Or.inl (fun hh ↦ Or.inr ⟨s,hh⟩)
      · exact Or.inr ⟨s,by simpa only [N,if_neg hsa] using hs⟩
    · rintro (rfl|⟨s,hs⟩)
      · exact ⟨a,by simp [N]⟩
      · exact ⟨s,by dsimp only [N]; split_ifs <;> simp_all⟩
  let α (s : Fin k × Bool) := if s=τ then r else T.endpoint s
  have hαb : α b.val=r := by simp [α,b]
  have hαout (s : M) (hs : s ≠ b) : α s.val=T.endpoint s.val :=
    if_neg (fun hh ↦ hs (Subtype.ext hh))
  have hdata (s : M) : ∃ q : G.Walk (α s.val) r,
      q.IsTrail ∧ RegularTail q ∧ q.toSubgraph.edgeSet=N s ∧
      (∀ hs : s.val.1 ∈ A, q.toSubgraph.verts=(R.tail ⟨s.val,hs⟩).toSubgraph.verts) ∧
      (s.val.1 ∉ A → q.toSubgraph.verts=
        if s=b then {r} else insert r (T.walk τ.1).toSubgraph.verts) := by
    by_cases hsA : s.val.1 ∈ A
    · let t := (R.tail ⟨s.val,hsA⟩).mapLe hHG
      have hte : t.toSubgraph=J s := (hJA s hsA).symm
      have htv : t.toSubgraph.verts=(R.tail ⟨s.val,hsA⟩).toSubgraph.verts := by simp [t,Walk.mapLe]
      by_cases hsb : s=b
      · subst s
        have htp : t.IsPath := by
          apply Walk.IsPath.mapLe
          exact (hR.1 ⟨τ,hsA⟩).resolve_right (fun hc ↦ h.ne hc.1.symm)
        have htn : e ∉ t.edges := fun hh ↦ hen b (hte ▸ t.mem_edges_toSubgraph.mpr hh)
        have hcycle : (Walk.cons h t).IsCycle := (Walk.cons_isCycle_iff t h).mpr ⟨htp,htn⟩
        let q := (Walk.cons h t).copy hαb.symm rfl
        have hqt : q.IsTrail := by simpa [q] using hcycle.isTrail
        have hqc : RegularTail q := by
          refine Or.inr ⟨hαb,?_⟩
          simpa only [q,NormalTrailSystem.walk_copy_subgraph,Walk.length_copy] using (closed_vertex_card_eq_iff_cycle (Walk.cons h t) hcycle.isTrail hcycle.not_nil).mpr hcycle
        refine ⟨q,hqt,hqc,?_,?_,fun hh ↦ (hh hsA).elim⟩
        · have hjA : τ.1 ∈ A := hsA
          have hba : b=a := by simp only [a,if_pos hjA]
          simp only [q,NormalTrailSystem.walk_copy_subgraph,N,if_pos hba]
          ext d
          simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,Set.mem_insert_iff,e]
          rw [←Walk.mem_edges_toSubgraph,hte]
        · intro _
          rw [NormalTrailSystem.walk_copy_subgraph,cons_into_root_verts h t,htv]
      · have hsa : s ≠ a := by
          by_cases hj : τ.1 ∈ A
          · simpa only [a,if_pos hj] using hsb
          · intro hh
            have hsc : s=c := by simpa only [a,if_neg hj] using hh
            exact hj (congrArg (fun s : M ↦ s.val.1) hsc ▸ hsA)
        let q := t.copy (hαout s hsb).symm rfl
        have hqt : q.IsTrail := by simpa [q,t] using (R.trail ⟨s.val,hsA⟩).mapLe hHG
        refine ⟨q,hqt,?_,?_,?_,fun hh ↦ (hh hsA).elim⟩
        · exact regularTail_of_subgraph_eq t q ((R.trail ⟨s.val,hsA⟩).mapLe hHG) hqt
            (regularTail_mapLe hHG _ (hR.1 _)) (NormalTrailSystem.walk_copy_subgraph _ _ _) (hαout s hsb)
        · rw [NormalTrailSystem.walk_copy_subgraph]
          simp only [N,if_neg hsa,hte]
        · intro _
          rw [NormalTrailSystem.walk_copy_subgraph,htv]
    · have hsj : s.val.1=τ.1 := (Finset.mem_insert.mp s.property).resolve_right hsA
      have hj : τ.1 ∉ A := hsj ▸ hsA
      rcases hslot s hsj with rfl|rfl
      · refine ⟨(Walk.nil : G.Walk r r).copy hαb.symm rfl,by simp,Or.inl (by simp),?_,
          fun hh ↦ (hj hh).elim,?_⟩
        · rw [NormalTrailSystem.walk_copy_subgraph]
          simp [N,a,hj,hbc,hJb hj]
        · intro _
          rw [NormalTrailSystem.walk_copy_subgraph,if_pos rfl]
          rfl
      · obtain ⟨P,hP,hPe⟩ := member_endpoint_path T τ (hR.2.2 τ.1 hj)
        let P' := P.mapLe hHG
        have hp' : P'.IsPath := hP.mapLe hHG
        have hP'e : P'.toSubgraph.edgeSet=(T.walk τ.1).toSubgraph.edgeSet := by
          simp [P',Walk.mapLe,hPe]
        have hP'v : P'.toSubgraph.verts=(T.walk τ.1).toSubgraph.verts := by
          simp [P',Walk.mapLe,hPe]
        have havoid : r ∉ P'.support := by
          rw [←Walk.mem_verts_toSubgraph,hP'v,Walk.mem_verts_toSubgraph]
          exact R.outside τ.1 hj
        let Q := (Walk.cons h P').reverse
        have hQ : Q.IsPath := ((Walk.cons_isPath_iff h P').mpr ⟨hp',havoid⟩).reverse
        have hαc : α c.val=T.endpoint (τ.1,!τ.2) := hαout c hbc.symm
        let q := Q.copy hαc.symm rfl
        refine ⟨q,by simpa [q] using hQ.isTrail,Or.inl (by simpa [q] using hQ),?_,
          fun hh ↦ (hj hh).elim,?_⟩
        · simp only [q,NormalTrailSystem.walk_copy_subgraph,Q,Walk.toSubgraph_reverse,
            N,a,if_neg hj,if_pos rfl,hJc hj]
          ext d
          simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,Set.mem_insert_iff,e]
          rw [←Walk.mem_edges_toSubgraph,hP'e]
          simp [Walk.mapLe]
        · intro _
          rw [NormalTrailSystem.walk_copy_subgraph,if_neg hbc.symm]
          change (Walk.cons h P').reverse.toSubgraph.verts=_
          rw [Walk.toSubgraph_reverse]
          ext z
          simp only [Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons,Set.mem_insert_iff]
          rw [←Walk.mem_verts_toSubgraph,hP'v]
          simp only [Walk.mem_verts_toSubgraph]
  choose q hqt hqr hqe hqv hqout using hdata
  have hfix (s : Fin k × Bool) (hs : s.1 ∉ insert τ.1 A) : α s=T.endpoint s := by
    apply if_neg
    intro hh
    exact hs (hh ▸ Finset.mem_insert_self _ _)
  have hcross (s : M) (i : Fin k) (hi : i ∉ insert τ.1 A) :
      Disjoint (q s).toSubgraph.edgeSet (T.walk i).toSubgraph.edgeSet := by
    rw [hqe]
    have hsi : s.val.1 ≠ i := fun hh ↦ hi (hh ▸ s.property)
    have hd := (T.disjoint hsi).mono_left (hJsub s)
    dsimp only [N]
    split_ifs
    · exact Set.disjoint_insert_left.mpr ⟨fun he ↦ hnew ((T.walk i).toSubgraph.edgeSet_subset he),hd⟩
    · exact hd
  have hcov (d : Sym2 V) : d ∈ G.edgeSet ↔
      (∃ s, d ∈ (q s).toSubgraph.edgeSet) ∨ ∃ i, i ∉ insert τ.1 A ∧ d ∈ (T.walk i).toSubgraph.edgeSet := by
    rw [hcover,Set.mem_insert_iff]
    simp only [hqe]
    rw [hNU,hJU]
    constructor
    · rintro (hd|hd)
      · exact Or.inl (Or.inl hd)
      · obtain ⟨i,hi⟩ := (T.cover d).mp hd
        by_cases hiA : i ∈ insert τ.1 A
        · exact Or.inl (Or.inr ⟨i,hiA,hi⟩)
        · exact Or.inr ⟨i,hiA,hi⟩
    · rintro ((hd|⟨i,_,hi⟩)|⟨i,_,hi⟩)
      · exact Or.inl hd
      · exact Or.inr ((T.cover d).mpr ⟨i,hi⟩)
      · exact Or.inr ((T.cover d).mpr ⟨i,hi⟩)
  obtain ⟨U,hUends,S,hSt,hSout⟩ := assemble_cut_graphs hHG T r (insert τ.1 A) α hfix q hqt
    (by intro s t hst; rw [hqe,hqe]; exact hND hst) hcross hcov
    (fun i hi ↦ R.outside i (fun hh ↦ hi (Finset.mem_insert_of_mem hh)))
  have hSr : RegularCut S := by
    refine ⟨?_,?_,?_⟩
    · intro s
      exact regularTail_of_subgraph_eq (q s) (S.tail s) (hqt s) (S.trail s)
        (hqr s) (hSt s) (hUends s.val)
    · intro i hi
      rw [hSt,hSt]
      by_cases hiA : i ∈ A
      · rw [hqv _ hiA,hqv _ hiA]
        exact hR.2.1 i hiA
      · have hij := (Finset.mem_insert.mp hi).resolve_right hiA
        subst i
        rw [hqout _ hiA,hqout _ hiA]
        have hb' : (⟨(τ.1,true),hi⟩ : M)=b ∨ (⟨(τ.1,false),hi⟩ : M)=b := by
          cases hτb : τ.2
          · exact Or.inr (Subtype.ext (Prod.ext rfl hτb.symm))
          · exact Or.inl (Subtype.ext (Prod.ext rfl hτb.symm))
        rcases hb' with hb'|hb'
        · rw [if_pos hb']; exact Set.inter_subset_left
        · rw [if_pos hb']; exact Set.inter_subset_right
    · intro i hi
      exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail i)
        ((hR.2.2 i (fun hh ↦ hi (Finset.mem_insert_of_mem hh))).mapLe hHG) (hSout i hi)
  exact ⟨U,⟨_,S,hSr⟩,quota_update_endpoint T U τ r hUends⟩

lemma regular_append_edge_positive {V : Type*} {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (T : TrailFamily H k) (r u : V) (hT : RegularlyRooted T r)
    (hu : 0 < T.quota u) (h : G.Adj r u) (hnew : s(r,u) ∉ H.edgeSet)
    (hcover : G.edgeSet=insert s(r,u) H.edgeSet) :
    ∃ U : TrailFamily G k, RegularlyRooted U r ∧
      ∀ v, U.quota v+(if u=v then 1 else 0)=T.quota v+(if r=v then 1 else 0) := by
  classical
  obtain ⟨A,R,hR⟩ := hT
  have hne : Nonempty {s : Fin k × Bool // T.endpoint s=u} :=
    Fintype.card_pos_iff.mp (by simpa only [TrailFamily.quota,Nat.card_eq_fintype_card] using hu)
  obtain ⟨⟨τ,hτ⟩⟩ := hne
  obtain ⟨U,hUr,hUq⟩ := regular_append_edge hHG T r A R hR τ
    (by rw [hτ]; exact h) (by rw [hτ]; exact hnew) (by rw [hτ]; exact hcover)
  exact ⟨U,hUr,by simpa only [hτ] using hUq⟩

end Erdos583RegularRootAppendDevelopment
