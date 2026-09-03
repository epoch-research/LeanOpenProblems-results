import Submission.RegularRootedCut
import Submission.AssembleRootedCut

/-! Edge transfer from a simple root petal to a root-avoiding outside path.
The surgery retains the regular-rooted-cut invariant. -/
namespace Erdos583RootedFlowerSurgeryDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583RegularRootedCutDevelopment Erdos583RegularTailRearrangementDevelopment
open Erdos583AssembleRootedCutDevelopment
open scoped Classical
set_option maxHeartbeats 2500000
set_option Elab.async false

lemma move_edge_sets {I E : Type*} [DecidableEq I] (S : I → Set E) (i j : I) (hij : i ≠ j)
    (e : E) (he : e ∈ S i) (hd : Pairwise fun s t ↦ Disjoint (S s) (S t)) :
    let N := fun s ↦ if s=i then S s \ {e} else if s=j then insert e (S s) else S s
    (Pairwise fun s t ↦ Disjoint (N s) (N t)) ∧
      ∀ d, (∃ s, d ∈ N s) ↔ ∃ s, d ∈ S s := by
  classical
  dsimp only
  let N := fun s ↦ if s=i then S s \ {e} else if s=j then insert e (S s) else S s
  change (Pairwise fun s t ↦ Disjoint (N s) (N t)) ∧
    ∀ d, (∃ s, d ∈ N s) ↔ ∃ s, d ∈ S s
  have hsub (s : I) (hs : s ≠ j) : N s ⊆ S s := by
    by_cases hsi : s=i
    · simp only [N,if_pos hsi]; exact Set.diff_subset
    · simp only [N,if_neg hsi,if_neg hs]; exact Set.Subset.rfl
  have hne (s : I) (hs : s ≠ j) : e ∉ N s := by
    by_cases hsi : s=i
    · simp [N,hsi]
    · intro hh
      exact Set.disjoint_left.mp (hd (Ne.symm hsi)) he (hsub s hs hh)
  have hj : N j=insert e (S j) := by simp [N,hij.symm]
  constructor
  · intro s t hst
    by_cases hs : s=j
    · subst s
      rw [hj]
      apply Set.disjoint_insert_left.mpr
      exact ⟨hne t hst.symm,(hd hst).mono_right (hsub t hst.symm)⟩
    · by_cases ht : t=j
      · subst t
        rw [hj]
        apply Set.disjoint_insert_right.mpr
        exact ⟨hne s hst,(hd hst).mono_left (hsub s hs)⟩
      · exact (hd hst).mono (hsub s hs) (hsub t ht)
  · intro d
    constructor
    · rintro ⟨s,hs⟩
      by_cases hsj : s=j
      · subst s; rw [hj] at hs
        rcases hs with rfl|hs
        · exact ⟨i,he⟩
        · exact ⟨j,hs⟩
      · exact ⟨s,hsub s hsj hs⟩
    · rintro ⟨s,hs⟩
      by_cases hde : d=e
      · subst d; exact ⟨j,by rw [hj]; exact Set.mem_insert _ _⟩
      · refine ⟨s,?_⟩
        by_cases hsi : s=i
        · simp only [N,if_pos hsi]
          exact ⟨hs,hde⟩
        · by_cases hsj : s=j
          · simp only [N,if_neg hsi,if_pos hsj]
            exact Or.inr hs
          · simpa only [N,if_neg hsi,if_neg hsj] using hs

lemma member_endpoint_path {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (s : Fin k × Bool) (hp : (T.walk s.1).IsPath) :
    ∃ p : G.Walk (T.endpoint s) (T.endpoint (s.1,!s.2)),
      p.IsPath ∧ p.toSubgraph=(T.walk s.1).toSubgraph := by
  rcases s with ⟨i,b⟩
  cases b
  · exact ⟨(T.walk i).reverse,hp.reverse,Walk.toSubgraph_reverse _⟩
  · exact ⟨T.walk i,hp,rfl⟩

lemma regular_improve_outside_rep {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (ρ : {s : Fin k × Bool // s.1 ∈ A})
    (hρ : T.endpoint ρ.val=r) (τ : Fin k × Bool) (hτ : τ.1 ∉ A)
    (h : G.Adj r (T.endpoint τ)) (p : G.Walk (T.endpoint τ) r)
    (hp : (Walk.cons h p).IsCycle)
    (he : (Walk.cons h p).toSubgraph=(R.tail ρ).toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score+1 ∧ (∀ v, U.quota v=T.quota v) ∧
      ∃ Q : RootedCut U r (insert τ.1 A), RegularCut Q := by
  classical
  let M := {s : Fin k × Bool // s.1 ∈ insert τ.1 A}
  let a : M := ⟨ρ.val,Finset.mem_insert_of_mem ρ.property⟩
  let b : M := ⟨τ,Finset.mem_insert_self _ _⟩
  let c : M := ⟨(τ.1,!τ.2),Finset.mem_insert_self _ _⟩
  have hab : a ≠ b := fun hh ↦ hτ (congrArg (fun s : M ↦ s.val.1) hh ▸ ρ.property)
  have hac : a ≠ c := fun hh ↦ hτ (congrArg (fun s : M ↦ s.val.1) hh ▸ ρ.property)
  have hbc : b ≠ c := by
    intro hh
    have h' := congrArg (fun s : M ↦ s.val.2) hh
    change τ.2= !τ.2 at h'
    cases hbτ : τ.2 <;> simp [hbτ] at h'
  have hbcv : τ ≠ (τ.1,!τ.2) := fun hh ↦ hbc (Subtype.ext hh)
  have habv : ρ.val ≠ τ := fun hh ↦ hab (Subtype.ext hh)
  have hacv : ρ.val ≠ (τ.1,!τ.2) := fun hh ↦ hac (Subtype.ext hh)
  have hslot (s : M) (hs : s.val.1=τ.1) : s=b ∨ s=c := by
    have hh : s.val.2=τ.2 ∨ s.val.2= !τ.2 := by
      cases s.val.2 <;> cases τ.2 <;> simp
    exact hh.elim (fun ht ↦ Or.inl (Subtype.ext (Prod.ext hs ht)))
      (fun ht ↦ Or.inr (Subtype.ext (Prod.ext hs ht)))
  have hmem (s : M) (hsb : s ≠ b) (hsc : s ≠ c) : s.val.1 ∈ A := by
    rcases Finset.mem_insert.mp s.property with hs|hs
    · exact ((hslot s hs).elim hsb hsc).elim
    · exact hs
  let H (s : M) : G.Subgraph := if hs : s.val.1 ∈ A then (R.tail ⟨s.val,hs⟩).toSubgraph
    else if s=b then G.singletonSubgraph r else (T.walk τ.1).toSubgraph
  have hHA (s : M) (hs : s.val.1 ∈ A) : H s=(R.tail ⟨s.val,hs⟩).toSubgraph := dif_pos hs
  have hHa : H a=(R.tail ρ).toSubgraph := hHA a ρ.property
  have hHb : H b=G.singletonSubgraph r := by simp [H,b,hτ]
  have hHc : H c=(T.walk τ.1).toSubgraph := by simp [H,c,hτ,hbc.symm]
  have hHEb : (H b).edgeSet=∅ := by rw [hHb,edgeSet_singletonSubgraph]
  have hHsub (s : M) : (H s).edgeSet ⊆ (T.walk s.val.1).toSubgraph.edgeSet := by
    by_cases hs : s.val.1 ∈ A
    · rw [hHA s hs]
      exact Subgraph.edgeSet_mono (R.tail_in_member ⟨s.val,hs⟩)
    · have hsj : s.val.1=τ.1 := (Finset.mem_insert.mp s.property).resolve_right hs
      rcases hslot s hsj with rfl|rfl
      · rw [hHEb]; exact Set.empty_subset _
      · simpa only [hHc] using (Set.Subset.rfl :
          (T.walk τ.1).toSubgraph.edgeSet ⊆ (T.walk τ.1).toSubgraph.edgeSet)
  have hHD : Pairwise fun s t : M ↦ Disjoint (H s).edgeSet (H t).edgeSet := by
    intro s t hst
    by_cases hi : s.val.1=t.val.1
    · by_cases hs : s.val.1 ∈ A
      · have ht : t.val.1 ∈ A := hi ▸ hs
        rw [hHA s hs,hHA t ht]
        exact R.disjoint (fun hh ↦ hst (Subtype.ext
          (congrArg (fun z : {s : Fin k × Bool // s.1 ∈ A} ↦ z.val) hh)))
      · have hj : s.val.1=τ.1 := (Finset.mem_insert.mp s.property).resolve_right hs
        rcases hslot s hj with rfl|rfl
        · rw [hHEb]; exact disjoint_bot_left
        · rcases hslot t (hi.symm.trans hj) with rfl|ht
          · rw [hHEb]; exact disjoint_bot_right
          · exact (hst ht.symm).elim
    · exact (T.disjoint hi).mono (hHsub s) (hHsub t)
  have hHU (e : Sym2 V) : (∃ s : M, e ∈ (H s).edgeSet) ↔
      ∃ i ∈ insert τ.1 A, e ∈ (T.walk i).toSubgraph.edgeSet := by
    constructor
    · rintro ⟨s,hs⟩
      exact ⟨s.val.1,s.property,hHsub s hs⟩
    · rintro ⟨i,hi,hei⟩
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact ⟨c,by rw [hHc]; exact hei⟩
      · rw [R.decomp i hi,Subgraph.edgeSet_sup] at hei
        rcases hei with hei|hei
        · exact ⟨⟨(i,true),Finset.mem_insert_of_mem hi⟩,by rw [hHA _ hi]; exact hei⟩
        · exact ⟨⟨(i,false),Finset.mem_insert_of_mem hi⟩,by rw [hHA _ hi]; exact hei⟩
  let e := s(r,T.endpoint τ)
  have hea : e ∈ (H a).edgeSet := by
    rw [hHa,←he]
    change s(r,T.endpoint τ) ∈ (Walk.cons h p).toSubgraph.edgeSet
    simpa only [Walk.snd_cons] using (Walk.cons h p).toSubgraph_adj_snd (by simp)
  let N (s : M) := if s=a then (H s).edgeSet \ {e}
    else if s=c then insert e (H s).edgeSet else (H s).edgeSet
  obtain ⟨hND,hNU⟩ := move_edge_sets (fun s : M ↦ (H s).edgeSet) a c hac e hea hHD
  have hND' : Pairwise (fun s t ↦ Disjoint (N s) (N t)) := by simpa only [N] using hND
  have hNU' : ∀ d, (∃ s, d ∈ N s) ↔ ∃ s, d ∈ (H s).edgeSet := by simpa only [N] using hNU
  let σ := Equiv.swap ρ.val τ
  have hσa : σ a.val=τ := Equiv.swap_apply_left _ _
  have hσb : σ b.val=ρ.val := Equiv.swap_apply_right _ _
  have hσc : σ c.val=c.val := Equiv.swap_apply_of_ne_of_ne hacv.symm hbcv.symm
  have hσout (s : M) (hsa : s ≠ a) (hsb : s ≠ b) : σ s.val=s.val :=
    Equiv.swap_apply_of_ne_of_ne (fun hh ↦ hsa (Subtype.ext hh))
      (fun hh ↦ hsb (Subtype.ext hh))
  obtain ⟨P,hP,hPe⟩ := member_endpoint_path T τ (hR.2.2 τ.1 hτ)
  have hPa : r ∉ P.support := by
    rw [←Walk.mem_verts_toSubgraph,hPe,Walk.mem_verts_toSubgraph]
    exact R.outside τ.1 hτ
  let Q := (Walk.cons h P).reverse
  have hQ : Q.IsPath := ((Walk.cons_isPath_iff h P).mpr ⟨hP,hPa⟩).reverse
  have hQe : Q.toSubgraph.edgeSet=insert e (T.walk τ.1).toSubgraph.edgeSet := by
    rw [←hPe]
    ext d
    simp only [Q,Walk.toSubgraph_reverse,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,
      Set.mem_insert_iff,e]
  have hQv : Q.toSubgraph.verts=insert r (T.walk τ.1).toSubgraph.verts := by
    rw [←hPe]
    ext z
    simp only [Q,Walk.toSubgraph_reverse,Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons,
      Set.mem_insert_iff]
  have hpP := (Walk.cons_isCycle_iff p h).mp hp |>.1
  have hpe : p.toSubgraph.edgeSet=(H a).edgeSet \ {e} := by
    rw [hHa,←he]
    ext d
    have hn := (Walk.cons_isCycle_iff p h).mp hp |>.2
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,
      Set.mem_diff,Set.mem_singleton_iff,e]
    constructor
    · intro hd
      exact ⟨Or.inr hd,fun hh ↦ hn (hh ▸ hd)⟩
    · rintro ⟨hd,hne⟩
      exact hd.resolve_left hne
  have hpv : p.toSubgraph.verts=(H a).verts := by
    rw [hHa,←he]
    exact (cons_into_root_verts h p).symm
  have hdata (s : M) : ∃ q : G.Walk (T.endpoint (σ s.val)) r,
      q.IsTrail ∧ RegularTail q ∧ q.toSubgraph.edgeSet=N s ∧
      q.toSubgraph.verts=(if s=c then insert r (H s).verts else (H s).verts) := by
    by_cases hsa : s=a
    · subst s
      have ha : T.endpoint τ=T.endpoint (σ a.val) := by rw [hσa]
      refine ⟨p.copy ha rfl,by simpa using hpP.isTrail,Or.inl (by simpa using hpP),?_,?_⟩
      · rw [NormalTrailSystem.walk_copy_subgraph]
        simpa only [N,if_pos rfl] using hpe
      · rw [NormalTrailSystem.walk_copy_subgraph,if_neg hac]
        exact hpv
    · by_cases hsb : s=b
      · subst s
        have hb : r=T.endpoint (σ b.val) := by rw [hσb,hρ]
        refine ⟨(Walk.nil : G.Walk r r).copy hb rfl,by simp,Or.inl (by simp),?_,?_⟩
        · rw [NormalTrailSystem.walk_copy_subgraph]
          simp [N,hab.symm,hbc,hHEb]
        · rw [NormalTrailSystem.walk_copy_subgraph,if_neg hbc,hHb]
          rfl
      · by_cases hsc : s=c
        · subst s
          have hc : T.endpoint (τ.1,!τ.2)=T.endpoint (σ c.val) := by rw [hσc]
          refine ⟨Q.copy hc rfl,by simpa using hQ.isTrail,Or.inl (by simpa using hQ),?_,?_⟩
          · rw [NormalTrailSystem.walk_copy_subgraph]
            simpa only [N,if_neg hac.symm,if_pos rfl,hHc] using hQe
          · rw [NormalTrailSystem.walk_copy_subgraph,if_pos rfl,hHc]
            exact hQv
        · have hsA := hmem s hsb hsc
          let t := R.tail ⟨s.val,hsA⟩
          have hs : T.endpoint s.val=T.endpoint (σ s.val) := by rw [hσout s hsa hsb]
          refine ⟨t.copy hs rfl,by simpa [t] using R.trail ⟨s.val,hsA⟩,?_,?_,?_⟩
          · apply regularTail_of_subgraph_eq t _ (R.trail _) (by simpa [t] using R.trail ⟨s.val,hsA⟩)
              (hR.1 ⟨s.val,hsA⟩) (NormalTrailSystem.walk_copy_subgraph _ _ _) hs.symm
          · rw [NormalTrailSystem.walk_copy_subgraph]
            simp only [N,if_neg hsa,if_neg hsc,hHA s hsA,t]
          · rw [NormalTrailSystem.walk_copy_subgraph,if_neg hsc,hHA s hsA]
  choose q hqt hqr hqe hqv using hdata
  have hfix (s : Fin k × Bool) (hs : s.1 ∉ insert τ.1 A) : σ s=s := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hh
      exact hs (hh ▸ Finset.mem_insert_of_mem ρ.property)
    · intro hh
      exact hs (hh ▸ Finset.mem_insert_self _ _)
  obtain ⟨U,hUq,hUends,S,hSt,hSout⟩ := assemble_cut T r (insert τ.1 A) σ hfix q hqt
    (by intro s t hst; rw [hqe,hqe]; exact hND' hst)
    (by intro d; simp only [hqe]; exact (hNU' d).trans (hHU d))
    (fun i hi ↦ R.outside i (fun hh ↦ hi (Finset.mem_insert_of_mem hh)))
  have hSv (s : M) : (S.tail s).toSubgraph.verts=
      (if s=c then insert r (H s).verts else (H s).verts) := by rw [hSt,hqv]
  have hSA (s : M) (hs : s.val.1 ∈ A) :
      (S.tail s).toSubgraph.verts=(R.tail ⟨s.val,hs⟩).toSubgraph.verts := by
    have hsc : s ≠ c := fun hh ↦ hτ (congrArg (fun s : M ↦ s.val.1) hh ▸ hs)
    rw [hSv,if_neg hsc,hHA s hs]
  have hSb : (S.tail b).toSubgraph.verts={r} := by rw [hSv,if_neg hbc,hHb]; rfl
  have hSc : (S.tail c).toSubgraph.verts=insert r (T.walk τ.1).toSubgraph.verts := by
    rw [hSv,if_pos rfl,hHc]
  have hUi (i : Fin k) (hij : i ≠ τ.1) :
      (U.walk i).toSubgraph.verts=(T.walk i).toSubgraph.verts := by
    by_cases hi : i ∈ A
    · rw [S.decomp i (Finset.mem_insert_of_mem hi),R.decomp i hi]
      change (S.tail _).toSubgraph.verts ∪ (S.tail _).toSubgraph.verts = _
      rw [hSA _ hi,hSA _ hi]
      rfl
    · rw [hSout i (by simp [hi,hij])]
  have hUj : (U.walk τ.1).toSubgraph.verts=insert r (T.walk τ.1).toSubgraph.verts := by
    rw [S.decomp τ.1 (Finset.mem_insert_self _ _)]
    change (S.tail _).toSubgraph.verts ∪ (S.tail _).toSubgraph.verts = _
    cases hb' : τ.2
    · have hs1 : (⟨(τ.1,true),Finset.mem_insert_self _ _⟩ : M)=c := by
        apply Subtype.ext; simp [c,hb']
      have hs2 : (⟨(τ.1,false),Finset.mem_insert_self _ _⟩ : M)=b := by
        apply Subtype.ext; exact Prod.ext rfl hb'.symm
      rw [hs1,hs2,hSc,hSb]
      exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    · have hs1 : (⟨(τ.1,true),Finset.mem_insert_self _ _⟩ : M)=b := by
        apply Subtype.ext; exact Prod.ext rfl hb'.symm
      have hs2 : (⟨(τ.1,false),Finset.mem_insert_self _ _⟩ : M)=c := by
        apply Subtype.ext; simp [c,hb']
      rw [hs1,hs2,hSb,hSc]
      exact Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hscore : U.score=T.score+1 := by
    have hv (i : Fin k) : (U.walk i).toSubgraph.verts.ncard=
        (T.walk i).toSubgraph.verts.ncard+(if i=τ.1 then 1 else 0) := by
      by_cases hi : i=τ.1
      · subst i
        rw [hUj,Set.ncard_insert_of_notMem]
        · simp
        · simpa only [Walk.mem_verts_toSubgraph] using R.outside τ.1 hτ
      · rw [hUi i hi,if_neg hi,Nat.add_zero]
    unfold TrailFamily.score
    simp_rw [hv]
    rw [Finset.sum_add_distrib]
    simp
  refine ⟨U,hscore,hUq,S,?_,?_,?_⟩
  · intro s
    exact regularTail_of_subgraph_eq (q s) (S.tail s) (hqt s) (S.trail s)
      (hqr s) (hSt s) (hUends s.val)
  · intro i hi
    by_cases hij : i=τ.1
    · subst i
      have hl := hslot (⟨(τ.1,true),hi⟩ : M) rfl
      have hr := hslot (⟨(τ.1,false),hi⟩ : M) rfl
      rcases hl with hl|hl <;> rcases hr with hr|hr
      · rw [hl,hSb]; exact Set.inter_subset_left
      · rw [hl,hSb]; exact Set.inter_subset_left
      · rw [hr,hSb]; exact Set.inter_subset_right
      · have hh : (⟨(τ.1,true),hi⟩ : M)=(⟨(τ.1,false),hi⟩ : M) := hl.trans hr.symm
        have := congrArg (fun s : M ↦ s.val.2) hh
        contradiction
    · have hiA := (Finset.mem_insert.mp hi).resolve_left hij
      rw [hSA _ hiA,hSA _ hiA]
      exact hR.2.1 i hiA
  · intro i hi
    exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail i)
      (hR.2.2 i (fun hh ↦ hi (Finset.mem_insert_of_mem hh))) (hSout i hi)

lemma regular_improve_outside {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (ρ : {s : Fin k × Bool // s.1 ∈ A})
    (hρ : T.endpoint ρ.val=r) (τ : Fin k × Bool) (hτ : τ.1 ∉ A)
    (hx : (R.tail ρ).toSubgraph.Adj r (T.endpoint τ)) :
    ∃ U : TrailFamily G k, U.score=T.score+1 ∧ (∀ v, U.quota v=T.quota v) ∧
      ∃ Q : RootedCut U r (insert τ.1 A), RegularCut Q := by
  let C := (R.tail ρ).copy hρ rfl
  have hC : C.IsTrail := by simpa only [C,Walk.isTrail_copy] using R.trail ρ
  have hCe : C.toSubgraph=(R.tail ρ).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hCr : RegularTail C := regularTail_of_subgraph_eq (R.tail ρ) C (R.trail ρ) hC
    (hR.1 ρ) hCe hρ.symm
  have hxC : C.toSubgraph.Adj r (T.endpoint τ) := by rw [hCe]; exact hx
  have hCn : ¬C.Nil := by
    intro hn
    have hh := C.mem_edges_toSubgraph.mp (show s(r,T.endpoint τ) ∈ C.toSubgraph.edgeSet from hxC)
    simp only [hn.eq_nil,Walk.edges_nil,List.not_mem_nil] at hh
  have hc := regularTail_cycle C hC hCn hCr
  obtain ⟨D,hD,hDe,hDn,hDz⟩ := MultipleEscape.closed_trail_first_at_neighbor C hC hxC
  have hDr : RegularTail D := regularTail_of_subgraph_eq C D hC hD hCr hDe rfl
  have hDc := regularTail_cycle D hD hDn hDr
  cases hform : D with
  | nil => exact (hDn (hform ▸ Walk.Nil.nil)).elim
  | @cons _ z _ h p =>
    have hz : z=T.endpoint τ := by simpa only [hform,Walk.snd_cons] using hDz
    subst z
    apply regular_improve_outside_rep R hR ρ hρ τ hτ h p (hform ▸ hDc)
    rw [←hform,hDe,hCe]

end Erdos583RootedFlowerSurgeryDevelopment
