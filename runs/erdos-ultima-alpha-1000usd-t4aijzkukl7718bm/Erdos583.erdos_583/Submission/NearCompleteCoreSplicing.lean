import Submission.CorePairSplicing
import Submission.SplitPortSets

/-! Splicing compatible arms through a near-complete even core with one
fresh endpoint pair. Only arms originally paired together need be disjoint. -/
namespace Erdos583NearCompleteCoreSplicingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583NearCompleteCorePortsDevelopment Erdos583CorePairSplicingDevelopment
open Erdos583SplitPortSetsDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma splice_near_complete_fresh_pair {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {t : ℕ} (a b : Fin t → S) (u v : S) (huv : u ≠ v) (j : Fin t)
    (hH : G.induce S=(⊤ : SimpleGraph S).deleteEdges {s(u,v)})
    (he : Function.Bijective (Sum.elim
      (fun z : Fin t × Bool ↦ if z.2 then a z.1 else b z.1)
      (fun z : Bool ↦ if z then u else v)))
    (x y : Fin t → V)
    (A : ∀ i, G.Walk (x i) (a i).val) (B : ∀ i, G.Walk (b i).val (y i))
    (hAp : ∀ i, (A i).IsPath) (hBp : ∀ i, (B i).IsPath)
    (hA : ∀ i, ∀ w ∈ (A i).support, w ∈ S → w=(a i).val)
    (hB : ∀ i, ∀ w ∈ (B i).support, w ∈ S → w=(b i).val)
    (hAB : ∀ i, ∀ w ∈ (A i).support, w ∈ (B i).support → False)
    (hdis : Pairwise (fun z w : Fin t × Bool ↦
      Disjoint (if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet)
        (if w.2 then (A w.1).toSubgraph.edgeSet else (B w.1).toSubgraph.edgeSet)))
    (hcover : (BridgeGlue.within G S).edgeSet ∪
      (⋃ i, (A i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet)=G.edgeSet) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  have hfresh (i : Fin t) : (a i).val ≠ v.val ∧ (b i).val ≠ v.val := by
    constructor
    · intro hh
      have heq : a i=v := Subtype.ext hh
      have hx := he.injective (a₁ := Sum.inl (i,true)) (a₂ := Sum.inr false) heq
      cases hx
    · intro hh
      have heq : b i=v := Subtype.ext hh
      have hx := he.injective (a₁ := Sum.inl (i,false)) (a₂ := Sum.inr false) heq
      cases hx
  have hex := near_complete_extended_pairs a b u v huv j he
  rw [←hH] at hex
  obtain ⟨q,hq,hqd,hqc⟩ := hex
  obtain ⟨Q,hQ,hQS,hQQ,hQc⟩ := map_induced_partition S
    (splitStart v a) (splitFinish v b j) q hq hqd hqc
  let X : Fin (t+1) → V := Fin.cases v.val x
  let Y : Fin (t+1) → V := Fin.cases (y j) (fun i ↦ if i=j then v.val else y i)
  have hAX (i : Fin (t+1)) : ∃ P : G.Walk (X i) (splitStart v a i).val,
      P.IsPath ∧ P.support=Fin.cases (motive := fun _ ↦ List V) [v.val] (fun l ↦ (A l).support) i ∧
      P.toSubgraph.edgeSet=Fin.cases (motive := fun _ ↦ Set (Sym2 V)) ∅ (fun l ↦ (A l).toSubgraph.edgeSet) i := by
    induction i using Fin.cases with
    | zero => exact ⟨Walk.nil,Walk.IsPath.nil,rfl,by simp⟩
    | succ i => exact ⟨A i,hAp i,rfl,rfl⟩
  have hBY (i : Fin (t+1)) : ∃ P : G.Walk (splitFinish v b j i).val (Y i),
      P.IsPath ∧ P.support=Fin.cases (motive := fun _ ↦ List V) (B j).support
        (fun l ↦ if l=j then [v.val] else (B l).support) i ∧
      P.toSubgraph.edgeSet=Fin.cases (motive := fun _ ↦ Set (Sym2 V)) (B j).toSubgraph.edgeSet
        (fun l ↦ if l=j then ∅ else (B l).toSubgraph.edgeSet) i := by
    induction i using Fin.cases with
    | zero => exact ⟨B j,hBp j,rfl,rfl⟩
    | succ i =>
      by_cases hij : i=j
      · let P : G.Walk (splitFinish v b j i.succ).val (Y i.succ) :=
          (Walk.nil : G.Walk v.val v.val).copy (by simp [splitFinish,hij]) (by simp [Y,hij])
        refine ⟨P,?_,?_,?_⟩
        · simp only [P,Walk.isPath_copy]; exact Walk.IsPath.nil
        · simp only [P,Walk.support_copy,Walk.support_nil,Fin.cases_succ,if_pos hij]
        · simp only [P,NormalTrailSystem.walk_copy_subgraph,Fin.cases_succ,if_pos hij]
          simp
      · let P : G.Walk (splitFinish v b j i.succ).val (Y i.succ) :=
          (B i).copy (by simp [splitFinish,hij]) (by simp [Y,hij])
        refine ⟨P,?_,?_,?_⟩
        · simpa only [P,Walk.isPath_copy] using hBp i
        · simp only [P,Walk.support_copy,Fin.cases_succ,if_neg hij]
        · simp only [P,NormalTrailSystem.walk_copy_subgraph,Fin.cases_succ,if_neg hij]
  choose AA hAAp hAAs hAAe using hAX
  choose BB hBBp hBBs hBBe using hBY
  have hAA (i : Fin (t+1)) : ∀ w ∈ (AA i).support, w ∈ S → w=(splitStart v a i).val := by
    intro w hw hwS
    rw [hAAs] at hw
    induction i using Fin.cases with
    | zero => exact List.mem_singleton.mp hw
    | succ i => exact hA i w hw hwS
  have hBB (i : Fin (t+1)) : ∀ w ∈ (BB i).support, w ∈ S → w=(splitFinish v b j i).val := by
    intro w hw hwS
    rw [hBBs] at hw
    induction i using Fin.cases with
    | zero => exact hB j w hw hwS
    | succ i =>
      by_cases hij : i=j
      · simp only [Fin.cases_succ,if_pos hij] at hw
        simpa only [splitFinish,Fin.cases_succ,if_pos hij] using List.mem_singleton.mp hw
      · simp only [Fin.cases_succ,if_neg hij] at hw
        simpa only [splitFinish,Fin.cases_succ,if_neg hij] using hB i w hw hwS
  have hAABB (i : Fin (t+1)) : ∀ w ∈ (AA i).support, w ∈ (BB i).support → False := by
    intro w hwA hwB
    rw [hAAs] at hwA
    rw [hBBs] at hwB
    induction i using Fin.cases with
    | zero =>
      have hw : w=v.val := List.mem_singleton.mp hwA
      subst w
      exact (hfresh j).2 (hB j v.val hwB v.property).symm
    | succ i =>
      by_cases hij : i=j
      · simp only [Fin.cases_succ,if_pos hij] at hwB
        have hw : w=v.val := List.mem_singleton.mp hwB
        subst w
        exact (hfresh i).1 (hA i v.val hwA v.property).symm
      · simp only [Fin.cases_succ,if_neg hij] at hwB
        exact hAB i w hwA hwB
  have hnewdis : Pairwise (fun z w : Fin (t+1) × Bool ↦
      Disjoint (if z.2 then (AA z.1).toSubgraph.edgeSet else (BB z.1).toSubgraph.edgeSet)
        (if w.2 then (AA w.1).toSubgraph.edgeSet else (BB w.1).toSubgraph.edgeSet)) := by
    simpa only [hAAe,hBBe] using split_port_sets_pairwise
      (fun i ↦ (A i).toSubgraph.edgeSet) (fun i ↦ (B i).toSubgraph.edgeSet) j hdis
  have hnewcover : (BridgeGlue.within G S).edgeSet ∪
      (⋃ i, (AA i).toSubgraph.edgeSet ∪ (BB i).toSubgraph.edgeSet)=G.edgeSet := by
    have houter : (⋃ i, (AA i).toSubgraph.edgeSet ∪ (BB i).toSubgraph.edgeSet)=
        ⋃ i, (A i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet := by
      simp_rw [hAAe,hBBe]
      exact split_port_sets_union (fun i ↦ (A i).toSubgraph.edgeSet)
        (fun i ↦ (B i).toSubgraph.edgeSet) j
    rw [houter]
    exact hcover
  obtain ⟨P,hP,hPd,hPc⟩ := splice_given_core_pairs S (splitStart v a) (splitFinish v b j)
    X Y AA BB Q hQ hQS hQQ hQc hAAp hBBp hAA hBB hAABB hnewdis hnewcover
  let U : TrailFamily G (t+1) :=
    { start := X
      finish := Y
      walk := P
      isTrail := fun i ↦ (hP i).isTrail
      disjoint := hPd
      cover := fun e ↦ by rw [←hPc]; exact Set.mem_iUnion }
  exact MatchingAppend.path_family_partition U hP

end Erdos583NearCompleteCoreSplicingDevelopment
