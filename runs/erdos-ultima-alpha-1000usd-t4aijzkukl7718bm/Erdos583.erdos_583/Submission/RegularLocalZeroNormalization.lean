import Submission.RegularSparseZeroNormalization

/-! Local zero-neighbor bounds for regular rooted optimization.
These do not settle the unrestricted path-decomposition conjecture. -/
namespace Erdos583RegularLocalZeroNormalizationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583RegularRootedCutDevelopment Erdos583RegularCutDefectsDevelopment
open Erdos583RegularFlowerExposuresDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma max_regular_local_petals_bound {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    {G : SimpleGraph V} {k : ℕ} {T : TrailFamily G k} {r : V} {A : Finset (Fin k)}
    (R : RootedCut T r A) (hR : RegularCut R)
    (hm : ∀ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) →
      RegularlyRooted U r → U.score ≤ T.score)
    (ρ : I ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hr : ∀ i, T.endpoint (ρ i).val=r) (hn : ∀ i, ¬(R.tail (ρ i)).Nil) :
    2*Fintype.card I ≤ {z | G.Adj r z ∧ T.quota z=0}.ncard := by
  obtain ⟨B,E,hEc,hE⟩ := regular_parallel_exposures R hR ρ hr hn
  have hsub : (E : Set V) ⊆ {z | G.Adj r z ∧ T.quota z=0} := by
    intro z hz
    obtain ⟨hzB,hEz⟩ := hE z hz
    have hz0 := regular_exposure_zero_at_max hm hzB hEz
    obtain ⟨U,_,_,Q,_,_,σ,_,hAdj⟩ := hEz
    exact ⟨(Q.tail σ).toSubgraph.adj_sub hAdj,hz0⟩
  have hh := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset,hEc] at hh
  exact hh

/-- Zero labels elsewhere in the graph are irrelevant to this fixed-quota
normalization criterion. -/
lemma normalize_regular_one_zero_neighbor {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hT : RegularlyRooted T r)
    (hz : {z | G.Adj r z ∧ T.quota z=0}.ncard ≤ 1) :
    ∃ P : TrailFamily G k, (∀ v, P.quota v=T.quota v) ∧
      ∀ i, (P.walk i).IsPath := by
  classical
  obtain ⟨U,hUq,⟨A,R,hR⟩,hm⟩ := exists_max_regular_score T r hT
  have hmU : ∀ S : TrailFamily G k, (∀ v, S.quota v=U.quota v) →
      RegularlyRooted S r → S.score ≤ U.score := by
    intro S hSq hSr
    exact hm S (fun v ↦ (hSq v).trans (hUq v)) hSr
  refine ⟨U,hUq,regularCut_all_paths R hR ?_⟩
  intro s
  by_contra hs
  let I := {s : {s : Fin k × Bool // s.1 ∈ A} // ¬(R.tail s).IsPath}
  letI : Nonempty I := ⟨⟨s,hs⟩⟩
  let ρ : I ↪ {s : Fin k × Bool // s.1 ∈ A} := Function.Embedding.subtype _
  have hb := max_regular_local_petals_bound R hR hmU ρ
    (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).1)
    (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).2)
  have hzU : {z | G.Adj r z ∧ U.quota z=0}.ncard ≤ 1 := by
    simpa only [hUq] using hz
  have hp : 0 < Fintype.card I := Fintype.card_pos
  omega

lemma max_regular_three_zero_neighbors_deficit {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} {T : TrailFamily G k} {r : V} {A : Finset (Fin k)}
    (R : RootedCut T r A) (hR : RegularCut R)
    (hm : ∀ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) →
      RegularlyRooted U r → U.score ≤ T.score)
    (hz : {z | G.Adj r z ∧ T.quota z=0}.ncard ≤ 3) :
    G.edgeSet.ncard+k ≤ T.score+1 := by
  classical
  by_cases hp : ∀ s, (R.tail s).IsPath
  · have hh := T.score_eq_edges_add_iff.mpr (regularCut_all_paths R hR hp)
    omega
  · obtain ⟨s,hs⟩ := not_forall.mp hp
    let I := {s : {s : Fin k × Bool // s.1 ∈ A} // ¬(R.tail s).IsPath}
    letI : Nonempty I := ⟨⟨s,hs⟩⟩
    let ρ : I ↪ {s : Fin k × Bool // s.1 ∈ A} := Function.Embedding.subtype _
    have hb := max_regular_local_petals_bound R hR hm ρ
      (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).1)
      (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).2)
    have hc : Fintype.card I ≤ 1 := by omega
    have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hc
    apply regularCut_one_petal_bound R hR s
    intro t hts
    by_contra ht
    exact hts (congrArg Subtype.val (hsub.elim (⟨t,ht⟩ : I) ⟨s,hs⟩))

lemma normalize_regular_local_zero_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hT : RegularlyRooted T r)
    (hz : {z | G.Adj r z ∧ T.quota z=0}.ncard ≤ 3)
    (hq : 2 ≤ T.quota r)
    (hf : (G.induce {v | (if v=r then T.quota v-2 else T.quota v)=0}).IsAcyclic) :
    ∃ P : TrailFamily G k, ∀ i, (P.walk i).IsPath := by
  classical
  obtain ⟨U,hUq,⟨A,R,hR⟩,hm⟩ := exists_max_regular_score T r hT
  have hmU : ∀ S : TrailFamily G k, (∀ v, S.quota v=U.quota v) →
      RegularlyRooted S r → S.score ≤ U.score := by
    intro S hSq hSr
    exact hm S (fun v ↦ (hSq v).trans (hUq v)) hSr
  have hzU : {z | G.Adj r z ∧ U.quota z=0}.ncard ≤ 3 := by
    simpa only [hUq] using hz
  have hb := max_regular_three_zero_neighbors_deficit R hR hmU hzU
  by_cases hp : ∀ i, (U.walk i).IsPath
  · exact ⟨U,hp⟩
  have hs : U.score+1=G.edgeSet.ncard+k := by
    have hle := U.score_le_edges_add
    have hne := U.score_eq_edges_add_iff.not.mpr hp
    omega
  have htail : ∃ s, ¬(R.tail s).IsPath := by
    by_contra hn
    push_neg at hn
    exact hp (regularCut_all_paths R hR hn)
  obtain ⟨s,hsp⟩ := htail
  obtain ⟨hroot,hn⟩ := regularCut_nonpath_root R hR s hsp
  let c (v : V) := if v=r then T.quota v-2 else T.quota v
  have hquota (v : V) : U.quota v=c v+2*(if r=v then 1 else 0) := by
    rw [hUq]
    by_cases hv : v=r
    · subst v
      simpa [c] using (Nat.sub_add_cancel hq).symm
    · simp [c,hv,Ne.symm hv]
  obtain ⟨_,P,_,hP⟩ := ForestZeroNormalization.normalize_one_defect_forest
    U c r hs hquota ⟨A,R,s,hroot,hn⟩ hf
  exact ⟨P,hP⟩

end Erdos583RegularLocalZeroNormalizationDevelopment
