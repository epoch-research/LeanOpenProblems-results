import Submission.RootedFlowerSurgery
import Submission.ParallelRootExposures
import Submission.RegularCutDefects

/-! Common-successor exposures for regular root petals, together with the
score-maximality obstruction at positive-quota exits. -/
namespace Erdos583RegularFlowerExposuresDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583RegularRootedCutDevelopment Erdos583RegularTailRearrangementDevelopment
open Erdos583ParallelRootExposuresDevelopment Erdos583RootedFlowerSurgeryDevelopment
open Erdos583RegularCutDefectsDevelopment
open scoped Classical
set_option maxHeartbeats 2500000
set_option Elab.async false

def RegularExposure {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (A : Finset (Fin k)) (B : Finset V) (z : V) : Prop :=
  ∃ U : TrailFamily G k, U.score=T.score ∧ (∀ v, U.quota v=T.quota v) ∧
    ∃ Q : RootedCut U r A, RegularCut Q ∧
      (∀ x, x ∈ B ↔ ∃ s : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint s.val=x) ∧
      ∃ ρ : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint ρ.val=r ∧
        (Q.tail ρ).toSubgraph.Adj r z

lemma regular_parallel_exposures {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    {G : SimpleGraph V} {k : ℕ} {T : TrailFamily G k} {r : V} {A : Finset (Fin k)}
    (R : RootedCut T r A) (hR : RegularCut R)
    (ρ : I ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hr : ∀ i, T.endpoint (ρ i).val=r) (hn : ∀ i, ¬(R.tail (ρ i)).Nil) :
    ∃ B E : Finset V, E.card=2*Fintype.card I ∧
      ∀ z ∈ E, z ∉ B ∧ RegularExposure T r A B z := by
  classical
  let i₀ : I := Classical.choice ‹Nonempty I›
  obtain ⟨B,hrB,ι₀,hlabel₀,hι₀,hB⟩ := R.select_labels (ρ i₀) (hr i₀)
  let j (i : I) (w : B) := if w.val=r then ρ i else ι₀ w
  have hlabel (i : I) (w : B) : T.endpoint (j i w).val=w.val := by
    by_cases hw : w.val=r
    · simp only [j,if_pos hw]
      rw [hr,hw]
    · simp only [j,if_neg hw,hlabel₀]
  have hjinj (i : I) : Function.Injective (j i) := by
    intro w z hwz
    apply Subtype.ext
    exact (hlabel i w).symm.trans
      ((congrArg (fun s ↦ T.endpoint s.val) hwz).trans (hlabel i z))
  let ι (i : I) : B ↪ {s : Fin k × Bool // s.1 ∈ A} := ⟨j i,hjinj i⟩
  have hjr (i : I) : ι i ⟨r,hrB⟩=ρ i := by simp [ι,j]
  have hnn (i : I) : ¬(R.tail (ι i ⟨r,hrB⟩)).Nil := by rw [hjr]; exact hn i
  let F (i : I) := R.selected B hrB (ι i) (hlabel i) (hnn i)
  have hFt (i j' : I) (w : B) (hw : w.val ≠ r) : (F i).tail w=(F j').tail w := by
    have hh : ι i w=ι j' w := by
      change j i w=j j' w
      simp only [j,if_neg hw]
    apply Walk.ext_support
    simp only [F,RootedCut.selected,Walk.support_copy]
    exact congrArg (fun s ↦ (R.tail s).support) hh
  have hFroot (i : I) : ((F i).tail ⟨r,(F i).root_mem⟩).toSubgraph=(R.tail (ρ i)).toSubgraph := by
    rw [R.selected_subgraph,hjr]
  have hFd : Pairwise fun i j' ↦
      Disjoint ((F i).tail ⟨r,(F i).root_mem⟩).toSubgraph.edgeSet
        ((F j').tail ⟨r,(F j').root_mem⟩).toSubgraph.edgeSet := by
    intro i j' hij
    rw [hFroot,hFroot]
    exact R.disjoint (ρ.injective.ne hij)
  obtain ⟨E,hEc,hE⟩ := parallel_root_exposures F hFt hFd
  have hcard : E.card=2*Fintype.card I := by
    rw [hEc]
    have hh (i : I) : (((F i).tail ⟨r,(F i).root_mem⟩).toSubgraph.neighborSet r).ncard=2 :=
      (selected_regular R hR B hrB (ι i) (hlabel i) (hnn i)).1.ncard_neighborSet_toSubgraph_eq_two
        ((F i).tail ⟨r,(F i).root_mem⟩).start_mem_support
    simp only [hh,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    omega
  refine ⟨B,E,hcard,?_⟩
  intro z hz
  obtain ⟨hzB,i,S,hS,hSz⟩ := hE z hz
  obtain ⟨U,hUs,hUq,hlabels,Q,hQr,ι',hlabel',hQt⟩ :=
    regular_rebuild_selected R hR B hrB (ι i) (hlabel i) (hnn i) S hS
  refine ⟨hzB,U,hUs,hUq,Q,hQr,fun x ↦ (hB x).trans (hlabels x).symm,
    ι' ⟨r,S.root_mem⟩,hlabel' _,?_⟩
  rw [hQt,←hSz]
  exact (S.tail ⟨r,S.root_mem⟩).toSubgraph_adj_snd S.root_nonempty

def RegularlyRooted {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) : Prop :=
  ∃ A : Finset (Fin k), ∃ R : RootedCut T r A, RegularCut R

lemma exists_max_regular_score {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hT : RegularlyRooted T r) :
    ∃ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) ∧ RegularlyRooted U r ∧
      ∀ S : TrailFamily G k, (∀ v, S.quota v=T.quota v) → RegularlyRooted S r → S.score ≤ U.score := by
  classical
  let P (m : ℕ) := ∃ S : TrailFamily G k,
    (∀ v, S.quota v=T.quota v) ∧ RegularlyRooted S r ∧ S.score=m
  have hm : P (Nat.findGreatest P (k*Fintype.card V)) :=
    Nat.findGreatest_spec T.score_le ⟨T,fun _ ↦ rfl,hT,rfl⟩
  obtain ⟨U,hUq,hUr,hUs⟩ := hm
  refine ⟨U,hUq,hUr,?_⟩
  intro S hSq hSr
  rw [hUs]
  exact Nat.le_findGreatest S.score_le ⟨S,hSq,hSr,rfl⟩

lemma regular_exposure_zero_at_max {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r z : V} {A : Finset (Fin k)} {B : Finset V}
    (hm : ∀ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) → RegularlyRooted U r → U.score ≤ T.score)
    (hz : z ∉ B) (hE : RegularExposure T r A B z) : T.quota z=0 := by
  by_contra hn
  have hp : 0 < T.quota z := Nat.pos_of_ne_zero hn
  obtain ⟨U,hUs,hUq,Q,hQr,hB,ρ,hρ,hAdj⟩ := hE
  obtain ⟨τ,hτ,hτA,_⟩ := Q.outside_endpoint B hB hz (by rw [hUq]; exact hp)
  obtain ⟨P,hPs,hPq,R,hR⟩ := regular_improve_outside Q hQr ρ hρ τ hτA (by rw [hτ]; exact hAdj)
  have hh := hm P (fun v ↦ (hPq v).trans (hUq v)) ⟨_,R,hR⟩
  omega

lemma max_regular_petals_bound {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    {G : SimpleGraph V} {k : ℕ} {T : TrailFamily G k} {r : V} {A : Finset (Fin k)}
    (R : RootedCut T r A) (hR : RegularCut R)
    (hm : ∀ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) → RegularlyRooted U r → U.score ≤ T.score)
    (ρ : I ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hr : ∀ i, T.endpoint (ρ i).val=r) (hn : ∀ i, ¬(R.tail (ρ i)).Nil) :
    2*Fintype.card I ≤ {z | T.quota z=0}.ncard := by
  obtain ⟨B,E,hEc,hE⟩ := regular_parallel_exposures R hR ρ hr hn
  have hsub : (E : Set V) ⊆ {z | T.quota z=0} := by
    intro z hz
    obtain ⟨hzB,hEz⟩ := hE z hz
    exact regular_exposure_zero_at_max hm hzB hEz
  have hh := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset,hEc] at hh
  exact hh

lemma regularCut_nonpath_root {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (s : {s : Fin k × Bool // s.1 ∈ A})
    (hs : ¬(R.tail s).IsPath) : T.endpoint s.val=r ∧ ¬(R.tail s).Nil := by
  refine ⟨((hR.1 s).resolve_left hs).1,?_⟩
  intro hn
  apply hs
  rw [Walk.isPath_def,Walk.nil_iff_support_eq.mp hn]
  exact List.nodup_singleton _

lemma max_regular_three_zeros_deficit {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} {T : TrailFamily G k} {r : V} {A : Finset (Fin k)}
    (R : RootedCut T r A) (hR : RegularCut R)
    (hm : ∀ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) → RegularlyRooted U r → U.score ≤ T.score)
    (hz : {z | T.quota z=0}.ncard ≤ 3) : G.edgeSet.ncard+k ≤ T.score+1 := by
  classical
  by_cases hp : ∀ s, (R.tail s).IsPath
  · have hh := T.score_eq_edges_add_iff.mpr (regularCut_all_paths R hR hp)
    omega
  · obtain ⟨s,hs⟩ := not_forall.mp hp
    let I := {s : {s : Fin k × Bool // s.1 ∈ A} // ¬(R.tail s).IsPath}
    letI : Nonempty I := ⟨⟨s,hs⟩⟩
    let ρ : I ↪ {s : Fin k × Bool // s.1 ∈ A} := Function.Embedding.subtype _
    have hb := max_regular_petals_bound R hR hm ρ
      (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).1)
      (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).2)
    have hc : Fintype.card I ≤ 1 := by omega
    have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hc
    apply regularCut_one_petal_bound R hR s
    intro t hts
    by_contra ht
    exact hts (congrArg Subtype.val (hsub.elim (⟨t,ht⟩ : I) ⟨s,hs⟩))

/-- Three zero labels suffice to leave at most one petal after regular
optimization. An available root pair and an even-induced forest repair that
last defect; endpoint quotas are not prescribed in the final family. -/
lemma normalize_regular_three_zeros {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hT : RegularlyRooted T r)
    (hz : {z | T.quota z=0}.ncard ≤ 3) (hq : 2 ≤ T.quota r)
    (hf : (G.induce {z | Even (Nat.card (G.neighborSet z))}).IsAcyclic) :
    ∃ P : TrailFamily G k, ∀ i, (P.walk i).IsPath := by
  classical
  obtain ⟨U,hUq,hUr,hm⟩ := exists_max_regular_score T r hT
  obtain ⟨A,R,hR⟩ := hUr
  have hmU : ∀ S : TrailFamily G k, (∀ v, S.quota v=U.quota v) → RegularlyRooted S r → S.score ≤ U.score := by
    intro S hSq hSr
    exact hm S (fun v ↦ (hSq v).trans (hUq v)) hSr
  have hzU : {z | U.quota z=0}.ncard ≤ 3 := by simpa only [hUq] using hz
  have hb := max_regular_three_zeros_deficit R hR hmU hzU
  by_cases hp : ∀ i, (U.walk i).IsPath
  · exact ⟨U,hp⟩
  · have hs : U.score+1=G.edgeSet.ncard+k := by
      have hle := U.score_le_edges_add
      have hne := U.score_eq_edges_add_iff.not.mpr hp
      omega
    have htail : ∃ s, ¬(R.tail s).IsPath := by
      by_contra hn
      push_neg at hn
      exact hp (regularCut_all_paths R hR hn)
    obtain ⟨s,hsp⟩ := htail
    obtain ⟨hroot,hn⟩ := regularCut_nonpath_root R hR s hsp
    apply QuotaParity.normalize_root_with_pair_of_even_forest U r hs ⟨A,R,s,hroot,hn⟩
      (by rw [hUq]; exact hq) hf

end Erdos583RegularFlowerExposuresDevelopment
