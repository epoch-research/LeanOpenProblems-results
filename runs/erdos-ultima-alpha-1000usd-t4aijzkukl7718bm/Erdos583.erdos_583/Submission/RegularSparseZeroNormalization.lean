import Submission.RegularFlowerExposures

/-! Sparse-zero consequences of regular rooted optimization.
These are auxiliary normalization results, not the Gallai conjecture. -/
namespace Erdos583RegularSparseZeroNormalizationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583RegularRootedCutDevelopment Erdos583RegularCutDefectsDevelopment
open Erdos583RegularFlowerExposuresDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- With at most one zero label, regular optimization produces paths at
exactly the original endpoint quotas. -/
lemma normalize_regular_one_zero {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hT : RegularlyRooted T r) (hz : {z | T.quota z=0}.ncard ≤ 1) :
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
  have hb := max_regular_petals_bound R hR hmU ρ
    (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).1)
    (fun i ↦ (regularCut_nonpath_root R hR i.val i.property).2)
  have hzU : {z | U.quota z=0}.ncard ≤ 1 := by simpa only [hUq] using hz
  have hp : 0 < Fintype.card I := Fintype.card_pos
  omega

/-- Only the zero-baseline graph must be a forest, not the entire graph
induced by even-degree vertices. Quotas may change by relocating a pair. -/
lemma normalize_regular_zero_baseline_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hT : RegularlyRooted T r) (hz : {z | T.quota z=0}.ncard ≤ 3)
    (hq : 2 ≤ T.quota r)
    (hf : (G.induce {v | (if v=r then T.quota v-2 else T.quota v)=0}).IsAcyclic) :
    ∃ P : TrailFamily G k, ∀ i, (P.walk i).IsPath := by
  classical
  obtain ⟨U,hUq,⟨A,R,hR⟩,hm⟩ := exists_max_regular_score T r hT
  have hmU : ∀ S : TrailFamily G k, (∀ v, S.quota v=U.quota v) →
      RegularlyRooted S r → S.score ≤ U.score := by
    intro S hSq hSr
    exact hm S (fun v ↦ (hSq v).trans (hUq v)) hSr
  have hzU : {z | U.quota z=0}.ncard ≤ 3 := by simpa only [hUq] using hz
  have hb := max_regular_three_zeros_deficit R hR hmU hzU
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

lemma acyclic_of_card_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : Fintype.card V ≤ 2) : G.IsAcyclic := by
  intro v C hC
  have hl := hC.support_nodup.length_le_card
  simp only [List.length_tail,Walk.length_support,Nat.add_sub_cancel] at hl
  have ht := hC.three_le_length
  omega

/-- A root quota at least three does not create a new zero baseline when
its pair is removed. Two actual zeros therefore always form a forest. -/
lemma normalize_regular_two_zeros_large_root {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hT : RegularlyRooted T r) (hz : {z | T.quota z=0}.ncard ≤ 2)
    (hq : 3 ≤ T.quota r) :
    ∃ P : TrailFamily G k, ∀ i, (P.walk i).IsPath := by
  classical
  apply normalize_regular_zero_baseline_forest T r hT (by omega) (by omega)
  have he : {v | (if v=r then T.quota v-2 else T.quota v)=0} =
      {v | T.quota v=0} := by
    ext v
    simp only [Set.mem_setOf_eq]
    by_cases hv : v=r
    · subst v
      simp only [ite_true]
      omega
    · simp only [if_neg hv]
  rw [he]
  apply acyclic_of_card_le_two
  simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using hz

/-- On at most three vertices, a cyclic graph must be the full triangle. -/
lemma nonacyclic_card_le_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : Fintype.card V ≤ 3) (hn : ¬G.IsAcyclic) :
    Fintype.card V=3 ∧ ∀ a b, a ≠ b → G.Adj a b := by
  classical
  simp only [SimpleGraph.IsAcyclic,not_forall,not_not] at hn
  obtain ⟨v,C,hC⟩ := hn
  have hl := hC.support_nodup.length_le_card
  simp only [List.length_tail,Walk.length_support,Nat.add_sub_cancel] at hl
  have ht := hC.three_le_length
  have hlen : C.length=3 := by omega
  have hcard : Fintype.card V=3 := by omega
  obtain ⟨s,hs⟩ := G.is3Clique_iff_exists_cycle_length_three.mpr ⟨v,C,hC,hlen⟩
  have hsu : s=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ s)
    (by simpa only [Finset.card_univ,hs.card_eq] using h)
  refine ⟨hcard,?_⟩
  intro a b hab
  exact hs.isClique (by simp [hsu]) (by simp [hsu]) hab

/-- Under the two-zero hypothesis, failure of regular normalization can
only occur at quota two, with precisely two zero labels forming a triangle
with the root. This is a necessary condition, not an existence claim. -/
lemma regular_two_zero_failure_triangle {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hT : RegularlyRooted T r) (hz : {z | T.quota z=0}.ncard ≤ 2)
    (hq : 2 ≤ T.quota r)
    (hn : ¬∃ P : TrailFamily G k, ∀ i, (P.walk i).IsPath) :
    T.quota r=2 ∧ ∃ x y, x ≠ y ∧ {z | T.quota z=0}=({x,y} : Set V) ∧
      G.Adj r x ∧ G.Adj r y ∧ G.Adj x y := by
  classical
  have hqr : T.quota r=2 := by
    by_contra he
    exact hn (normalize_regular_two_zeros_large_root T r hT hz (by omega))
  have hf : ¬(G.induce {v | (if v=r then T.quota v-2 else T.quota v)=0}).IsAcyclic := by
    intro hf
    exact hn (normalize_regular_zero_baseline_forest T r hT (by omega) hq hf)
  let Z : Set V := {z | T.quota z=0}
  have hrZ : r ∉ Z := by change ¬T.quota r=0; omega
  have he : {v | (if v=r then T.quota v-2 else T.quota v)=0}=insert r Z := by
    ext v
    by_cases hv : v=r
    · subst v; simp [hqr]
    · simp [hv,Z]
  rw [he] at hf
  have hcard : Fintype.card ↥(insert r Z) ≤ 3 := by
    have hh := Set.ncard_insert_le r Z
    have hz' : Z.ncard ≤ 2 := hz
    have hh' : (insert r Z).ncard ≤ 3 := by omega
    simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using hh'
  obtain ⟨hthree,hcl⟩ := nonacyclic_card_le_three (G.induce (insert r Z)) hcard hf
  have hZcard : Z.ncard=2 := by
    have hh : (insert r Z).ncard=3 := by
      simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using hthree
    rw [Set.ncard_insert_of_notMem hrZ] at hh
    omega
  obtain ⟨x,y,hxy,hZ⟩ := Set.ncard_eq_two.mp hZcard
  have hx : x ∈ Z := by simp [hZ]
  have hy : y ∈ Z := by simp [hZ]
  have hrx : r ≠ x := by rintro rfl; exact hrZ hx
  have hry : r ≠ y := by rintro rfl; exact hrZ hy
  let r' : ↥(insert r Z) := ⟨r,Set.mem_insert r Z⟩
  let x' : ↥(insert r Z) := ⟨x,Set.mem_insert_of_mem r hx⟩
  let y' : ↥(insert r Z) := ⟨y,Set.mem_insert_of_mem r hy⟩
  exact ⟨hqr,x,y,hxy,hZ,
    hcl r' x' (fun hh ↦ hrx (congrArg Subtype.val hh)),
    hcl r' y' (fun hh ↦ hry (congrArg Subtype.val hh)),
    hcl x' y' (fun hh ↦ hxy (congrArg Subtype.val hh))⟩

end Erdos583RegularSparseZeroNormalizationDevelopment
