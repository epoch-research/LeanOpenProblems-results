import Submission.SplitPathFamilyCapacity
import Submission.PathCoreIntervals

/-! A singleton core interval created by splitting a path has its other
split piece as a crossing partner. Unsplit carriers with at least two core
vertices cannot create a singleton interval. -/
namespace Erdos583SplitCorePartnersDevelopment
open SimpleGraph Erdos583Work
open Erdos583SplitPathFamilyCapacityDevelopment Erdos583PathCoreIntervalsDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma split_core_family_with_partners {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (a b : Fin k → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (E : Set (Sym2 V)) (hE : ∀ i, Disjoint E (p i).toSubgraph.edgeSet)
    (S : Set V) (hsize : ∀ i, 2 ≤ (coreVerts (p i) S).ncard)
    (R : ∀ {u v}, G.Walk u v → Prop)
    (j : Fin k) {z : V} (hz : z ∉ S) (A : G.Walk (a j) z) (B : G.Walk z (b j))
    (hform : p j=A.append B) (hA : R A) (hB : R B)
    (hR : ∀ i, i ≠ j → R (p i)) :
    ∃ x y : Fin (k+1) → V, ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath) ∧
      Pairwise (fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) ∧
      (∀ i, Disjoint E (q i).toSubgraph.edgeSet) ∧
      (⋃ i, (q i).toSubgraph.edgeSet)=(⋃ i, (p i).toSubgraph.edgeSet) ∧
      (∀ i, R (q i)) ∧
      (∀ w ∈ S, (Finset.univ.filter fun i ↦ w ∈ (q i).support).card ≤ k) ∧
      (∀ i, (coreVerts (q i) S).ncard=1 → ∃ l z,
        i ≠ l ∧ z ∉ S ∧ ((y i=z ∧ x l=z) ∨ (x i=z ∧ y l=z)) ∧
        ∀ w ∈ (q i).support, w ∈ (q l).support → w=z) := by
  classical
  obtain ⟨x,y,q,hq,hqd,hEq,hqc,hRq,hcount,hzero,hsucc⟩ :=
    split_path_family_capacity a b p hp hd E hE R j A B hform hA hB hR
  have hcap (w : V) (hw : w ∈ S) :
      (Finset.univ.filter fun i ↦ w ∈ (q i).support).card ≤ k := by
    rw [hcount w (fun hh ↦ hz (hh ▸ hw))]
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  let sup (d : Σ u v, G.Walk u v) := d.2.2.support
  let core (d : Σ u v, G.Walk u v) := (coreVerts d.2.2 S).ncard
  have hq0s : (q 0).support=A.support := congrArg sup hzero
  have hqjs : (q j.succ).support=B.support := by
    have hh := congrArg sup (hsucc j)
    simpa only [if_pos rfl] using hh
  have hy0 : y 0=z := congrArg (fun d : Σ u v, G.Walk u v ↦ d.2.1) hzero
  have hxj : x j.succ=z := by
    have hh := congrArg (fun d : Σ u v, G.Walk u v ↦ d.1) (hsucc j)
    simpa only [if_pos rfl] using hh
  have hmeet : ∀ w ∈ (q 0).support, w ∈ (q j.succ).support → w=z := by
    rw [hq0s,hqjs]
    intro w hwA hwB
    by_contra hwz
    exact (hform ▸ hp j).ne_of_mem_support_of_append hwz hwA hwB rfl
  refine ⟨x,y,q,hq,hqd,hEq,hqc,hRq,hcap,?_⟩
  intro i hi
  induction i using Fin.cases with
  | zero =>
    exact ⟨j.succ,z,(Fin.succ_ne_zero j).symm,hz,Or.inl ⟨hy0,hxj⟩,hmeet⟩
  | succ l =>
    by_cases hlj : l=j
    · subst l
      exact ⟨0,z,Fin.succ_ne_zero j,hz,Or.inr ⟨hxj,hy0⟩,fun w hwB hwA ↦ hmeet w hwA hwB⟩
    · have hc : (coreVerts (q l.succ) S).ncard=(coreVerts (p l) S).ncard := by
        have hh := congrArg core (hsucc l)
        simpa only [if_neg hlj] using hh
      have hb := hsize l
      omega

end Erdos583SplitCorePartnersDevelopment
