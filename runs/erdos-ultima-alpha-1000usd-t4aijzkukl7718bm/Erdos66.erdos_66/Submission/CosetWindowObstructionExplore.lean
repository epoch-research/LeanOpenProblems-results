import Submission.AffineOldPlaneSliceExplore
import Submission.SquareAnnulusMassExplore

/-! A coset-by-coset natural encoding of a sparse parabola model cannot
supply the mass required in every doubling window. This excludes the stated
encoding class only; it is not a disproof of Erdős 66. -/
namespace Erdos66CosetWindowObstruction
open Erdos66AffineOldPlaneSlice Erdos66FreshCurvePrefix
  Erdos66ParabolaRepair Erdos66OriginRepair Erdos66FiniteField Erdos66Coset
  Erdos66Counting Erdos66SquareAnnulusMass
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2200000

section Finite
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

lemma encoded_coset_window_bound (A : Set ℕ) (N : ℕ) (e : ℕ→K×K)
    (he : Set.InjOn e (Set.Ico N (2*N)))
    (k : Subfield K) (hK : ringChar K≠2)
    (U : Finset K) (hU : ∀ u∈U, u≠0) (w : K) (hw : w≠0)
    (T : Finset K) (z : K×K) (hz : z∉oldPlane k)
    (hcoset : ∀ n, N≤n → n<2*N → z-e n∈oldPlane k)
    (hmem : ∀ n, N≤n → n<2*N →
      (n∈A ↔ e n∈parabolaSet U∪repairPoints w T)) :
    count A (2*N)≤count A N+2*U.card+4 := by
  let D := cutoff A (2*N)\cutoff A N
  have hd (n : ℕ) (hn : n∈D) : N≤n ∧ n<2*N ∧ n∈A := by
    obtain ⟨hn2,hnN⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hn2,hnA⟩ := mem_cutoff.mp hn2
    have hh : ¬n<N := fun h ↦ hnN (mem_cutoff.mpr ⟨h,hnA⟩)
    exact ⟨by omega,hn2,hnA⟩
  have hcut : cutoff A N⊆cutoff A (2*N) := by
    intro n hn
    obtain ⟨hn,ha⟩ := mem_cutoff.mp hn
    exact mem_cutoff.mpr ⟨by omega,ha⟩
  have hc : D.card=count A (2*N)-count A N := Finset.card_sdiff_of_subset hcut
  have him : (D.image e).card=D.card := by
    apply Finset.card_image_iff.mpr
    intro n hn m hm heq
    exact he ⟨(hd n hn).1,(hd n hn).2.1⟩ ⟨(hd m hm).1,(hd m hm).2.1⟩ heq
  have hsub : D.image e⊆(parabolaSet U∪repairPoints w T).filter
      (fun b ↦ z-b∈oldPlane k) := by
    intro b hb
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hN,hn2,hnA⟩ := hd n hn
    exact Finset.mem_filter.mpr ⟨(hmem n hN hn2).mp hnA,hcoset n hN hn2⟩
  have hcount := Finset.card_le_card hsub
  rw [him] at hcount
  have hcap := off_old_repaired_cap k hK U hU w hw T z hz
  change ((parabolaSet U∪repairPoints w T).filter
    (fun b ↦ z-b∈oldPlane k)).card≤2*U.card+4 at hcap
  have hle := Finset.card_le_card hcut
  change count A N≤count A (2*N) at hle
  omega

/-- The cardinality regime of the subfield-block extension gives a uniform
linear bound on the entire next old-sized natural block. -/
lemma encoded_subfield_sized_window_bound (A : Set ℕ) (q : ℕ) (e : ℕ→K×K)
    (he : Set.InjOn e (Set.Ico (q^2) (2*q^2)))
    (k : Subfield K) (hK : ringChar K≠2)
    (U : Finset K) (hU : ∀ u∈U, u≠0) (hcard : U.card≤2*q)
    (w : K) (hw : w≠0) (T : Finset K) (z : K×K) (hz : z∉oldPlane k)
    (hcoset : ∀ n, q^2≤n → n<2*q^2 → z-e n∈oldPlane k)
    (hmem : ∀ n, q^2≤n → n<2*q^2 →
      (n∈A ↔ e n∈parabolaSet U∪repairPoints w T)) :
    count A (2*q^2)≤count A (q^2)+4*q+4 := by
  have hh := encoded_coset_window_bound A (q^2) e he k hK U hU w hw T z hz hcoset hmem
  omega
end Finite

/-- A necessary parameter budget for any such encoded window of a
hypothetical witness. The field and all encoding data may be chosen after q. -/
theorem witness_eventually_many_coset_parameters {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) (C : ℕ) :
    ∀ᶠ q : ℕ in atTop,
      ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K],
      ∀ e : ℕ→K×K, Set.InjOn e (Set.Ico (q^2) (2*q^2)) →
      ∀ k : Subfield K, ringChar K≠2 →
      ∀ U : Finset K, (∀ u∈U, u≠0) →
      ∀ w : K, w≠0 → ∀ T : Finset K, ∀ z : K×K, z∉oldPlane k →
      (∀ n, q^2≤n → n<2*q^2 → z-e n∈oldPlane k) →
      (∀ n, q^2≤n → n<2*q^2 → (n∈A ↔ e n∈parabolaSet U∪repairPoints w T)) →
      C*q<U.card := by
  filter_upwards [witness_eventually_large_window_budget hc ht C] with q hq
  intro K _ _ _ e he k hK U hU w hw T z hz hcoset hmem
  exact hq U.card (encoded_coset_window_bound A (q^2) e he k hK U hU w hw T z hz hcoset hmem)

/-- Only the next window is prescribed. The encoding, field, subfield,
parameters, and repair may all change with q. The encoder is injective on
that finite window, not on all of Nat. -/
def HasCosetWindow (A : Set ℕ) (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : DecidableEq K)
    (k : Subfield K) (U : Finset K) (w : K) (T : Finset K)
    (z : K×K) (e : ℕ→K×K),
    ringChar K≠2 ∧ (∀ u∈U, u≠0) ∧ U.card≤2*q ∧ w≠0 ∧
    z∉oldPlane k ∧ Set.InjOn e (Set.Ico (q^2) (2*q^2)) ∧
    (∀ n, q^2≤n → n<2*q^2 → z-e n∈oldPlane k) ∧
    ∀ n, q^2≤n → n<2*q^2 → (n∈A ↔ e n∈parabolaSet U∪repairPoints w T)

lemma hasCosetWindow_count_bound (A : Set ℕ) (q : ℕ) (h : HasCosetWindow A q) :
    count A (2*q^2)≤count A (q^2)+4*q+4 := by
  obtain ⟨K,hfield,hfinite,hdec,k,U,w,T,z,e,hK,hU,hcard,hw,hz,he,hcoset,hmem⟩ := h
  exact encoded_subfield_sized_window_bound A q e he k hK U hU hcard w hw T z hz hcoset hmem

/-- This excludes repeated coset-block encodings with O(q) parameters,
not arbitrary natural sets or the original conjecture. -/
theorem no_log_limit_of_frequent_coset_windows (A : Set ℕ)
    (hmodel : ∀ L : ℕ, ∃ q≥L, HasCosetWindow A q) (c : ℝ) (hc : c≠0) :
    ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c) := by
  apply no_log_limit_of_frequent_thin_square_annuli A 4 _ c hc
  intro L
  obtain ⟨q,hq,hmodel⟩ := hmodel L
  exact ⟨q,hq,hasCosetWindow_count_bound A q hmodel⟩

end Erdos66CosetWindowObstruction
