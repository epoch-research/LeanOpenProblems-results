import Submission.BoundaryCorrectionEligibilityExplore
import Submission.CountingExplore

/-! Monotone clipping gives simultaneous upper bounds. The explicit
prefix deletion budget is a condition to check, not a lower-bound theorem. -/
namespace Erdos66MonotoneClipping
open Filter AdditiveCombinatorics Erdos66BoundaryCorrectionEligibility
  Erdos66CentralTripleDeletion Erdos66Counting Erdos66Explore Erdos66Compactness
open scoped Classical Topology
set_option maxHeartbeats 2000000

 def excess (r q : ℕ) : ℕ := if q<r then (r-q+1)/2 else 0

lemma excess_mono {r s q : ℕ} (hrs : r ≤ s) : excess r q ≤ excess s q := by
  unfold excess
  split_ifs <;> omega

lemma exists_upper_clipping (A : Set ℕ) (n q : ℕ) (hq : 1 ≤ q) :
    ∃ D : Finset ℕ, D ⊆ upperEndpoints A 0 n ∧ D.card=excess (sumRep A n) q ∧
      sumRep (A\(D : Set ℕ)) n ≤ q ∧
      min (sumRep A n) (q-1) ≤ sumRep (A\(D : Set ℕ)) n := by
  by_cases hr : sumRep A n ≤ q
  · refine ⟨∅,Finset.empty_subset _,?_,?_,?_⟩
    · simp only [Finset.card_empty,excess,not_lt.mpr hr,ite_false]
    · simpa using hr
    · simpa using min_le_left (sumRep A n) (q-1)
  have hcap := upper_count_bounds_rep A n
  have hk : excess (sumRep A n) q ≤ (upperEndpoints A 0 n).card := by
    simp only [excess,lt_of_not_ge hr,ite_true]
    omega
  obtain ⟨D,hD,hcard,he,hother⟩ := exists_exact_downward_correction A 0 n (excess (sumRep A n) q) hk
  refine ⟨D,hD,hcard,?_,?_⟩
  · simp only [excess,lt_of_not_ge hr,ite_true] at he
    omega
  · simp only [excess,lt_of_not_ge hr,ite_true] at he
    omega

lemma exists_clipping_chain (A : Set ℕ) (q : ℕ → ℕ) (hq : ∀ n, 1 ≤ q n) :
    ∃ (B : ℕ → Set ℕ) (D : ℕ → Finset ℕ), B 0=A ∧
      (∀ n, B (n+1)=B n\(D n : Set ℕ)) ∧
      (∀ n, D n ⊆ upperEndpoints (B n) 0 n) ∧
      (∀ n, (D n).card=excess (sumRep (B n) n) (q n)) ∧
      (∀ n, sumRep (B (n+1)) n ≤ q n) ∧
      (∀ n, min (sumRep (B n) n) (q n-1) ≤ sumRep (B (n+1)) n) := by
  choose packet hp using fun n B ↦ exists_upper_clipping B n (q n) (hq n)
  let B : ℕ → Set ℕ := Nat.rec A (fun n S ↦ S\(packet n S : Set ℕ))
  let D : ℕ → Finset ℕ := fun n ↦ packet n (B n)
  exact ⟨B,D,rfl,fun _ ↦ rfl,fun n ↦ (hp n (B n)).1,
    fun n ↦ (hp n (B n)).2.1,fun n ↦ (hp n (B n)).2.2.1,
    fun n ↦ (hp n (B n)).2.2.2⟩

lemma chain_antitone (B : ℕ → Set ℕ) (D : ℕ → Finset ℕ)
    (hstep : ∀ n, B (n+1)=B n\(D n : Set ℕ)) : Antitone B := by
  apply antitone_nat_of_succ_le
  intro n
  rw [hstep]
  exact Set.diff_subset

lemma chain_mem_iff (A : Set ℕ) (B : ℕ → Set ℕ) (D : ℕ → Finset ℕ)
    (hzero : B 0=A) (hstep : ∀ n, B (n+1)=B n\(D n : Set ℕ)) (n a : ℕ) :
    a∈B n ↔ a∈A ∧ ∀ t<n, a∉D t := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [hstep]
    simp only [Set.mem_diff,Finset.mem_coe,ih]
    constructor
    · rintro ⟨⟨ha,ht⟩,hn⟩
      exact ⟨ha,fun t htn ↦ by rcases Nat.lt_succ_iff_lt_or_eq.mp htn with ht' | rfl; exact ht t ht'; exact hn⟩
    · rintro ⟨ha,ht⟩
      exact ⟨⟨ha,fun t htn ↦ ht t (by omega)⟩,ht n (by omega)⟩

lemma intersection_mem_iff (A : Set ℕ) (B : ℕ → Set ℕ) (D : ℕ → Finset ℕ)
    (hzero : B 0=A) (hstep : ∀ n, B (n+1)=B n\(D n : Set ℕ)) (a : ℕ) :
    a∈⋂ n, B n ↔ a∈A ∧ ∀ t, a∉D t := by
  simp only [Set.mem_iInter,chain_mem_iff A B D hzero hstep]
  constructor
  · intro h
    exact ⟨(h 0).1,fun t ↦ (h (t+1)).2 t (by omega)⟩
  · rintro ⟨ha,ht⟩ n
    exact ⟨ha,fun t _ ↦ ht t⟩

lemma clipping_prefix_stable (A : Set ℕ) (B : ℕ → Set ℕ) (D : ℕ → Finset ℕ)
    (hzero : B 0=A) (hstep : ∀ n, B (n+1)=B n\(D n : Set ℕ))
    (hD : ∀ n, D n ⊆ upperEndpoints (B n) 0 n) (N a : ℕ) (ha : a<N) :
    a∈⋂ n, B n ↔ a∈B (2*N) := by
  rw [intersection_mem_iff A B D hzero hstep,chain_mem_iff A B D hzero hstep]
  apply and_congr_right
  intro _
  constructor
  · exact fun h t _ ↦ h t
  · intro h t ht
    have hh := (mem_upperEndpoints.mp (hD t ht)).2.2.2.2.2
    exact h t (by omega) ht

lemma clipping_removed_prefix_subset (A : Set ℕ) (B : ℕ → Set ℕ) (D : ℕ → Finset ℕ)
    (hzero : B 0=A) (hstep : ∀ n, B (n+1)=B n\(D n : Set ℕ))
    (hD : ∀ n, D n ⊆ upperEndpoints (B n) 0 n) (N : ℕ) :
    cutoff (A\⋂ n, B n) N ⊆ (Finset.range (2*N)).biUnion D := by
  intro a ha
  obtain ⟨haN,haA,hanot⟩ := mem_cutoff.mp ha
  rw [intersection_mem_iff A B D hzero hstep] at hanot
  have he : ∃ t, a∈D t := by simpa only [haA,true_and,not_forall,not_not] using hanot
  obtain ⟨t,ht⟩ := he
  have hh := (mem_upperEndpoints.mp (hD t ht)).2.2.2.2.2
  exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_range.mpr (by omega),ht⟩

 theorem exists_simultaneous_upper_clipping (A : Set ℕ) (q : ℕ → ℕ) (hq : ∀ n, 1 ≤ q n) :
    ∃ C : Set ℕ, C ⊆ A ∧ (∀ n, sumRep C n ≤ q n) ∧
      ∀ N, count (A\C) N ≤ ∑ n∈Finset.range (2*N), excess (sumRep A n) (q n) := by
  obtain ⟨B,D,hzero,hstep,hD,hcard,hu,hl⟩ := exists_clipping_chain A q hq
  let C := ⋂ n, B n
  have hsub : C ⊆ A := by simpa only [hzero] using Set.iInter_subset B 0
  have hBA (n : ℕ) : B n ⊆ A := by simpa only [hzero] using chain_antitone B D hstep (Nat.zero_le n)
  refine ⟨C,hsub,fun n ↦ (sumRep_mono (Set.iInter_subset B (n+1)) n).trans (hu n),?_⟩
  intro N
  have hc := (Finset.card_le_card (clipping_removed_prefix_subset A B D hzero hstep hD N)).trans Finset.card_biUnion_le
  apply hc.trans
  apply Finset.sum_le_sum
  intro n hn
  rw [hcard]
  exact excess_mono (sumRep_mono (hBA n) n)

end Erdos66MonotoneClipping
