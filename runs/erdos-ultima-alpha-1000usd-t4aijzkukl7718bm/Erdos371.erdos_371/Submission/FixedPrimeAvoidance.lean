import Submission.CoprimeResidueSieve
import Submission.FiniteEndpointTransfer

/-! Finite-prime approximations to a fixed prime-avoidance indicator. The
forbidden set is fixed before the counting endpoint tends to infinity. -/
namespace Erdos371.FixedPrimeAvoidance
open Finset Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def avoid (B : Set ℕ) (n : ℕ) : ℝ :=
  if ∀ p, p.Prime → p ∈ B → ¬p ∣ n then 1 else 0

noncomputable def finiteAvoid (S : Finset ℕ) (n : ℕ) : ℝ :=
  if ∀ p ∈ S, ¬p ∣ n then 1 else 0

noncomputable def primeCut (B : Set ℕ) (K : ℕ) : Finset ℕ :=
  (range K).filter fun p => p.Prime ∧ p ∈ B

noncomputable def reciprocal (B : Set ℕ) (p : ℕ) : ℝ :=
  if p.Prime ∧ p ∈ B then 1/p else 0

lemma avoid_bounds (B : Set ℕ) (n : ℕ) : 0 ≤ avoid B n ∧ avoid B n ≤ 1 := by
  unfold avoid
  split_ifs <;> norm_num

lemma finiteAvoid_bounds (S : Finset ℕ) (n : ℕ) :
    0 ≤ finiteAvoid S n ∧ finiteAvoid S n ≤ 1 := by
  unfold finiteAvoid
  split_ifs <;> norm_num

lemma avoid_le_cut (B : Set ℕ) (K n : ℕ) : avoid B n ≤ finiteAvoid (primeCut B K) n := by
  unfold avoid finiteAvoid
  split_ifs with h h' h'
  · rfl
  · exact (h' (fun p hp => h p (mem_filter.mp hp).2.1 (mem_filter.mp hp).2.2)).elim
  · norm_num
  · rfl

lemma cut_error_bounds (B : Set ℕ) (K n : ℕ) :
    0 ≤ finiteAvoid (primeCut B K) n-avoid B n ∧
      finiteAvoid (primeCut B K) n-avoid B n ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (avoid_le_cut B K n)
  · linarith [(avoid_bounds B n).1,(finiteAvoid_bounds (primeCut B K) n).2]

lemma cut_error_eq_abs (B : Set ℕ) (K n : ℕ) :
    |avoid B n-finiteAvoid (primeCut B K) n| = finiteAvoid (primeCut B K) n-avoid B n := by
  rw [abs_of_nonpos (sub_nonpos.mpr (avoid_le_cut B K n))]
  ring

lemma finiteAvoid_periodic (S : Finset ℕ) (M : ℕ) (hM : ∀ p ∈ S, p ∣ M) :
    Function.Periodic (finiteAvoid S) M := by
  intro n
  unfold finiteAvoid
  have he : (∀ p ∈ S, ¬p ∣ n+M) ↔ ∀ p ∈ S, ¬p ∣ n := by
    apply forall₂_congr
    intro p hp
    exact not_congr (Nat.dvd_add_iff_left (m := n) (hM p hp)).symm
  simp only [he]

lemma finiteAvoid_reflection (S : Finset ℕ) (M : ℕ) (hM : ∀ p ∈ S, p ∣ M)
    (n : ℕ) (hn : n ≤ M) : finiteAvoid S (M-n) = finiteAvoid S n := by
  unfold finiteAvoid
  have he : (∀ p ∈ S, ¬p ∣ M-n) ↔ ∀ p ∈ S, ¬p ∣ n := by
    apply forall₂_congr
    intro p hp
    rw [Nat.dvd_sub_iff_right hn (hM p hp)]
  simp only [he]

lemma reciprocal_nonneg (B : Set ℕ) (p : ℕ) : 0 ≤ reciprocal B p := by
  unfold reciprocal
  split_ifs <;> positivity

lemma cut_reciprocal_sum (B : Set ℕ) (K : ℕ) :
    (∑ p ∈ primeCut B K, (1 : ℝ)/p) = ∑ p ∈ range K, reciprocal B p := by
  simp [primeCut,reciprocal,sum_filter]

lemma positive_cut_error_bound (B : Set ℕ) (K N : ℕ) :
    (∑ n ∈ range N, |avoid B (n+1)-finiteAvoid (primeCut B K) (n+1)|) ≤
      N * (∑ p ∈ (range (N+1)).filter (fun p => K ≤ p ∧ p.Prime ∧ p ∈ B), (1 : ℝ)/p) := by
  let S := (range (N+1)).filter (fun p => K ≤ p ∧ p.Prime ∧ p ∈ B)
  have hpoint (n : ℕ) (hn : n ∈ range N) :
      |avoid B (n+1)-finiteAvoid (primeCut B K) (n+1)| ≤
        ∑ p ∈ S, if p ∣ n+1 then (1 : ℝ) else 0 := by
    by_cases h : ∀ p, p.Prime → p ∈ B → ¬p ∣ n+1
    · have hf : avoid B (n+1) = 1 := if_pos h
      have hc : finiteAvoid (primeCut B K) (n+1) = 1 := by
        have := avoid_le_cut B K (n+1)
        have := (finiteAvoid_bounds (primeCut B K) (n+1)).2
        linarith
      rw [hf,hc,sub_self,abs_zero]
      exact sum_nonneg fun p _ => by split_ifs <;> norm_num
    · by_cases hc : ∀ p ∈ primeCut B K, ¬p ∣ n+1
      · push_neg at h
        obtain ⟨p,hp,hpB,hpn⟩ := h
        have hpK : K ≤ p := by
          by_contra hpK
          exact hc p (mem_filter.mpr ⟨mem_range.mpr (by omega),hp,hpB⟩) hpn
        have hpN : p ≤ N := (Nat.le_of_dvd (by omega : 0 < n+1) hpn).trans
          (by have := mem_range.mp hn; omega)
        have hpS : p ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega),hpK,hp,hpB⟩
        have hb := single_le_sum (s := S) (f := fun p => if p ∣ n+1 then (1 : ℝ) else 0)
          (fun p _ => by dsimp only; split_ifs <;> norm_num) hpS
        dsimp only at hb
        rw [if_pos hpn] at hb
        rw [cut_error_eq_abs]
        exact (cut_error_bounds B K (n+1)).2.trans hb
      · simp only [avoid,finiteAvoid,if_neg h,if_neg hc,sub_self,abs_zero]
        exact sum_nonneg fun p _ => by split_ifs <;> norm_num
  calc
    _ ≤ ∑ n ∈ range N, ∑ p ∈ S, if p ∣ n+1 then (1 : ℝ) else 0 := sum_le_sum hpoint
    _ = ∑ p ∈ S, ((N/p : ℕ) : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      simp [Nat.card_multiples]
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro p _
      simpa only [mul_one_div] using (Nat.cast_div_le (m := N) (n := p) (α := ℝ))

lemma reciprocal_tail_bound (B : Set ℕ) (hB : Summable (reciprocal B)) (K N : ℕ) :
    (∑ p ∈ (range (N+1)).filter (fun p => K ≤ p ∧ p.Prime ∧ p ∈ B), (1 : ℝ)/p) ≤
      (∑' p, reciprocal B p) - ∑ p ∈ range K, reciprocal B p := by
  let S := (range (N+1)).filter (fun p => K ≤ p ∧ p.Prime ∧ p ∈ B)
  have he : (∑ p ∈ S, (1 : ℝ)/p) = ∑ p ∈ S, reciprocal B p := by
    apply sum_congr rfl
    intro p hp
    rw [reciprocal,if_pos (mem_filter.mp hp).2.2]
  have hd : Disjoint S (range K) := by
    apply disjoint_left.mpr
    intro p hp hk
    have := (mem_filter.mp hp).2.1
    have := mem_range.mp hk
    omega
  have ht := hB.sum_le_tsum (S ∪ range K) (fun p _ => reciprocal_nonneg B p)
  rw [sum_union hd] at ht
  change (∑ p ∈ S, (1 : ℝ)/p) ≤ _
  simp only [he]
  linarith

lemma cut_error_bound_of_summable (B : Set ℕ) (hB : Summable (reciprocal B)) (K N : ℕ) :
    (∑ n ∈ range N, |avoid B (n+1)-finiteAvoid (primeCut B K) (n+1)|) ≤
      N * ((∑' p, reciprocal B p)-∑ p ∈ range K, reciprocal B p) :=
  (positive_cut_error_bound B K N).trans
    (mul_le_mul_of_nonneg_left (reciprocal_tail_bound B hB K N) (Nat.cast_nonneg N))

#print axioms cut_error_bound_of_summable
end Erdos371.FixedPrimeAvoidance
