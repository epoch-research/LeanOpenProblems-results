import Submission.PrimePowerError

/-! A nonprime prime power larger than `U^3` contains a square divisor `b^2`
with `b>U`. Integers with such a divisor form a set of size at most `N/U`.
These are support estimates, not prime-pair lower bounds. -/
namespace Erdos972LargeSquareDivisors

open Finset ArithmeticFunction
open Erdos972PrimePowerError

lemma proper_prime_power_has_large_square {d U : ℕ} (hd : IsPrimePow d)
    (hnp : ¬d.Prime) (hlarge : U^3 < d) :
    ∃ b : ℕ, U < b ∧ b^2 ∣ d := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hd
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    simp only [this, pow_one] at hnp
    exact hnp hp
  refine ⟨p^(k/2), ?_, ?_⟩
  · have hle : p^k ≤ (p^(k/2))^3 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hp.one_lt.le (by omega)
    by_contra h
    have hb : p^(k/2) ≤ U := by omega
    have := pow_le_pow_left₀ (Nat.zero_le _) hb 3
    omega
  · rw [← pow_mul]
    exact Nat.pow_dvd_pow p (by omega)

noncomputable def largeSquareSet (U N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => ∃ b ∈ Ioc U N, b^2 ∣ n

lemma mem_largeSquareSet_iff {U N n : ℕ} :
    n ∈ largeSquareSet U N ↔ n ∈ Ioc 0 N ∧ ∃ b : ℕ, U < b ∧ b^2 ∣ n := by
  classical
  simp only [largeSquareSet, mem_filter]
  constructor
  · rintro ⟨hn, b, hb, hd⟩
    exact ⟨hn, b, (mem_Ioc.mp hb).1, hd⟩
  · rintro ⟨hn, b, hb, hd⟩
    have hbn : b ≤ n := (Nat.le_self_pow (by norm_num : 2 ≠ 0) b).trans
      (Nat.le_of_dvd (mem_Ioc.mp hn).1 hd)
    exact ⟨hn, b, mem_Ioc.mpr ⟨hb, hbn.trans (mem_Ioc.mp hn).2⟩, hd⟩

lemma largeSquareSet_subset (U N : ℕ) : largeSquareSet U N ⊆ Ioc 0 N :=
  filter_subset _ _

lemma prime_power_divisor_mem {U N n d : ℕ} (hn : n ∈ Ioc 0 N)
    (hd : d ∣ n) (hpow : IsPrimePow d) (hnp : ¬d.Prime) (hlarge : U^3 < d) :
    n ∈ largeSquareSet U N := by
  obtain ⟨b, hb, hbd⟩ := proper_prime_power_has_large_square hpow hnp hlarge
  exact mem_largeSquareSet_iff.mpr ⟨hn, b, hb, hbd.trans hd⟩

lemma largeSquareSet_eq_biUnion (U N : ℕ) :
    largeSquareSet U N = (Ioc U N).biUnion fun b => (Ioc 0 N).filter fun n => b^2 ∣ n := by
  classical
  ext n
  simp only [largeSquareSet, mem_filter, mem_biUnion]
  aesop

lemma sum_reciprocal_squares_tail {U : ℕ} (hU : 0 < U) (N : ℕ) :
    (∑ b ∈ Ioc U N, 1/(b : ℝ)^2) ≤ 1/(U : ℝ) := by
  by_cases hUN : U ≤ N
  · have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) hU.ne' hUN
    simpa only [one_div] using
      hh.trans (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _)))
  · rw [Ioc_eq_empty_of_le (by omega), sum_empty]
    positivity

theorem largeSquareSet_card_le {U : ℕ} (hU : 0 < U) (N : ℕ) :
    ((largeSquareSet U N).card : ℝ) ≤ (N : ℝ)/U := by
  classical
  rw [largeSquareSet_eq_biUnion]
  calc
    _ ≤ ∑ b ∈ Ioc U N, (((Ioc 0 N).filter fun n => b^2 ∣ n).card : ℝ) := by
      exact_mod_cast (card_biUnion_le (s := Ioc U N)
        (t := fun b => (Ioc 0 N).filter fun n => b^2 ∣ n))
    _ = ∑ b ∈ Ioc U N, ((N / b^2 : ℕ) : ℝ) := by
      simp_rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ b ∈ Ioc U N, (N : ℝ)/(b : ℝ)^2 := by
      apply sum_le_sum
      intro b hb
      simpa only [Nat.cast_pow] using (show ((N / b^2 : ℕ) : ℝ) ≤ (N : ℝ)/(b^2 : ℕ) from Nat.cast_div_le)
    _ = (N : ℝ)*(∑ b ∈ Ioc U N, 1/(b : ℝ)^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ (N : ℝ)*(1/(U : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_squares_tail hU N) (Nat.cast_nonneg _)
    _ = _ := by ring

noncomputable def pairLargeSquareSet (α : ℝ) (U N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n =>
    n ∈ largeSquareSet U N ∨ floorMul α n ∈ largeSquareSet U (floorMul α N)

lemma pairLargeSquareSet_subset (α : ℝ) (U N : ℕ) :
    pairLargeSquareSet α U N ⊆ Ioc 0 N := filter_subset _ _

theorem pairLargeSquareSet_card_le {α : ℝ} (hα : 1 ≤ α) {U : ℕ}
    (hU : 0 < U) (N : ℕ) :
    ((pairLargeSquareSet α U N).card : ℝ) ≤ ((N : ℝ)+floorMul α N)/U := by
  classical
  let s := (Ioc 0 N).filter fun n => floorMul α n ∈ largeSquareSet U (floorMul α N)
  have hs : s.card ≤ (largeSquareSet U (floorMul α N)).card := by
    apply card_le_card_of_injOn (floorMul α)
    · intro n hn
      change n ∈ s at hn
      exact (mem_filter.mp hn).2
    · exact (floorMul_strictMono hα).injective.injOn
  have hsub : pairLargeSquareSet α U N ⊆ largeSquareSet U N ∪ s := by
    intro n hn
    obtain ⟨hn, h⟩ := mem_filter.mp hn
    rcases h with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, h⟩)
  have hc := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left hs _))
  have hcR : ((pairLargeSquareSet α U N).card : ℝ) ≤
      (largeSquareSet U N).card+(largeSquareSet U (floorMul α N)).card := by exact_mod_cast hc
  exact hcR.trans ((add_le_add (largeSquareSet_card_le hU N)
    (largeSquareSet_card_le hU (floorMul α N))).trans_eq (add_div _ _ _).symm)

#print axioms proper_prime_power_has_large_square
#print axioms largeSquareSet_card_le
#print axioms pairLargeSquareSet_card_le
end Erdos972LargeSquareDivisors
