import Submission.DyadicPrimeReciprocals

/-! The reciprocal mass of multiplicatively comparable prime pairs has a
uniform vanishing tail. -/

namespace Erdos371
namespace FiniteSieve
open Finset

def primesAbovePower (A D : ℕ) : Finset ℕ :=
  (D+1).primesBelow.filter fun p => 2^A ≤ p

lemma mem_primesAbovePower {A D p : ℕ} :
    p ∈ primesAbovePower A D ↔ p.Prime ∧ 2^A ≤ p ∧ p ≤ D := by
  simp only [primesAbovePower, mem_filter, Nat.mem_primesBelow, Nat.lt_succ_iff]
  tauto

lemma ordered_prime_row_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (C L k q : ℕ) (hC : C ≤ 2^L) (hk : 0 < k)
    (hql : 2^k ≤ q) (hqu : q < 2^(k+1)) :
    (∑ p ∈ S, if q ≤ p ∧ p ≤ C*q then (1 : ℝ)/p else 0) ≤ 4*(L+1 : ℝ)/k := by
  rw [← sum_filter]
  have h := prime_band_reciprocal_le (S.filter fun p => q ≤ p ∧ p ≤ C*q) k (k+L) hk (by
    intro p hp
    obtain ⟨hp,hqp,hpC⟩ := mem_filter.mp hp
    refine ⟨hS p hp,hql.trans hqp,?_⟩
    calc
      p ≤ C*q := hpC
      _ ≤ 2^L*q := Nat.mul_le_mul_right q hC
      _ < 2^L*2^(k+1) := Nat.mul_lt_mul_of_pos_left hqu (by positivity)
      _ = 2^(k+L+1) := by rw [← pow_add]; congr 1; omega)
  simpa only [show k+L+1-k = L+1 by omega, Nat.cast_add, Nat.cast_one] using h

noncomputable def orderedPrimeMass (C A D : ℕ) : ℝ :=
  ∑ q ∈ primesAbovePower A D, ∑ p ∈ primesAbovePower A D,
    if q ≤ p ∧ p ≤ C*q then (1 : ℝ)/((p : ℝ)*q) else 0

lemma reciprocal_sq_Icc_le (A M : ℕ) (hA : 0 < A) :
    (∑ k ∈ Icc A M, ((k : ℝ)^2)⁻¹) ≤ 2/(A : ℝ) := by
  have hs : Icc A M = Ioo (A-1) (M+1) := by ext k; simp only [mem_Icc,mem_Ioo]; omega
  rw [hs]
  have h := sum_Ioo_inv_sq_le (α := ℝ) (A-1) (M+1)
  simpa only [Nat.cast_sub hA, Nat.cast_one, sub_add_cancel] using h

lemma orderedPrimeMass_bound (C L A D : ℕ) (hC : C ≤ 2^L) (hA : 0 < A) :
    orderedPrimeMass C A D ≤ 32*(L+1 : ℝ)/A := by
  let S := primesAbovePower A D
  have hmap : ∀ q ∈ S, Nat.log 2 q ∈ Icc A (Nat.log 2 D) := by
    intro q hq
    obtain ⟨hqp,hAq,hqD⟩ := mem_primesAbovePower.mp hq
    exact mem_Icc.mpr ⟨(Nat.le_log_iff_pow_le (by decide : 1 < 2) hqp.ne_zero).mpr hAq,
      Nat.log_mono_right hqD⟩
  change (∑ q ∈ S, ∑ p ∈ S, if q ≤ p ∧ p ≤ C*q then (1 : ℝ)/((p : ℝ)*q) else 0) ≤ _
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ k ∈ Icc A (Nat.log 2 D), (16*(L+1 : ℝ))*((k : ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro k hk
      have hk0 : 0 < k := hA.trans_le (mem_Icc.mp hk).1
      have hrow (q : ℕ) (hq : q ∈ S.filter fun q => Nat.log 2 q = k) :
          (∑ p ∈ S, if q ≤ p ∧ p ≤ C*q then (1 : ℝ)/((p : ℝ)*q) else 0) ≤
            (4*(L+1 : ℝ)/k)*(1/(q : ℝ)) := by
        obtain ⟨hq,hqk⟩ := mem_filter.mp hq
        have hqprime := (mem_primesAbovePower.mp hq).1
        have hdyadic := (mem_dyadicPrimeSet.mp ((dyadicPrimeSet_eq_log_fiber hqprime).mpr hqk))
        have h := ordered_prime_row_bound S (fun p hp => (mem_primesAbovePower.mp hp).1)
          C L k q hC hk0 hdyadic.2.1 hdyadic.2.2
        have h' := mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ 1/q by positivity)
        convert h' using 1
        rw [sum_mul]
        apply sum_congr rfl
        intro p hp
        split_ifs <;> ring
      calc
        _ ≤ ∑ q ∈ S with Nat.log 2 q = k, (4*(L+1 : ℝ)/k)*(1/(q : ℝ)) := sum_le_sum hrow
        _ = (4*(L+1 : ℝ)/k) * (∑ q ∈ S with Nat.log 2 q = k, (1 : ℝ)/q) := by rw [mul_sum]
        _ ≤ (4*(L+1 : ℝ)/k) * (4/(k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)).trans (dyadicPrimeSet_reciprocal_le k hk0)
          intro q hq
          obtain ⟨hq,hqk⟩ := mem_filter.mp hq
          exact (dyadicPrimeSet_eq_log_fiber (mem_primesAbovePower.mp hq).1).mpr hqk
        _ = _ := by ring
    _ = 16*(L+1 : ℝ) * (∑ k ∈ Icc A (Nat.log 2 D), ((k : ℝ)^2)⁻¹) := by rw [mul_sum]
    _ ≤ 16*(L+1 : ℝ)*(2/(A : ℝ)) :=
      mul_le_mul_of_nonneg_left (reciprocal_sq_Icc_le A _ hA) (by positivity)
    _ = _ := by ring

noncomputable def comparablePrimeMass (C A D : ℕ) : ℝ :=
  ∑ p ∈ primesAbovePower A D, ∑ q ∈ primesAbovePower A D,
    if p ≤ C*q ∧ q ≤ C*p then (1 : ℝ)/((p : ℝ)*q) else 0

/-- This bound is uniform in the upper prime cutoff. -/
theorem comparablePrimeMass_bound (C L A D : ℕ) (hC : C ≤ 2^L) (hA : 0 < A) :
    comparablePrimeMass C A D ≤ 64*(L+1 : ℝ)/A := by
  have hswap : (∑ p ∈ primesAbovePower A D, ∑ q ∈ primesAbovePower A D,
      if p ≤ q ∧ q ≤ C*p then (1 : ℝ)/((p : ℝ)*q) else 0) = orderedPrimeMass C A D := by
    unfold orderedPrimeMass
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    simp only [mul_comm]
  have hsame : (∑ p ∈ primesAbovePower A D, ∑ q ∈ primesAbovePower A D,
      if q ≤ p ∧ p ≤ C*q then (1 : ℝ)/((p : ℝ)*q) else 0) = orderedPrimeMass C A D := by
    rw [sum_comm]
    rfl
  have hsplit : comparablePrimeMass C A D ≤ orderedPrimeMass C A D + orderedPrimeMass C A D := by
    conv_rhs => lhs; rw [← hswap]
    conv_rhs => rhs; rw [← hsame]
    unfold comparablePrimeMass
    simp only [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro q hq
    by_cases hc : p ≤ C*q ∧ q ≤ C*p
    · rw [if_pos hc]
      rcases le_total p q with h | h
      · rw [if_pos (show p ≤ q ∧ q ≤ C*p from ⟨h,hc.2⟩)]
        exact le_add_of_nonneg_right (by split_ifs <;> positivity)
      · rw [if_pos (show q ≤ p ∧ p ≤ C*q from ⟨h,hc.1⟩)]
        exact le_add_of_nonneg_left (by split_ifs <;> positivity)
    · rw [if_neg hc]
      apply add_nonneg <;> split_ifs <;> positivity
  have h := orderedPrimeMass_bound C L A D hC hA
  convert hsplit.trans (add_le_add h h) using 1; ring

#print axioms comparablePrimeMass_bound
end FiniteSieve
end Erdos371
