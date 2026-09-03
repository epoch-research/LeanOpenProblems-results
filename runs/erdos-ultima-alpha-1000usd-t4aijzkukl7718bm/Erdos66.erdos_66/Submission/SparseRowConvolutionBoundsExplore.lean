import Submission.TruncatedConvolutionAlgebraExplore

/-! Pointwise convolution bounds for a sparse insertion profile dominated by
constant-height interval rows in the central part of each target. -/
namespace Erdos66SparseRowConvolutionBounds
open AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66ClampedPrefixContinuation Erdos66TruncatedConvolutionAlgebra
  Erdos66BoundaryPairMean
open scoped Classical
set_option maxHeartbeats 3400000

lemma central_rows_bound (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (q : ℕ → ℝ) (n m : ℕ) (J : Finset ℕ) (a b : ℕ → ℕ) (c : ℕ → ℝ)
    (hc : ∀ j∈J, 0 ≤ c j)
    (hj : ∀ j∈J, m ≤ a j ∧ a j ≤ b j ∧ b j ≤ n+1-m)
    (hm : 2*m ≤ n+1)
    (hq : ∀ i∈Finset.Ico m (n+1-m), q i ≤ ∑ j∈J, if i∈Finset.Ico (a j) (b j) then c j else 0) :
    (∑ i∈Finset.Ico m (n+1-m), q i*indicator A (n-i)) ≤
      profile m*(∑ j∈J, c j*(b j-a j : ℕ))+2*∑ j∈J, c j := by
  have hs : (∑ i∈Finset.Ico m (n+1-m), q i*indicator A (n-i)) ≤
      ∑ j∈J, c j*∑ i∈Finset.Ico (a j) (b j), indicator A (n-i) := by
    calc
      _ ≤ ∑ i∈Finset.Ico m (n+1-m),
          (∑ j∈J, if i∈Finset.Ico (a j) (b j) then c j else 0)*indicator A (n-i) :=
        Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_right (hq i hi) (indicator_nonneg A _))
      _ = _ := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj'
        simp_rw [ite_mul,zero_mul]
        rw [←Finset.sum_filter]
        have he : (Finset.Ico m (n+1-m)).filter (fun i ↦ i∈Finset.Ico (a j) (b j))=
            Finset.Ico (a j) (b j) := by
          ext i
          have hh := hj j hj'
          simp only [Finset.mem_filter,Finset.mem_Ico]
          omega
        rw [he,←Finset.mul_sum]
  have hb : (∑ j∈J, c j*∑ i∈Finset.Ico (a j) (b j), indicator A (n-i)) ≤
      ∑ j∈J, c j*((b j-a j : ℕ)*profile m+2) := by
    apply Finset.sum_le_sum
    intro j hj'
    have hh := hj j hj'
    exact mul_le_mul_of_nonneg_left
      (reflected_interval_occupancy A hbr n m (a j) (b j) hh.2.1 (by omega) (by omega)) (hc j hj')
  calc
    _ ≤ _ := hs.trans hb
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · apply Finset.sum_congr rfl
        intro j _
        ring

lemma central_self_bound (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (C : ℝ)
    (hC : 0 ≤ C) (hqp : ∀ i, q i ≤ C*profile i) (n m : ℕ) (hm : 2*m ≤ n+1) :
    (∑ i∈Finset.Ico m (n+1-m), q i*q (n-i)) ≤ C*profile m*mass q (n+1) := by
  calc
    _ ≤ ∑ i∈Finset.Ico m (n+1-m), C*profile m*q i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      have hp := (hqp (n-i)).trans (mul_le_mul_of_nonneg_left (profile_antitone (by omega : m ≤ n-i)) hC)
      nlinarith only [mul_le_mul_of_nonneg_left hp (hq i)]
    _ ≤ ∑ i∈Finset.range (n+1), C*profile m*q i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi ↦ Finset.mem_range.mpr (by have := Finset.mem_Ico.mp hi; omega))
        (fun i _ _ ↦ mul_nonneg (mul_nonneg hC (profile_nonneg m)) (hq i))
    _ = _ := by rw [←Finset.mul_sum]; rfl

lemma mixed_three_parts_bound (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (q : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hqp : ∀ i, q i ≤ C*profile i)
    (n d : ℕ) (hd : 2 ≤ d) :
    sumConv q (indicator A) n ≤ 2*C*boundaryMean d n+8*C+
      ∑ i∈Finset.Ico (n/d^2) (n+1-n/d^2), q i*indicator A (n-i) := by
  let m := n/d^2
  have hm : 2*m ≤ n := quotient_half d n hd
  have hleft : (∑ i∈Finset.range m, q i*indicator A (n-i)) ≤ C*(boundaryMean d n+4) := by
    calc
      _ ≤ ∑ i∈Finset.range m, (C*profile i)*indicator A (n-i) :=
        Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (hqp i) (indicator_nonneg A _))
      _ = C*∑ i∈Finset.range m, profile i*indicator A (n-i) := by rw [Finset.mul_sum]; simp only [mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (boundary_profile_indicator A hbr n m (by omega)) hC
  have hright : (∑ i∈Finset.range m, indicator A i*q (n-i)) ≤ C*(boundaryMean d n+4) := by
    calc
      _ ≤ ∑ i∈Finset.range m, indicator A i*(C*profile (n-i)) :=
        Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hqp (n-i)) (indicator_nonneg A _))
      _ = C*∑ i∈Finset.range m, indicator A i*profile (n-i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (boundary_indicator_profile A hbr n m) hC
  rw [sumConv_three_parts q (indicator A) n m (by omega)]
  change _ ≤ 2*C*boundaryMean d n+8*C+∑ i∈Finset.Ico m (n+1-m), q i*indicator A (n-i)
  linarith

lemma self_three_parts_bound (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i)
    (C : ℝ) (hC : 0 ≤ C) (hqp : ∀ i, q i ≤ C*profile i)
    (n d : ℕ) (hd : 2 ≤ d) :
    sumConv q q n ≤ 2*C^2*boundaryMean d n+C*profile (n/d^2)*mass q (n+1) := by
  let m := n/d^2
  have hm : 2*m ≤ n := quotient_half d n hd
  have hb : (∑ i∈Finset.range m, q i*q (n-i)) ≤ C^2*boundaryMean d n := by
    calc
      _ ≤ ∑ i∈Finset.range m, (C*profile i)*(C*profile (n-i)) :=
        Finset.sum_le_sum (fun i _ ↦ mul_le_mul (hqp i) (hqp (n-i)) (hq _) (mul_nonneg hC (profile_nonneg _)))
      _ = _ := by
        rw [boundaryMean,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [sumConv_three_parts q q n m (by omega)]
  have hc := central_self_bound q hq C hC hqp n m (by omega)
  change _ ≤ 2*C^2*boundaryMean d n+C*profile m*mass q (n+1)
  linarith

end Erdos66SparseRowConvolutionBounds
