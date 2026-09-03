import Submission.ParameterizedProgressionPartition
import Submission.MixedRecurrencePolynomialBound

/-! Almost-complete polynomial-phase partitions with polynomial dependence on
the number of phases in the logarithmic threshold exponent. -/
namespace Erdos3EfficientPolynomialPartition
open Finset Erdos3ParameterizedPartitionCosts Erdos3ParameterizedProgressionPartition
  Erdos3PolynomialDimensionTorusRecurrence Erdos3MixedRecurrencePolynomialBound
  Erdos3HigherPhaseDifferences Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

def efficientThreshold (k m L s : ℕ) : ℕ :=
  flatThreshold (fun j ↦ tupleRecurrenceConstant j m) k L s

def efficientStride (k m L s : ℕ) : ℕ :=
  flatStride (fun j ↦ tupleRecurrenceConstant j m) k L s

def partitionCoefficient : ℕ → ℕ
  | 0 => 1
  | k+1 => partitionCoefficient k*((k+1)*degreeCoefficient k+1)+degreeCoefficient k+1

def partitionLogBound (k m L s : ℕ) : ℕ :=
  partitionCoefficient k*(m+1)^(5*k)*(s+k+1+Nat.clog 2 L)

lemma partition_exponent_polynomial (k m : ℕ) :
    flatExponent (fun j ↦ tupleRecurrenceConstant j m) k ≤ partitionCoefficient k*(m+1)^(5*k) := by
  induction k with
  | zero => simp [flatExponent,partitionCoefficient]
  | succ k ih =>
    let p := m+1
    have hp : 1 ≤ p := by dsimp only [p]; omega
    have hp5 : 1 ≤ p^5 := Nat.one_le_pow _ _ hp
    have hC : tupleRecurrenceConstant k m ≤ degreeCoefficient k*p^5 := tuple_constant_polynomial k m
    have hfactor : (k+1)*tupleRecurrenceConstant k m+1 ≤ ((k+1)*degreeCoefficient k+1)*p^5 := by
      nlinarith only [Nat.mul_le_mul_left (k+1) hC,hp5]
    have hnew : tupleRecurrenceConstant k m+1 ≤ (degreeCoefficient k+1)*p^(5*(k+1)) := by
      have hh : tupleRecurrenceConstant k m+1 ≤ (degreeCoefficient k+1)*p^5 := by
        nlinarith only [hC,hp5]
      exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < p) (by omega)))
    rw [flatExponent,partitionCoefficient]
    calc
      _ = flatExponent (fun j ↦ tupleRecurrenceConstant j m) k*((k+1)*tupleRecurrenceConstant k m+1)+
          (tupleRecurrenceConstant k m+1) := by omega
      _ ≤ (partitionCoefficient k*p^(5*k))*(((k+1)*degreeCoefficient k+1)*p^5)+
          (degreeCoefficient k+1)*p^(5*(k+1)) := Nat.add_le_add (Nat.mul_le_mul ih hfactor) hnew
      _ = _ := by
        change _ = (partitionCoefficient k*((k+1)*degreeCoefficient k+1)+degreeCoefficient k+1)*p^(5*(k+1))
        rw [show 5*(k+1) = 5*k+5 by ring,pow_add]
        ring

lemma efficientThreshold_bound (k m L s : ℕ) : efficientThreshold k m L s ≤ 2^(partitionLogBound k m L s) :=
  (flatThreshold_exponential_bound _ k L s).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (partition_exponent_polynomial k m)))

lemma efficientThreshold_pos (k m L s : ℕ) (hL : 0 < L) : 0 < efficientThreshold k m L s :=
  flatThreshold_pos _ k L s hL

lemma efficientStride_bound (k m L s : ℕ) (hL : 0 < L) : efficientStride k m L s ≤ 2^(partitionLogBound k m L s) :=
  (flatStride_le_threshold _ k L s hL).trans (efficientThreshold_bound k m L s)

/-- The efficient monomial recurrence theorem supplies an unconditional partition
for arbitrary tuples of globally polynomial circle phases. -/
theorem efficient_polynomial_partition {I : Type*} [Fintype I]
    (k : ℕ) (f : I → ℕ → Additive Circle) (hf : ∀ i, diffIter (k+1) (f i) = 0)
    (N L s : ℕ) (hL : 0 < L) (hN : efficientThreshold k (Fintype.card I) L s ≤ N) :
    ∃ c : Fin N → Option (Fin N), ∃ w : I → Fin N → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧ cellMass c none ≤ (1/2:ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i x.val)-w i j‖ ≤ (1/2:ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ a d : ℕ, 0 < d ∧ d ≤ efficientStride k (Fintype.card I) L s ∧
          (∀ n < L, a+n*d < N) ∧
          ∀ x : Fin N, c x = some j ↔ ∃ n : Fin L, x.val = a+n.val*d := by
  exact polynomial_partition_of_recurrence (fun j ↦ tupleRecurrenceConstant j (Fintype.card I))
    (fun j v hv u ↦ simultaneous_unit_monomial_recurrence v hv j u) k f hf N L s hL hN

/-- Explicit polynomial-dimensional logarithmic cost for the full partition. -/
theorem polynomial_dimension_partition {I : Type*} [Fintype I]
    (k : ℕ) (f : I → ℕ → Additive Circle) (hf : ∀ i, diffIter (k+1) (f i) = 0)
    (N L s : ℕ) (hL : 0 < L) (hN : 2^(partitionLogBound k (Fintype.card I) L s) ≤ N) :
    ∃ c : Fin N → Option (Fin N), ∃ w : I → Fin N → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧ cellMass c none ≤ (1/2:ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i x.val)-w i j‖ ≤ (1/2:ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ a d : ℕ, 0 < d ∧ d ≤ 2^(partitionLogBound k (Fintype.card I) L s) ∧
          (∀ n < L, a+n*d < N) ∧
          ∀ x : Fin N, c x = some j ↔ ∃ n : Fin L, x.val = a+n.val*d := by
  obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := efficient_polynomial_partition k f hf N L s hL
    ((efficientThreshold_bound k (Fintype.card I) L s).trans hN)
  refine ⟨c,w,hw,hbad,hflat,?_⟩
  intro j hj
  obtain ⟨a,d,hd,hdb,hpoints,hfiber⟩ := hgeom j hj
  exact ⟨a,d,hd,hdb.trans (efficientStride_bound k _ L s hL),hpoints,hfiber⟩

#print axioms polynomial_dimension_partition
end Erdos3EfficientPolynomialPartition
