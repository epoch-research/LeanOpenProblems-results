import Submission.HigherPartitionParameters
import Submission.PolynomialProgressionThresholds

/-! At fixed degree, number of phases, and accuracy, the new partition
threshold and stride costs are polynomial in the requested progression length. -/
namespace Erdos3HigherPartitionPowerBounds
open Erdos3HigherPartitionParameters Erdos3SimultaneousPolynomialRecurrence
  Erdos3PolynomialProgressionThresholds
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

lemma power_clog_bound (a b M : ℕ) :
    2^(a+b*Nat.clog 2 M)+1 ≤ (2^(a+b)+1)*(M+1)^b := by
  have hp : 1 ≤ (M+1)^b := Nat.one_le_pow _ _ (by omega)
  calc
    _ = 2^a*(2^(Nat.clog 2 M))^b+1 := by
      rw [pow_add,Nat.mul_comm b (Nat.clog 2 M),pow_mul]
    _ ≤ 2^a*(2*(M+1))^b+(M+1)^b := Nat.add_le_add
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (pow_clog_two_le M) b)) hp
    _ = _ := by rw [mul_pow,pow_add]; ring

lemma power_clog_poly (a b : ℕ) : HasPolyBound (fun M ↦ 2^(a+b*Nat.clog 2 M)) b :=
  ⟨2^(a+b)+1,fun M ↦ power_clog_bound a b M⟩

def higherPartitionDegree : ℕ → ℕ → ℕ
  | 0,_ => 1
  | k+1,m => higherPartitionDegree k m*((k+1)*simultaneousPowerConstant (k+1) m+1)

lemma higherPartitionDegree_pos (k m : ℕ) : 0 < higherPartitionDegree k m := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos ih (Nat.succ_pos _)

/-- Both costs are polynomial in the target length. The polynomial coefficients
may depend on degree, phase count, and dyadic accuracy. -/
theorem higher_partition_costs_poly (k m s : ℕ) :
    HasPolyBound (fun L ↦ higherPartitionThreshold k m L s) (higherPartitionDegree k m) ∧
    HasPolyBound (fun L ↦ higherPartitionStride k m L s) (higherPartitionDegree k m) := by
  induction k generalizing s with
  | zero =>
    constructor
    · apply (poly_id.affine (2^s) 0).congr
      intro L
      simp only [Function.id_def,higherPartitionThreshold,Nat.add_zero,Nat.mul_comm]
    · refine ⟨2,?_⟩
      intro L
      simp only [higherPartitionStride,higherPartitionDegree,pow_one]
      omega
  | succ k ih =>
    let C := simultaneousPowerConstant (k+1) m
    let E := higherPartitionDegree k m
    have hM := (ih (s+1)).1
    have hD := (ih (s+1)).2
    have hB : HasPolyBound (fun L ↦ higherTopStride k m L s) (E*((k+1)*C)) := by
      apply ((power_clog_poly (C*(s+2)) ((k+1)*C)).comp hM).congr
      intro L
      unfold higherTopStride higherTopAccuracy higherCoarseLength
      change 2^(C*(s+2)+((k+1)*C)*Nat.clog 2 (higherPartitionThreshold k m L (s+1))) =
        2^(C*(s+1+(k+1)*Nat.clog 2 (higherPartitionThreshold k m L (s+1))+1))
      congr 1
      ring
    change HasPolyBound _ (E*((k+1)*C+1)) ∧ HasPolyBound _ (E*((k+1)*C+1))
    constructor
    · have hp := ((hB.mul hM).affine (2^(s+1)) 0).congr
        (g := fun L ↦ higherPartitionThreshold (k+1) m L s) (fun L ↦ by
          dsimp only
          rw [higherPartitionThreshold_succ]
          simp only [higherCoarseLength,Nat.add_zero]
          ring)
      have he : E*((k+1)*C)+E = E*((k+1)*C+1) := by ring
      rw [he] at hp
      exact hp
    · have hp := (hD.mul hB).congr (g := fun L ↦ higherPartitionStride (k+1) m L s)
        (fun _ ↦ rfl)
      have he : E+E*((k+1)*C) = E*((k+1)*C+1) := by ring
      change HasPolyBound _ (E+E*((k+1)*C)) at hp
      rw [he] at hp
      exact hp

#print axioms higher_partition_costs_poly
end Erdos3HigherPartitionPowerBounds
