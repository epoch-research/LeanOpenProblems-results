import Submission.SharpReciprocalPrimeCost
import Submission.PrimeAlmostPrime

/-! A larger polynomial roughness radius made possible by the sharp
reciprocal prime cost and the squared Selberg coefficient budget. -/
namespace Erdos972EfficientSieveScale

open Filter
open scoped Topology
open Erdos972PolynomialRowScales Erdos972PrimePowerError

set_option maxHeartbeats 1500000
set_option exponentiation.threshold 8192

def fastRoot (u : ℕ) : ℕ := root64 (root64 u)

lemma le_fastRoot_iff (Z u : ℕ) : Z ≤ fastRoot u ↔ Z^4096 ≤ u := by
  simp only [fastRoot, le_root64_iff, ← pow_mul, Nat.reduceMul]

lemma fastRoot_tendsto : Tendsto fastRoot atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (B^4096)] with u hu
  exact (le_fastRoot_iff B u).mpr hu

lemma fastRoot_power_level (u : ℕ) : (fastRoot u)^64 ≤ root64 u := by
  exact (le_root64_iff (fastRoot u) (root64 u)).mp le_rfl

lemma fastRoot_eligible {u : ℕ} (hu : 0 < u) :
    1 ≤ fastRoot u ∧ ((fastRoot u)^16)^3*fastRoot u ≤ root64 u := by
  have hZ : 1 ≤ fastRoot u := (le_fastRoot_iff 1 u).mpr (by simpa using hu)
  refine ⟨hZ, ?_⟩
  calc
    _ = (fastRoot u)^49 := by rw [← pow_mul, ← pow_succ]
    _ ≤ (fastRoot u)^64 := Nat.pow_le_pow_right hZ (by decide)
    _ ≤ _ := fastRoot_power_level u

lemma fastRoot_upper {u : ℕ} (hZ : 2 ≤ fastRoot u) : u ≤ (fastRoot u)^8192 := by
  have hu : u < (fastRoot u+1)^4096 := by
    apply Nat.lt_of_not_ge
    intro h
    have hh := (le_fastRoot_iff (fastRoot u+1) u).mpr h
    omega
  have hz : fastRoot u+1 ≤ (fastRoot u)^2 := by nlinarith only [hZ]
  calc
    u ≤ (fastRoot u+1)^4096 := hu.le
    _ ≤ ((fastRoot u)^2)^4096 := Nat.pow_le_pow_left hz _
    _ = _ := by rw [← pow_mul]

lemma fast_floor_output_power_bound {α : ℝ} {p u : ℕ} (hα : α ≤ fastRoot u)
    (hZ : 2 ≤ fastRoot u) (hp : p ≤ u^6) :
    floorMul α p ≤ (fastRoot u)^49153 := by
  have hfloor : floorMul α p ≤ fastRoot u*p := by
    unfold floorMul
    have hh := Nat.floor_mono (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) p))
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using hh
  have hscale : u^6 ≤ (fastRoot u)^49152 := by
    have hh := Nat.pow_le_pow_left (fastRoot_upper hZ) 6
    simpa only [← pow_mul, Nat.reduceMul] using hh
  calc
    _ ≤ fastRoot u*p := hfloor
    _ ≤ fastRoot u*(fastRoot u)^49152 := Nat.mul_le_mul_left _ (hp.trans hscale)
    _ = _ := by rw [← pow_succ']

#print axioms fastRoot_eligible
#print axioms fast_floor_output_power_bound

end Erdos972EfficientSieveScale
