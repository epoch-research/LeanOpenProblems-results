import Submission.PrimeRoughOutputs
import Submission.SieveBarrier

/-! Numerical limits of the specific uniform row estimates currently
available. These are not impossibility theorems for all sieve methods, and
are not a disproof of the original prime-pair conjecture. -/
namespace Erdos972LowerSieveCutoff

open Erdos972PrimeRoughOutputs Erdos972PrimePowerError
open Erdos972GrowingCoprimeCandidates Erdos972PolynomialRowScales
open Erdos972ScaledPrimeRows Erdos972PrimeRotation

set_option maxHeartbeats 1000000

/-- At the existing sixth scale, every sifting radius whose full lower-test
modulus range fits inside root64(u) is below the output primality threshold. -/
theorem available_level_below_primality {α : ℝ} (hα : 1 ≤ α)
    {u R Z : ℕ} (hu : 2 ≤ u) (hR : 1 ≤ R) (hlevel : R^2*Z ≤ root64 u) :
    (Z+1)^2 ≤ floorMul α (u^6) := by
  have hZ : Z ≤ u :=
    ((Nat.le_mul_of_pos_left Z (Nat.pow_pos hR)).trans hlevel).trans (root64_le_self u)
  have hfloor : u^6 ≤ floorMul α (u^6) := by
    unfold floorMul
    apply Nat.le_floor
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hα
  calc
    (Z+1)^2 ≤ (u+1)^2 := Nat.pow_le_pow_left (Nat.add_le_add_right hZ 1) 2
    _ ≤ (u^2)^2 := Nat.pow_le_pow_left (by nlinarith only [hu]) 2
    _ = u^4 := by rw [← pow_mul]
    _ ≤ u^6 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ _ := hfloor

/-- In particular the size condition in prime_of_coprime_factorial_of_lt_square
cannot be instantiated from this modulus range at N=u^6. -/
theorem not_available_square_root_sieve {α : ℝ} (hα : 1 ≤ α)
    {u R Z : ℕ} (hu : 2 ≤ u) (hR : 1 ≤ R) (hlevel : R^2*Z ≤ root64 u) :
    ¬ floorMul α (u^6) < (Z+1)^2 :=
  not_lt_of_ge (available_level_below_primality hα hu hR hlevel)

lemma scaledRowError_ge_level (K : ℕ) {u v : ℕ} (hv : 1 ≤ v) (hvu : v ≤ u) :
    (v:ℝ) ≤ scaledRowError K u v := by
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have hv1 : (1:ℝ) ≤ v := by exact_mod_cast hv
  have hu1 : (1:ℝ) ≤ u := by exact_mod_cast hv.trans hvu
  have huR : (0:ℝ) < u := lt_of_lt_of_le (by norm_num) hu1
  have hpow : (v:ℝ)^4 ≤ (u:ℝ)^6 := by
    exact (pow_le_pow_left₀ hvR.le (Nat.cast_le.mpr hvu) 4).trans
      (pow_le_pow_right₀ hu1 (by decide : 4 ≤ 6))
  have hcoef : 1 ≤ (28+rotationConstant (256*K))*(1+Real.log u)^5 := by
    have hC : 1 ≤ 28+rotationConstant (256*K) := by linarith only [rotationConstant_pos (256*K)]
    have hL : 1 ≤ 1+Real.log u := by linarith only [Real.log_natCast_nonneg u]
    exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hL)
  calc
    (v:ℝ) = (v:ℝ)^4/(v:ℝ)^3 := by field_simp
    _ ≤ (u:ℝ)^6/(v:ℝ)^3 := div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ ((28+rotationConstant (256*K))*(1+Real.log u)^5)*((u:ℝ)^6/(v:ℝ)^3) :=
      le_mul_of_one_le_left (by positivity) hcoef
    _ = _ := by unfold scaledRowError; ring

/-- Uniformity in prefixes does not mean that the same absolute error is
small on short prefixes. The positive lower-sieve budget fails whenever
X<=v^2 for this row-error formula. -/
theorem square_prefix_exceeds_error_budget (K : ℕ) {u v X : ℕ}
    (hv : 1 ≤ v) (hvu : v ≤ u) (hX : X ≤ v^2) :
    ¬ scaledRowError K u v ≤ (X:ℝ)/(16*v) := by
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have hE := scaledRowError_ge_level K hv hvu
  intro hbudget
  have hh := (le_div_iff₀ (show 0 < 16*(v:ℝ) by positivity)).mp hbudget
  have hX' := Nat.cast_le (α := ℝ).mpr hX
  rw [Nat.cast_pow] at hX'
  have hl := mul_le_mul_of_nonneg_right hE (show 0 ≤ 16*(v:ℝ) by positivity)
  nlinarith only [hh, hX', hl, sq_pos_of_pos hvR]

#print axioms available_level_below_primality
#print axioms square_prefix_exceeds_error_budget

end Erdos972LowerSieveCutoff
