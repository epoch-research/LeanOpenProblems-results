import Submission.FixedRoughFactorCount
import Submission.MappedSquarefreeDivisorExpansion
import Submission.AsymmetricDiagonalBudget
open Erdos972PrimePowerError Erdos972PrimeAlmostPrime
open Erdos972PrimeRoughOutputs Erdos972GrowingCoprimeCandidates
open Erdos972EfficientPrimeAlmostPrime Erdos972FourthPowerAlmostPrime
open Erdos972MappedSquarefreeDivisorExpansion Erdos972SquarefreeDivisorExpansion
open Erdos972FixedRoughFactorCount
#check floorMul_le_real
#check Nat.cast_pow
#print Erdos972AsymmetricDiagonalBudget.mobiusCutoff
#print Erdos972EfficientSieveScale.fastRoot
example {α : ℝ} (hα : 1 ≤ α) (u : ℕ) :
    (floorMul α (u^6) : ℝ) ≤ α*(u:ℝ)^6 := by
  have hh := floorMul_le_real hα (le_refl (u^6))
  set_option pp.all true in
    trace_state
  rw [Nat.cast_pow] at hh
  exact hh
example (x C L : ℝ) : x/(C*L) = 2*(x/(2*C*L)) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
