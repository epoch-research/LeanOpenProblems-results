import Submission.HigherPhaseDifferences

/-! Integer linear combinations of additive circle phases. -/
namespace Erdos3PhaseIntegerLinear
open Finset Erdos3HigherPhaseDifferences
open scoped BigOperators Classical

lemma phase_zsmul (n : ℤ) (z : Additive Circle) : phase (n • z) = (phase z)^n :=
  Circle.coeHom.map_zpow _ _

lemma phase_sum {I : Type*} (S : Finset I) (z : I → Additive Circle) :
    phase (∑ i ∈ S, z i) = ∏ i ∈ S, phase (z i) := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert a S ha ih => rw [sum_insert ha,prod_insert ha,phase_add,ih]

lemma phase_integer_combination {I : Type*} (S : Finset I) (h : I → ℤ)
    (z : I → Additive Circle) (n : ℕ) :
    phase (n • ∑ j ∈ S, h j • z j) = ∏ j ∈ S, ((phase (z j))^n)^(h j) := by
  rw [phase_nsmul,phase_sum,← prod_pow]
  apply prod_congr rfl
  intro j _
  rw [phase_zsmul]
  simp_rw [← zpow_natCast]
  rw [← zpow_mul,← zpow_mul,mul_comm (h j)]

#print axioms phase_integer_combination
end Erdos3PhaseIntegerLinear
