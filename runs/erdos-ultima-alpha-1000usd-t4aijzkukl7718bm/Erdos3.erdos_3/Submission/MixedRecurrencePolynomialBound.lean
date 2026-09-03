import Submission.PolynomialDimensionMixedRecurrence

/-! An explicit polynomial bound on the dimension dependence of simultaneous
mixed-degree recurrence. The exponent in dimension is 5K for degree bound K. -/
namespace Erdos3MixedRecurrencePolynomialBound
open Erdos3PolynomialDimensionTorusRecurrence Erdos3PolynomialDimensionMixedRecurrence
  Erdos3LatticeHeightDescent Erdos3SharpHigherPhaseWeylInverse
set_option maxHeartbeats 4000000

def degreeCoefficient (k : ℕ) : ℕ := 2592*sharpWeylConstant k+360+(k+1).factorial

lemma tuple_constant_polynomial (k m : ℕ) :
    tupleRecurrenceConstant k m ≤ degreeCoefficient k*(m+1)^5 := by
  let p := m+1
  have hbase : baseWeylCost k m ≤ 36*sharpWeylConstant k*p^2 := by
    unfold baseWeylCost
    calc
      _ ≤ sharpWeylConstant k*(9*p)*(4*p) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by dsimp only [p]; omega)) (by dsimp only [p]; omega)
      _ = _ := by ring
  have hrest : 6*m+10 ≤ 10*p^2 := by dsimp only [p]; nlinarith
  have hA : 2*baseWeylCost k m+6*m+10 ≤ (72*sharpWeylConstant k+10)*p^2 := by
    nlinarith only [hbase,hrest]
  have hK : m^2+2*m+36 ≤ 36*p^2 := by dsimp only [p]; nlinarith
  have hprod := Nat.mul_le_mul hA hK
  have hp4 : 1 ≤ p^4 := Nat.one_le_pow _ _ (by dsimp only [p]; omega)
  have hfact : (k+1).factorial ≤ (k+1).factorial*p^4 := by
    simpa only [mul_one] using Nat.mul_le_mul_left (k+1).factorial hp4
  have hsum : (2*baseWeylCost k m+6*m+10)*(m^2+2*m+36)+(k+1).factorial ≤
      degreeCoefficient k*p^4 := by
    unfold degreeCoefficient
    nlinarith only [hprod,hfact]
  calc
    _ ≤ p*(degreeCoefficient k*p^4) := Nat.mul_le_mul (by dsimp only [p]; omega) hsum
    _ = _ := by change p*(degreeCoefficient k*p^4) = degreeCoefficient k*p^5; ring

def mixedDegreeCoefficient : ℕ → ℕ
  | 0 => 0
  | K+1 => mixedDegreeCoefficient K*((K+1)*degreeCoefficient K+1)+degreeCoefficient K

lemma mixed_constant_polynomial (K m : ℕ) :
    mixedTupleConstant K m ≤ mixedDegreeCoefficient K*(m+1)^(5*K) := by
  induction K with
  | zero => simp [mixedTupleConstant,mixedDegreeCoefficient]
  | succ K ih =>
    let p := m+1
    have hp : 1 ≤ p := by dsimp only [p]; omega
    have hp5 : 1 ≤ p^5 := Nat.one_le_pow _ _ hp
    have hC : tupleRecurrenceConstant K m ≤ degreeCoefficient K*p^5 := tuple_constant_polynomial K m
    have hfactor : (K+1)*tupleRecurrenceConstant K m+1 ≤ ((K+1)*degreeCoefficient K+1)*p^5 := by
      nlinarith only [Nat.mul_le_mul_left (K+1) hC,hp5]
    have hnew : tupleRecurrenceConstant K m ≤ degreeCoefficient K*p^(5*(K+1)) :=
      hC.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < p) (by omega)))
    rw [mixedTupleConstant,mixedDegreeCoefficient]
    calc
      _ ≤ (mixedDegreeCoefficient K*p^(5*K))*(((K+1)*degreeCoefficient K+1)*p^5)+
          degreeCoefficient K*p^(5*(K+1)) := Nat.add_le_add (Nat.mul_le_mul ih hfactor) hnew
      _ = _ := by
        change _ = (mixedDegreeCoefficient K*((K+1)*degreeCoefficient K+1)+degreeCoefficient K)*p^(5*(K+1))
        rw [show 5*(K+1) = 5*K+5 by ring,pow_add]
        ring

/-- A simultaneous recurrence bound polynomial in the number of phases, for
any fixed positive maximum degree. -/
theorem polynomial_dimension_mixed_recurrence {I : Type*} [Fintype I]
    (K : ℕ) (e : I → ℕ) (he : ∀ i, 0 < e i ∧ e i ≤ K)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (s : ℕ) :
    ∃ d : ℕ, 0 < d ∧
      d ≤ 2^(mixedDegreeCoefficient K*(Fintype.card I+1)^(5*K)*(s+1)) ∧
      ∀ i, ‖(v i)^(d^(e i))-1‖ ≤ (1/2:ℝ)^s := by
  obtain ⟨d,hd,hdb,hrec⟩ := simultaneous_mixed_degrees K e he v hv s
  exact ⟨d,hd,hdb.trans (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.mul_le_mul_right (s+1) (mixed_constant_polynomial K (Fintype.card I)))),hrec⟩

#print axioms polynomial_dimension_mixed_recurrence
end Erdos3MixedRecurrencePolynomialBound
