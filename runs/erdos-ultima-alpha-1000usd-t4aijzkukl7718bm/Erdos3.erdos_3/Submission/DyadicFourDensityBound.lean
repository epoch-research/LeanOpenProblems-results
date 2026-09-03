import Submission.ExplicitProgressionThresholds
import Submission.DyadicFourParameters

/-! A uniform triple-exponential four-term threshold at dyadic density.
This is a quantitative finite theorem, not a reciprocal-summability theorem. -/
namespace Erdos3DyadicFourDensityBound
open Finset Erdos3ExplicitProgressionThresholds Erdos3DyadicFourParameters
  Erdos3PolynomialProgressionThresholds
  Erdos3PolynomialFourDensityBound Erdos3IntegerFourDensityIncrement
  Erdos3IntegerFourDensityBound Erdos3ProgressionIncrementParameters
  Erdos3NormalizedQuadraticInverse Erdos3CyclicIntervalMask
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

lemma interval_step_scale_bound (α : ℝ) {X : ℕ} (hX : 2^100 ≤ X)
    (hD : normalizedRank (intervalUniformityThreshold α)+1 ≤ X)
    (hZ : incrementPrecision (intervalGain α)+2 ≤ X)
    (hdiag : ⌈4096/α^4⌉₊+10 ≤ X) (ℓ : ℕ) :
    intervalStepThreshold α ℓ+1 ≤ X^(1000*X)*(ℓ+1)^(1000*X) := by
  let D := normalizedRank (intervalUniformityThreshold α)
  let e := 69*(2*D+1)
  have hX2 : 2 ≤ X := (by norm_num : 2 ≤ 2^100).trans hX
  have hX1 : 1 ≤ X := by omega
  have hE : 0 < 1000*X := Nat.mul_pos (by decide) (by omega)
  have hXe : X ≤ X^(1000*X) := Nat.le_self_pow (Nat.ne_of_gt hE) X
  have hbase : X ≤ X^(1000*X)*(ℓ+1)^(1000*X) :=
    hXe.trans (le_mul_of_one_le_right (Nat.zero_le _) (Nat.one_le_pow _ _ (by omega)))
  have he : e ≤ 1000*X := by dsimp [e]; change D+1 ≤ X at hD; omega
  have hexp : 500*(D+1)+e ≤ 1000*X := by dsimp [e]; change D+1 ≤ X at hD; omega
  have hL : requestedCyclicLength α ℓ+1 ≤ X*(ℓ+1) :=
    (roundedScale_nat_bound ℓ (intervalGain α)).trans (Nat.mul_le_mul_right _ hZ)
  have hinc : incrementThreshold D (requestedCyclicLength α ℓ) (intervalGain α)+1 ≤
      X^(1000*X)*(ℓ+1)^(1000*X) := by
    calc
      _ ≤ X^(500*(D+1))*(requestedCyclicLength α ℓ+1)^e :=
        incrementThreshold_explicit (intervalGain α) hX hZ hD
      _ ≤ X^(500*(D+1))*(X*(ℓ+1))^e :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL e)
      _ = X^(500*(D+1)+e)*(ℓ+1)^e := by rw [mul_pow,pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right hX1 hexp)
        (Nat.pow_le_pow_right (by omega) he)
  unfold intervalStepThreshold
  rw [← max_add_add_right,← max_add_add_right]
  apply max_le
  · exact (by omega : 8+1 ≤ X).trans hbase
  · exact max_le ((by omega : ⌈4096/α^4⌉₊+1 ≤ X).trans hbase) hinc

/-- A numerical bound for the polynomial iteration with exponentially growing
coefficient and degree. No density theorem is used in this calculation. -/
lemma scale_iteration_triple_bound {h t : ℕ} (hh : 100 ≤ h) (ht : t ≤ 2^h) :
    ((2^h)^(1000*2^h)+2)^((1000*2^h+1)^t) ≤ 2^(2^(2^(4*h))) := by
  generalize hXdef : 2^h = X at ht ⊢
  let E := 1000*X
  have hX1000 : 1000 ≤ X := by
    have hb : 2^100 ≤ 2^h := Nat.pow_le_pow_right (by decide) hh
    rw [hXdef] at hb
    exact (by norm_num : 1000 ≤ 2^100).trans hb
  have hX1 : 1 ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hX3 : 3 ≤ X := by omega
  have hX4 : 4 ≤ X := by omega
  have hhX : h ≤ X := by simpa only [hXdef] using (Nat.lt_two_pow_self (n := h)).le
  have hE0 : 0 < E := by dsimp [E]; omega
  have hE2 : E ≤ X^2 := by
    calc
      _ ≤ X*X := Nat.mul_le_mul_right X hX1000
      _ = _ := (pow_two X).symm
  have hE3 : E+1 ≤ X^3 := by
    have hp : 1 ≤ X^2 := Nat.one_le_pow _ _ hX1
    have hm := Nat.mul_le_mul_right (X^2) hX2
    nlinarith only [hE2,hp,hm]
  have hXle : X ≤ X^E := Nat.le_self_pow (Nat.ne_of_gt hE0) X
  have hhE : h*E+1 ≤ X^4 := by
    have hm : h*E ≤ X*X^2 := Nat.mul_le_mul hhX hE2
    have h3 : 1 ≤ X^3 := Nat.one_le_pow _ _ hX1
    have hmult := Nat.mul_le_mul_right (X^3) hX2
    nlinarith only [hm,h3,hmult]
  have hbase : X^E+2 ≤ 2^(X^4) := by
    calc
      _ ≤ 2*X^E := by omega
      _ = 2^(h*E+1) := by rw [pow_succ,← hXdef,← pow_mul]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hhE
  have hhexp : h*3*X ≤ X^3 := by
    have hm := Nat.mul_le_mul_right (3*X) hhX
    have hx := Nat.mul_le_mul_right (X^2) hX3
    nlinarith only [hm,hx]
  have hexponent : (E+1)^t ≤ 2^(X^3) := by
    calc
      _ ≤ (X^3)^X := (Nat.pow_le_pow_left hE3 t).trans
        (Nat.pow_le_pow_right (Nat.pow_pos (by omega)) ht)
      _ = 2^(h*3*X) := by rw [← hXdef,← pow_mul,← pow_mul]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hhexp
  have h4h : h*4 ≤ X^3 := by
    have hm := Nat.mul_le_mul_right 4 hhX
    have hxx := Nat.mul_le_mul_right X hX4
    have hsq : X^2 ≤ X^3 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3)
    nlinarith only [hm,hxx,hsq]
  have hX4exp : X^4 ≤ 2^(X^3) := by
    calc
      _ = (2^h)^4 := by rw [hXdef]
      _ = 2^(h*4) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) h4h
  have hlast : 2*X^3 ≤ 2^(4*h) := by
    calc
      _ = 2^(3*h+1) := by
        have he : X^3 = 2^(3*h) := by rw [Nat.mul_comm 3 h,pow_mul,hXdef]
        rw [he,pow_succ]
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  change (X^E+2)^((E+1)^t) ≤ _
  calc
    _ ≤ (2^(X^4))^(2^(X^3)) := (Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (Nat.two_pow_pos _) hexponent)
    _ = 2^(X^4*2^(X^3)) := (pow_mul ..).symm
    _ ≤ 2^((2^(X^3))*(2^(X^3))) := Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ hX4exp)
    _ = 2^(2^(2*X^3)) := by rw [← pow_add]; congr 2; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hlast)

/-- Uniform dyadic form of the finite four-term theorem. Its triple exponential
in s corresponds to a double exponential in a fixed power of inverse density. -/
theorem dyadic_four_density_bound : ∃ c : ℕ, 0 < c ∧ ∀ s N : ℕ, ∀ S : Finset ℕ,
    S ⊆ range N → (S : Set ℕ).IsAPOfLengthFree 4 → (1/2 : ℝ)^s ≤ intervalDensity S N →
    N < 2^(2^(2^(c*(s+1)))) := by
  obtain ⟨c,hc,hparameters⟩ := dyadic_four_parameter_bound
  refine ⟨4*c,by omega,?_⟩
  intro s N S hS hfree hden
  obtain ⟨hD,hZ,hT,hdiag⟩ := hparameters s
  have hh : 100 ≤ c*(s+1) := by nlinarith only [hc,Nat.zero_le (c*s)]
  have hX : 2^100 ≤ 2^(c*(s+1)) := Nat.pow_le_pow_right (by decide) hh
  have hstep := interval_step_scale_bound ((1/2 : ℝ)^s) hX hD hZ hdiag
  have hQ := polynomial_iteration_bound
    (intervalStepThreshold ((1/2 : ℝ)^s)) (fourIterationThreshold ((1/2 : ℝ)^s))
    hstep rfl (fun _ ↦ rfl) (fourIterationCount ((1/2 : ℝ)^s))
  have hbound := hQ.trans (scale_iteration_triple_bound hh hT)
  have hN := integer_four_density_bound (pow_pos (by norm_num : (0 : ℝ) < 1/2) s)
    N S hS hfree hden
  change N < fourIterationThreshold ((1/2 : ℝ)^s) (fourIterationCount ((1/2 : ℝ)^s)) at hN
  apply hN.trans_le
  apply (Nat.le_succ _).trans
  simpa only [Nat.mul_assoc] using hbound

#print axioms interval_step_scale_bound
#print axioms scale_iteration_triple_bound
#print axioms dyadic_four_density_bound
end Erdos3DyadicFourDensityBound
