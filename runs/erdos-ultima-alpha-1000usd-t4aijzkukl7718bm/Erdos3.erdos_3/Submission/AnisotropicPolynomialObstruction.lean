import Submission.AnisotropicAvoidanceParameters
import Submission.SharpHigherPhaseWeylInverse
import Submission.PhaseIntegerLinear
import Submission.CircleIntegerApproximation

/-! Anisotropic monomial recurrence obstruction with a short frequency and a
separate denominator. Keeping these separate is essential for volume-controlled
lattice reduction: the denominator must not enlarge the geometric frequency. -/
namespace Erdos3AnisotropicPolynomialObstruction
open Finset Erdos3AnisotropicAvoidanceParameters Erdos3SharpHigherPhaseWeylInverse
  Erdos3HigherPhaseDifferences Erdos3PhaseIntegerLinear
  Erdos3QuadraticRecurrenceAverages Erdos3CircleIntegerApproximation
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

/-- The structural frequency is bounded by kernelPower(t)*2^(t_i+2).
The possibly larger arithmetic denominator is reported separately. -/
theorem anisotropic_polynomial_obstruction {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (t : I → ℕ) (N : ℕ) (z : I → Additive Circle)
    (hN : 2^(sharpWeylConstant k*(frequencyMeanExponent t+1)) ≤ N)
    (havoid : ∀ n : ℕ, 0 < n → n ≤ N → ∃ i, (1/2 : ℝ)^(t i) ≤
      ‖(phase (z i))^(n^(k+1))-1‖) :
    ∃ h : I → ℤ, (∃ i, h i ≠ 0) ∧
      (∀ i, |h i| < (kernelPower t*2^(t i+2) : ℕ)) ∧
      ∃ q : ℕ, 0 < q ∧ q ≤ 2^(sharpWeylConstant k*(frequencyMeanExponent t+1)+(k+1).factorial) ∧
      ‖phase (q • ∑ i, h i • z i)-1‖ ≤
        (2 : ℝ)^(sharpWeylConstant k*(frequencyMeanExponent t+1))/(N : ℝ)^(k+1) := by
  have hN0 : 0 < N := (Nat.two_pow_pos _).trans_le hN
  letI : NeZero N := ⟨by omega⟩
  let v : Fin N → I → ℂ := fun n i ↦ (phase (z i))^((n.val+1)^(k+1))
  have hv : ∀ n i, ‖v n i‖ = 1 := by intro n i; simp only [v,norm_pow,phase_norm,one_pow]
  have hav : ∀ n : Fin N, ∃ i, (1/2 : ℝ)^(t i) ≤ ‖v n i-1‖ := by
    intro n
    exact havoid (n.val+1) (by omega) (by omega)
  obtain ⟨h,hne,hbound,hfreq⟩ := dyadic_anisotropic_avoidance t v hv hav
  let z₀ : Additive Circle := ∑ i, h i • z i
  let f : ℕ → Additive Circle := fun n ↦ ((n+1)^(k+1)) • z₀
  let ztop := (k+1).factorial • z₀
  have hf : diffIter (k+1) f = fun _ ↦ ztop := by
    funext n
    calc
      _ = diffIter (k+1) (fun n : ℕ ↦ (n^(k+1)) • z₀) (n+1) :=
        fwdDiff_iter_comp_add 1 _ 1 (k+1) n
      _ = _ := congr_fun (diffIter_monomial z₀ (k+1)) (n+1)
  have hmean : (1/2 : ℝ)^(frequencyMeanExponent t) ≤ ‖intervalMean N (fun n ↦ phase (f n))‖ := by
    have he : (𝔼 n : Fin N, ∏ i, (v n i)^(h i)) = intervalMean N (fun n ↦ phase (f n)) := by
      apply expect_congr rfl
      intro n _
      exact (phase_integer_combination univ h z ((n.val+1)^(k+1))).symm
    rw [he] at hfreq
    exact hfreq.le
  obtain ⟨a,ha,haB,hsmall⟩ := sharp_leading_phase_inverse k f ztop hf (frequencyMeanExponent t) N hN hmean
  refine ⟨h,hne,hbound,a*(k+1).factorial,Nat.mul_pos ha (Nat.factorial_pos _),?_,?_⟩
  · calc
      _ ≤ 2^(sharpWeylConstant k*(frequencyMeanExponent t+1))*2^((k+1).factorial) :=
        Nat.mul_le_mul haB Nat.lt_two_pow_self.le
      _ = _ := (pow_add ..).symm
  · dsimp only [ztop] at hsmall
    rw [phase_nsmul,← pow_mul,Nat.mul_comm (k+1).factorial a] at hsmall
    simpa only [phase_nsmul] using hsmall

noncomputable def realPhaseHom : ℝ →+ Additive Circle where
  toFun x := Circle.expHom (2*Real.pi*x)
  map_zero' := by simp
  map_add' x y := by rw [mul_add,map_add]

lemma phase_realPhaseHom (x : ℝ) : phase (realPhaseHom x) = ephase x := rfl

lemma phase_real_combination {I : Type*} [Fintype I] (α : I → ℝ) (h : I → ℤ) (q : ℕ) :
    phase (q • ∑ i, h i • realPhaseHom (α i)) = ephase ((q : ℝ)*∑ i, (h i : ℝ)*α i) := by
  have he : (∑ i, h i • realPhaseHom (α i)) = realPhaseHom (∑ i, (h i : ℝ)*α i) := by
    rw [map_sum]
    apply sum_congr rfl
    intro i _
    simpa only [zsmul_eq_mul] using (map_zsmul realPhaseHom (h i) (α i)).symm
  rw [he,← map_nsmul,phase_realPhaseHom,nsmul_eq_mul]

/-- Real-coordinate version, with exact integer correction b. -/
theorem anisotropic_real_obstruction {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (t : I → ℕ) (N : ℕ) (α : I → ℝ)
    (hN : 2^(sharpWeylConstant k*(frequencyMeanExponent t+1)) ≤ N)
    (havoid : ∀ n : ℕ, 0 < n → n ≤ N → ∃ i, (1/2 : ℝ)^(t i) ≤
      ‖ephase (((n^(k+1) : ℕ) : ℝ)*α i)-1‖) :
    ∃ h : I → ℤ, (∃ i, h i ≠ 0) ∧
      (∀ i, |h i| < (kernelPower t*2^(t i+2) : ℕ)) ∧
      ∃ q : ℕ, ∃ b : ℤ, 0 < q ∧
      q ≤ 2^(sharpWeylConstant k*(frequencyMeanExponent t+1)+(k+1).factorial) ∧
      |(q : ℝ)*(∑ i, (h i : ℝ)*α i)-(b : ℝ)| ≤
        (2 : ℝ)^(sharpWeylConstant k*(frequencyMeanExponent t+1))/(N : ℝ)^(k+1) := by
  have hav : ∀ n : ℕ, 0 < n → n ≤ N → ∃ i, (1/2 : ℝ)^(t i) ≤
      ‖(phase (realPhaseHom (α i)))^(n^(k+1))-1‖ := by
    simpa only [phase_realPhaseHom,ephase_pow] using havoid
  obtain ⟨h,hne,hbound,q,hq,hqB,hsmall⟩ := anisotropic_polynomial_obstruction
    k t N (fun i ↦ realPhaseHom (α i)) hN hav
  rw [phase_real_combination] at hsmall
  obtain ⟨b,hb⟩ := exists_integer_near ((q : ℝ)*∑ i, (h i : ℝ)*α i)
  refine ⟨h,hne,hbound,q,b,hq,hqB,hb.trans ?_⟩
  exact (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 4)).trans hsmall

#print axioms anisotropic_polynomial_obstruction
#print axioms anisotropic_real_obstruction
end Erdos3AnisotropicPolynomialObstruction
