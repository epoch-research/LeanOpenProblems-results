import Submission.SimultaneousAvoidanceFrequency
import Submission.SharpHigherPhaseWeylInverse
import Submission.PhaseIntegerLinear

/-! Failure of simultaneous monomial recurrence gives a bounded nonzero integer
relation with the natural N^-degree approximation scale. This is a relation
certificate, not yet a dimension-reduction recurrence theorem. -/
namespace Erdos3PolynomialRecurrenceObstruction
open Finset Erdos3HigherPhaseDifferences Erdos3SharpHigherPhaseWeylInverse
  Erdos3SimultaneousAvoidanceFrequency Erdos3PhaseIntegerLinear
  Erdos3QuadraticRecurrenceAverages
open scoped BigOperators Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

def avoidanceMeanExponent (m t : ℕ) : ℕ := m*(2*t+2*m+3)+2

def avoidanceRelationExponent (k m t : ℕ) : ℕ :=
  sharpWeylConstant k*(avoidanceMeanExponent m t+1)+(k+1).factorial+2*t+2*m+3

/-- If no n in [1,N] simultaneously returns a tuple of degree-(k+1) monomial
phases within 2^-t of 1, there is a nonzero bounded integer relation among the
coefficients with chord error O_{k,m,t}(N^-(k+1)). -/
theorem polynomial_recurrence_obstruction (k m t N : ℕ) (hm : 0 < m)
    (z : Fin m → Additive Circle)
    (hN : 2^(sharpWeylConstant k*(avoidanceMeanExponent m t+1)) ≤ N)
    (havoid : ∀ n : ℕ, 0 < n → n ≤ N → ∃ j, (1/2 : ℝ)^t ≤
      ‖(phase (z j))^(n^(k+1))-1‖) :
    ∃ h : Fin m → ℤ, (∃ j, h j ≠ 0) ∧
      (∀ j, |h j| ≤ (2^(avoidanceRelationExponent k m t) : ℕ)) ∧
      ‖phase (∑ j, h j • z j)-1‖ ≤
        (2 : ℝ)^(sharpWeylConstant k*(avoidanceMeanExponent m t+1))/(N : ℝ)^(k+1) := by
  let K := 2^(2*t+3)*m
  let s := avoidanceMeanExponent m t
  let B := sharpWeylConstant k*(s+1)
  have hN0 : 0 < N := (Nat.two_pow_pos _).trans_le hN
  have hK : 0 < K := Nat.mul_pos (Nat.two_pow_pos _) hm
  letI : NeZero N := ⟨by omega⟩
  letI : NeZero m := ⟨by omega⟩
  have hε : 0 < (1/2 : ℝ)^t := pow_pos (by norm_num) _
  have hscale : 8*(m : ℝ) ≤ (K : ℝ)*((1/2 : ℝ)^t)^2 := by
    have he : (K : ℝ)*((1/2 : ℝ)^t)^2 = 8*(m : ℝ) := by
      dsimp only [K]
      push_cast
      rw [show 2*t+3=t*2+3 by omega,pow_add,pow_mul,div_pow,one_pow]
      field_simp
      ring
    exact he.ge
  let v : Fin N → Fin m → ℂ := fun n j ↦ (phase (z j))^((n.val+1)^(k+1))
  have hv : ∀ n j, ‖v n j‖ = 1 := by intro n j; simp only [v,norm_pow,phase_norm,one_pow]
  have hav : ∀ n : Fin N, ∃ j, (1/2 : ℝ)^t ≤ ‖v n j-1‖ := by
    intro n
    exact havoid (n.val+1) (by omega) (by omega)
  obtain ⟨h,hne,hbound,hfreq⟩ := simultaneous_avoidance_frequency hm hK v hv hε hscale hav
  have hL : m*K ≤ 2^(2*t+2*m+3) := by
    have hmm : m ≤ 2^m := Nat.lt_two_pow_self.le
    calc
      _ ≤ 2^(2*t+3)*(2^m)^2 := by
        have hh := Nat.pow_le_pow_left hmm 2
        have hh' := Nat.mul_le_mul_left (2^(2*t+3)) hh
        dsimp only [K]
        nlinarith only [hh']
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  have hfreqden : 4*(m*K)^m ≤ 2^s := by
    calc
      _ ≤ 4*(2^(2*t+2*m+3))^m := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hL m)
      _ = _ := by
        rw [show 4=2^2 by norm_num,← pow_mul,← pow_add]
        congr 1
        dsimp only [s,avoidanceMeanExponent]
        ring
  have hδfreq : (1/2 : ℝ)^s ≤ 1/(4*((m : ℝ)*(K : ℝ))^m) := by
    rw [div_pow,one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hfreqden
  let z₀ : Additive Circle := ∑ j, h j • z j
  let f : ℕ → Additive Circle := fun n ↦ ((n+1)^(k+1)) • z₀
  let ztop := (k+1).factorial • z₀
  have hf : diffIter (k+1) f = fun _ ↦ ztop := by
    funext n
    calc
      _ = diffIter (k+1) (fun n : ℕ ↦ (n^(k+1)) • z₀) (n+1) :=
        fwdDiff_iter_comp_add 1 _ 1 (k+1) n
      _ = _ := congr_fun (diffIter_monomial z₀ (k+1)) (n+1)
  have hmean : (1/2 : ℝ)^s ≤ ‖intervalMean N (fun n ↦ phase (f n))‖ := by
    have he : (𝔼 n : Fin N, ∏ j, (v n j)^(h j)) = intervalMean N (fun n ↦ phase (f n)) := by
      apply expect_congr rfl
      intro n _
      exact (phase_integer_combination univ h z ((n.val+1)^(k+1))).symm
    rw [he] at hfreq
    exact hδfreq.trans hfreq.le
  obtain ⟨a,ha,haB,hsmall⟩ := sharp_leading_phase_inverse k f ztop hf s N hN hmean
  let h' : Fin m → ℤ := fun j ↦ ((a*(k+1).factorial : ℕ) : ℤ)*h j
  have hane : ((a*(k+1).factorial : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos ha (Nat.factorial_pos _)))
  have hne' : ∃ j, h' j ≠ 0 := by
    obtain ⟨j,hj⟩ := hne
    exact ⟨j,mul_ne_zero hane hj⟩
  have htotal : a*(k+1).factorial*(m*K) ≤ 2^(avoidanceRelationExponent k m t) := by
    have hfac : (k+1).factorial ≤ 2^((k+1).factorial) := Nat.lt_two_pow_self.le
    calc
      _ ≤ (2^B*2^((k+1).factorial))*2^(2*t+2*m+3) :=
        Nat.mul_le_mul (Nat.mul_le_mul haB hfac) hL
      _ = _ := by
        rw [← pow_add,← pow_add]
        congr 1
        dsimp only [B,s,avoidanceRelationExponent]
        omega
  have hbound' (j : Fin m) : |h' j| ≤ (2^(avoidanceRelationExponent k m t) : ℕ) := by
    dsimp only [h']
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    calc
      _ ≤ ((a*(k+1).factorial : ℕ) : ℤ)*(m*K : ℕ) :=
        mul_le_mul_of_nonneg_left (hbound j).le (Int.natCast_nonneg _)
      _ ≤ _ := by exact_mod_cast htotal
  have hrel : (∑ j, h' j • z j) = (a*(k+1).factorial) • z₀ := by
    calc
      _ = ∑ j, (a*(k+1).factorial) • (h j • z j) := by
        apply sum_congr rfl
        intro j _
        dsimp only [h']
        rw [← smul_smul,natCast_zsmul]
      _ = _ := sum_nsmul (univ : Finset (Fin m)) (a*(k+1).factorial) (fun j ↦ h j • z j)
  refine ⟨h',hne',hbound',?_⟩
  rw [hrel,phase_nsmul]
  dsimp only [ztop] at hsmall
  rw [phase_nsmul,← pow_mul,Nat.mul_comm (k+1).factorial a] at hsmall
  exact hsmall

#print axioms polynomial_recurrence_obstruction
end Erdos3PolynomialRecurrenceObstruction
