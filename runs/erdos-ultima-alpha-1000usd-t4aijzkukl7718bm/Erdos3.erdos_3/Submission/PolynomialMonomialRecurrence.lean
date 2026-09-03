import Submission.HigherPhaseWeylInverse

/-! Polynomial recurrence bounds for monomial unit phases of every positive
fixed degree. This does not assert a higher-order inverse theorem. -/
namespace Erdos3PolynomialMonomialRecurrence
open Finset Metric Erdos3HigherPhaseDifferences Erdos3HigherPhaseWeylInverse
  Erdos3QuadraticRecurrenceExtraction Erdos3QuadraticRecurrenceAverages
  Erdos3LocalQuadraticProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

/-- Index k denotes the positive monomial degree k+1. -/
def powerRecurrenceConstant (k : ℕ) : ℕ :=
  (7*weylConstant k+(k+1).factorial+4)*(k+1)+1

lemma powerRecurrenceConstant_pos (k : ℕ) : 0 < powerRecurrenceConstant k := by
  unfold powerRecurrenceConstant
  omega

/-- For every fixed positive degree, the return-time bound is polynomial in
inverse dyadic accuracy. The bound is uniform in the unit phase. -/
theorem monomial_recurrence (k : ℕ) (v : ℂ) (hv : ‖v‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(powerRecurrenceConstant k*(t+1)) ∧
      ‖v^(d^(k+1))-1‖ ≤ (1/2 : ℝ)^t := by
  let A := 7*weylConstant k+(k+1).factorial+4
  let N := 2^(powerRecurrenceConstant k*(t+1))
  let K := 2^(2*t+4)
  have hN : 0 < N := Nat.two_pow_pos _
  have hK : 0 < K := Nat.two_pow_pos _
  letI : NeZero N := ⟨by omega⟩
  have hε : 0 < (1/2 : ℝ)^t := pow_pos (by norm_num) _
  have hscale : 8 ≤ (K : ℝ)*((1/2 : ℝ)^t)^2 := by
    have hKr : (K : ℝ) = (2 : ℝ)^(t*2)*16 := by
      simp only [K,Nat.cast_pow,Nat.cast_ofNat]
      rw [Nat.mul_comm t 2,pow_add]
      norm_num
    rw [hKr,div_pow,one_pow,pow_mul]
    have hp : (2 : ℝ)^t ≠ 0 := by positivity
    field_simp
    norm_num
  have hB : weylConstant k*((2*t+6)+1) ≤ A*(t+1) := by
    dsimp [A]
    nlinarith only [Nat.zero_le (weylConstant k*t),Nat.zero_le ((k+1).factorial*(t+1))]
  have hAN : A*(t+1) ≤ powerRecurrenceConstant k*(t+1) := by
    apply Nat.mul_le_mul_right
    change A ≤ A*(k+1)+1
    nlinarith only [Nat.zero_le (A*k)]
  by_contra hn
  push_neg at hn
  have havoid (n : Fin N) : (1/2 : ℝ)^t ≤ ‖v^((n.val+1)^(k+1))-1‖ :=
    (hn (n.val+1) (by omega) (by omega)).le
  obtain ⟨q,hq,hqK,hfreq⟩ := avoidance_frequency
    (fun n : Fin N ↦ v^((n.val+1)^(k+1)))
    (fun n ↦ by rw [norm_pow,hv,one_pow]) hε havoid hK hscale
  let z₀ : Additive Circle := Additive.ofMul (⟨v,mem_sphere_zero_iff_norm.mpr hv⟩ : Circle)
  have hz₀ : phase z₀ = v := rfl
  let f : ℕ → Additive Circle := fun n ↦ ((n+1)^(k+1)) • (q • z₀)
  let z : Additive Circle := (k+1).factorial • (q • z₀)
  have hf : diffIter (k+1) f = fun _ ↦ z := by
    funext n
    calc
      _ = diffIter (k+1) (fun n : ℕ ↦ (n^(k+1)) • (q • z₀)) (n+1) :=
        fwdDiff_iter_comp_add 1 _ 1 (k+1) n
      _ = _ := congr_fun (diffIter_monomial (q • z₀) (k+1)) (n+1)
  have hmean : (1/2 : ℝ)^(2*t+6) ≤ ‖intervalMean N (fun n ↦ phase (f n))‖ := by
    have he : 1/(4*(K : ℝ)) = (1/2 : ℝ)^(2*t+6) := by
      simp only [K,Nat.cast_pow,Nat.cast_ofNat,div_pow,one_pow]
      have he : (2 : ℝ)^(2*t+6) = 4*(2 : ℝ)^(2*t+4) := by
        rw [show 2*t+6 = 2+(2*t+4) by omega,pow_add]
        norm_num
      rw [he]
    rw [he] at hfreq
    have hfun : (fun n : Fin N ↦ (v^((n.val+1)^(k+1)))^q) =
        fun n : Fin N ↦ phase (f n.val) := by
      funext n
      simp only [f,phase_nsmul,hz₀,← pow_mul]
      rw [Nat.mul_comm]
    simpa only [hfun,intervalMean] using hfreq.le
  have hNinverse : 2^(weylConstant k*((2*t+6)+1)) ≤ N :=
    Nat.pow_le_pow_right (by decide) (hB.trans hAN)
  obtain ⟨a,ha,hab,hsmall⟩ := leading_phase_inverse k f z hf (2*t+6) N hNinverse hmean
  let d := q*(k+1).factorial*a
  have hd : 0 < d := Nat.mul_pos (Nat.mul_pos hq (Nat.factorial_pos _)) ha
  have hdA : d ≤ 2^(A*(t+1)) := by
    have hfac : (k+1).factorial ≤ 2^((k+1).factorial) := Nat.lt_two_pow_self.le
    calc
      _ ≤ (2^(2*t+4)*2^((k+1).factorial))*2^(weylConstant k*((2*t+6)+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hqK.le hfac) hab
      _ = 2^((2*t+4)+(k+1).factorial+weylConstant k*((2*t+6)+1)) := by rw [← pow_add,← pow_add]
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        dsimp [A]
        nlinarith only [Nat.zero_le (weylConstant k*t),Nat.zero_le ((k+1).factorial*t)]
  have hdN : d ≤ N := hdA.trans (Nat.pow_le_pow_right (by decide) hAN)
  have hsmall' : ‖v^d-1‖ ≤ (2 : ℝ)^(A*(t+1))/(N : ℝ) := by
    have he : (phase z)^a = v^d := by
      simp only [z,phase_nsmul,hz₀,← pow_mul,d]
    rw [he] at hsmall
    exact hsmall.trans (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hB) (Nat.cast_nonneg N))
  have hosc : ‖v^(d^(k+1))-1‖ ≤ ((d : ℝ)^k)*‖v^d-1‖ := by
    have hh := unit_power_oscillation (v^d) (by rw [norm_pow,hv,one_pow]) (d^k)
    simpa only [← pow_mul,← pow_succ',Nat.cast_pow] using hh
  have hdpow : (d : ℝ)^k ≤ (2 : ℝ)^(A*(t+1)*k) := by
    have hh : (d : ℝ) ≤ (2 : ℝ)^(A*(t+1)) := by exact_mod_cast hdA
    simpa only [pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg d) hh k
  have hfinal : ‖v^(d^(k+1))-1‖ ≤ (1/2 : ℝ)^t := by
    calc
      _ ≤ ((d : ℝ)^k)*‖v^d-1‖ := hosc
      _ ≤ (2 : ℝ)^(A*(t+1)*k)*((2 : ℝ)^(A*(t+1))/(N : ℝ)) :=
        mul_le_mul hdpow hsmall' (norm_nonneg _) (pow_nonneg (by norm_num) _)
      _ = (2 : ℝ)^(A*(k+1)*(t+1))/(N : ℝ) := by
        rw [← mul_div_assoc,← pow_add]
        congr 2
        ring
      _ = (1/2 : ℝ)^(t+1) := by
        have hNr : (N : ℝ) = (2 : ℝ)^(A*(k+1)*(t+1)+(t+1)) := by
          simp only [N,Nat.cast_pow,Nat.cast_ofNat]
          congr 1
          change (A*(k+1)+1)*(t+1) = _
          ring
        rw [hNr,pow_add,div_pow,one_pow]
        field_simp
      _ ≤ _ := by rw [pow_succ]; nlinarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) t]
  exact (not_lt_of_ge hfinal) (hn d hd hdN)

#print axioms monomial_recurrence
end Erdos3PolynomialMonomialRecurrence
