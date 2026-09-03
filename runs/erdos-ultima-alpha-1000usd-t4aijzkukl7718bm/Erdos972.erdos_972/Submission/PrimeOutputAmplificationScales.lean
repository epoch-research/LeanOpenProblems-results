import Submission.WeightedDivisorAmplification
import Submission.PrimeGcdRows
import Submission.PrimeCovarianceObstruction

/-! Actual irrational good scales for weighted divisor amplification.
The amplified signed sum is not estimated by the comparison proved here. -/
namespace Erdos972PrimeOutputAmplificationScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972WeightedDivisorAmplification Erdos972PrimeGcdRows
open Erdos972PrimePowerError Erdos972ChebyshevRowMean Erdos972CenteredRowScales
open Erdos972CovarianceScaleBudgets Erdos972CommonCovarianceScales
open Erdos972PolynomialRowScales Erdos972WeightedBeattyRows
open Erdos972PrimeCovarianceObstruction Erdos972DivisorCovariance

set_option maxHeartbeats 1500000

noncomputable def outputWeight (α : ℝ) (n : ℕ) : ℝ := Λ (floorMul α n)

lemma exists_large_prime_harmonicMass (C : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧ C < harmonicMass P := by
  classical
  by_contra! h
  apply not_summable_one_div_on_primes
  apply summable_of_sum_le (c := C)
  · intro n
    exact Set.indicator_nonneg (fun n _ => by positivity) n
  · intro s
    have hh := h (s.filter Nat.Prime) (fun p hp => (mem_filter.mp hp).2)
    simpa only [harmonicMass, sum_filter, Set.indicator_apply, Set.mem_setOf_eq] using hh

noncomputable def outputRowBudget (α : ℝ) (u : ℕ) : ℝ :=
  polynomialRowError u (root64 u) + 2 * Real.log (α * scaleCutoff α u) + 7

/-- The established one-prime estimates supply arbitrarily small relative
errors for any fixed finite collection of input divisors. -/
theorem exists_small_output_rows {α η : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hη : 0 < η) (M B : ℕ) :
    ∃ N : ℕ, ∃ X E : ℝ, B < N ∧ 0 ≤ X ∧ X ≤ 7 * N ∧
      0 ≤ E ∧ E ≤ η * N ∧
      ∀ d : ℕ, 0 < d → d ≤ M →
        |divisorRow (Ioc 0 N) (outputWeight α) d - X / d| ≤ E := by
  have hlim : Tendsto (fun u => outputRowBudget α u / scaleCutoff α u)
      atTop (𝓝 0) := output_row_error_budget_tendsto hα.le
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_bound_of_scaled_limit hα.le (outputRowBudget α) hlim hη).and
      (root64_tendsto.eventually_ge_atTop M))
  obtain ⟨u, hu, hαu, hv, hrows, _⟩ := exists_joint_prime_divisor_scale hα hI (max B T)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith
  have huN := (scaleCutoff_bounds hα.le hu0 hαu').1
  have hN : 0 < scaleCutoff α u := hu0.trans_le huN
  obtain ⟨hbudget, hM⟩ := hT u ((le_max_right B T).trans hu.le)
  have hα0 : 0 < α := by linarith
  have hy : 1 ≤ α * scaleCutoff α u :=
    one_le_mul_of_one_le_of_one_le hα.le (by exact_mod_cast hN)
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hX0 : 0 ≤ rowMean α (scaleCutoff α u) :=
    div_nonneg (Chebyshev.psi_nonneg _) hα0.le
  have hX7 : rowMean α (scaleCutoff α u) ≤ 7 * scaleCutoff α u := by
    unfold rowMean
    apply (div_le_iff₀ hα0).mpr
    have hh := psi_le_seven_mul (show 0 ≤ α * scaleCutoff α u by positivity)
    nlinarith only [hh]
  refine ⟨scaleCutoff α u, rowMean α (scaleCutoff α u), outputRowBudget α u,
    ((le_max_left B T).trans_lt hu).trans_le huN, hX0, hX7, ?_, hbudget, ?_⟩
  · unfold outputRowBudget
    positivity [Real.log_nonneg hy]
  · intro d hd hdM
    have hh := prime_divisor_prefix_error hα hI hE0 hN hd
      (j := scaleCutoff α u) le_rfl (by
        intro Q hQ
        rw [outputRow_mangoldt]
        exact hrows d hd (hdM.trans hM) Q
          (hQ.trans (scaleCutoff_row_eligible hα.le u d (scaleCutoff α u / d) le_rfl)))
    change |(∑ n ∈ Ioc 0 (scaleCutoff α u),
      if d ∣ n then Λ (floorMul α n) else 0) - rowMean α (scaleCutoff α u) / d| ≤ _
    exact hh.trans (by unfold outputRowBudget; linarith)

lemma amplification_numeric {C A H X E K N ε : ℝ}
    (hH : 0 < H) (hN : 0 ≤ N) (hε : 0 < ε)
    (hX : 0 ≤ X) (hX7 : X ≤ 7*N) (hE : 0 ≤ E) (hEN : E ≤ N)
    (hEc : 4*E*K^2 ≤ H*N) (hεH : 64 ≤ ε^2*H)
    (hbound : (H*C-A)^2 ≤ (X+E)*(X*H+4*E*K^2)) :
    |C-A/H| ≤ ε*N := by
  have hfirst : X+E ≤ 8*N := by linarith
  have hsecond : X*H+4*E*K^2 ≤ 8*H*N := by nlinarith only [hEc, mul_le_mul_of_nonneg_right hX7 hH.le]
  have hsec0 : 0 ≤ X*H+4*E*K^2 := by positivity
  have hb := hbound.trans (mul_le_mul hfirst hsecond hsec0 (by positivity : 0 ≤ 8*N))
  have hident : H^2*(C-A/H)^2 = (H*C-A)^2 := by field_simp
  have hsq : (C-A/H)^2 ≤ (ε*N)^2 := by
    apply le_of_mul_le_mul_left (a := H^2) _ (sq_pos_of_pos hH)
    rw [hident]
    have hh := mul_le_mul_of_nonneg_right hεH (mul_nonneg hH.le (sq_nonneg N))
    nlinarith only [hb, hh]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hε.le hN)).mp
  simpa only [sq_abs] using hsq

/-- For every fixed irrational slope and tolerance there is a fixed finite
prime amplifier which works at arbitrarily large actual good scales, uniformly
for all bounded source coefficients. This is a replacement estimate, not
cancellation of the amplified signed sum. -/
theorem exists_prime_amplifier_comparison {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧ 0 < harmonicMass P ∧
      ∀ B : ℕ, ∃ N : ℕ, B < N ∧ ∀ b : ℕ → ℝ, (∀ n ∈ Ioc 0 N, |b n| ≤ 1) →
        |(∑ n ∈ Ioc 0 N, outputWeight α n * b n) -
          (∑ p ∈ P, divisorRow (Ioc 0 N) (fun n => outputWeight α n * b n) p) /
            harmonicMass P| ≤ ε * N := by
  obtain ⟨P, hP, hHP⟩ := exists_large_prime_harmonicMass (64 / ε^2)
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  have hH : 0 < harmonicMass P := (by positivity : 0 < 64 / ε^2).trans hHP
  have hεH : 64 ≤ ε^2 * harmonicMass P := by
    have hh := (div_lt_iff₀ hε2).mp hHP
    nlinarith only [hh]
  let R := P.sup (fun n => n) + 1
  have hR : 0 < R := by dsimp [R]; omega
  have hpR (p : ℕ) (hp : p ∈ P) : p ≤ R :=
    (show p ≤ P.sup (fun n => n) from le_sup (f := fun n : ℕ => n) hp).trans (Nat.le_succ _)
  let η : ℝ := min 1 (harmonicMass P / (4*((P.card : ℝ)^2+1)))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηc : 4*η*(P.card : ℝ)^2 ≤ harmonicMass P := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*((P.card : ℝ)^2+1))).mp
      (min_le_right (1 : ℝ) (harmonicMass P / (4*((P.card : ℝ)^2+1))))
    nlinarith only [hh, hη.le]
  refine ⟨P, hP, hH, ?_⟩
  intro B
  obtain ⟨N, X, E, hBN, hX0, hX7, hE0, hEη, hrows⟩ :=
    exists_small_output_rows hα hI hη (R^2) B
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hEN : E ≤ N := hEη.trans (by nlinarith only [mul_le_mul_of_nonneg_right hη1 hN0])
  have hEc : 4*E*(P.card : ℝ)^2 ≤ harmonicMass P * N := by
    have h₁ := mul_le_mul_of_nonneg_right hEη (by positivity : 0 ≤ 4*(P.card : ℝ)^2)
    have h₂ := mul_le_mul_of_nonneg_right hηc hN0
    nlinarith only [h₁, h₂]
  have hRR : R ≤ R^2 := Nat.le_self_pow (by omega : 2 ≠ 0) R
  have hrow1 : |divisorRow (Ioc 0 N) (outputWeight α) 1-X| ≤ E := by
    simpa only [Nat.cast_one, div_one] using hrows 1 (by norm_num) ((show 1 ≤ R from hR).trans hRR)
  have hrowp (p : ℕ) (hp : p ∈ P) :=
    hrows p (hP p hp).pos ((hpR p hp).trans hRR)
  have hrowpq (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      |divisorRow (Ioc 0 N) (outputWeight α) (p.lcm q)-X/(p.lcm q)| ≤ E := by
    apply hrows _ (Nat.lcm_pos (hP p hp).pos (hP q hq).pos)
    calc
      p.lcm q ≤ p*q := Nat.lcm_le_mul (hP p hp).pos (hP q hq).pos
      _ ≤ R*R := Nat.mul_le_mul (hpR p hp) (hpR q hq)
      _ = R^2 := by ring
  refine ⟨N, hBN, ?_⟩
  intro b hb
  have hc := amplification_rows_sq (Ioc 0 N) P (outputWeight α) b
    (fun n _ => vonMangoldt_nonneg) hb hP hX0 hE0 hrow1 hrowp hrowpq
  exact amplification_numeric hH hN0 hε hX0 hX7 hE0 hEN hEc hεH hc

#print axioms exists_small_output_rows
#print axioms exists_prime_amplifier_comparison

end Erdos972PrimeOutputAmplificationScales
