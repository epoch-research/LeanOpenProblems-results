import Submission.ReciprocalDivisorCounts
import Submission.GrowingTypeI

/-! Uniform joint moments of small-divisor polynomials on the same scales as
the one-prime Type-I estimates. These do not estimate the four-factor remainder. -/
namespace Erdos972DivisorCovariance

open Finset Filter ArithmeticFunction Classical
open scoped Topology
open Erdos972PrimePowerError Erdos972DivisorPairCount Erdos972ReciprocalDivisorCounts
open Erdos972PolynomialRowScales Erdos972CenteredRowScales Erdos972WeightedPrimeRotation Erdos972BeattyRows
open Erdos972ExponentialSum

noncomputable def divisorPolynomial (D : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 D, if d ∣ n then a d else 0

noncomputable def divisorMean (D : ℕ) (a : ℕ → ℝ) : ℝ := ∑ d ∈ Ioc 0 D, a d/d
noncomputable def coefficientMass (D : ℕ) (a : ℕ → ℝ) : ℝ := ∑ d ∈ Ioc 0 D, |a d|

lemma polynomial_pair_expansion (α : ℝ) (N D E : ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 N, divisorPolynomial D a n*divisorPolynomial E b (floorMul α n)) =
      ∑ d ∈ Ioc 0 D, ∑ e ∈ Ioc 0 E, a d*b e*(divisorPairs α N d e).card := by
  have hterm (n : ℕ) : divisorPolynomial D a n*divisorPolynomial E b (floorMul α n) =
      ∑ d ∈ Ioc 0 D, ∑ e ∈ Ioc 0 E, if d ∣ n ∧ e ∣ floorMul α n then a d*b e else 0 := by
    simp only [divisorPolynomial, sum_mul_sum]
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro e he
    split_ifs <;> simp_all
  simp only [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [← sum_filter]
  simp only [divisorPairs, floorMul, sum_const, nsmul_eq_mul]
  ring

lemma polynomial_pair_error (α : ℝ) (N D E : ℕ) (a b : ℕ → ℝ) (B : ℝ)
    (hlocal : ∀ d ∈ Ioc 0 D, ∀ e ∈ Ioc 0 E,
      |((divisorPairs α N d e).card : ℝ)-(N : ℝ)/(d*e)| ≤ B) :
    |(∑ n ∈ Ioc 0 N, divisorPolynomial D a n*divisorPolynomial E b (floorMul α n))-
      (N : ℝ)*divisorMean D a*divisorMean E b| ≤ B*coefficientMass D a*coefficientMass E b := by
  have he : (∑ n ∈ Ioc 0 N, divisorPolynomial D a n*divisorPolynomial E b (floorMul α n))-
      (N : ℝ)*divisorMean D a*divisorMean E b =
      ∑ d ∈ Ioc 0 D, ∑ e ∈ Ioc 0 E, a d*b e*((divisorPairs α N d e).card-(N : ℝ)/(d*e)) := by
    rw [polynomial_pair_expansion]
    simp only [divisorMean, mul_sum, sum_mul]
    rw [sum_comm (s := Ioc 0 E) (t := Ioc 0 D), ← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro e he
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Ioc 0 D, ∑ e ∈ Ioc 0 E, B*|a d| * |b e| := by
      apply sum_le_sum
      intro d hd
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro e he
      rw [abs_mul, abs_mul]
      have hh := mul_le_mul_of_nonneg_left (hlocal d hd e he) (mul_nonneg (abs_nonneg (a d)) (abs_nonneg (b e)))
      exact hh.trans_eq (by ring)
    _ = _ := by
      simp only [coefficientMass, sum_mul, mul_sum]
      exact sum_comm

/-- Partial summation with any fixed power of the logarithm. -/
lemma logPower_prefix_approx (a : ℕ → ℝ) (ρ E : ℝ) (N k : ℕ)
    (hE : ∀ j ≤ N, |(∑ n ∈ Ioc 0 j, a n)-ρ*j| ≤ E) :
    |(∑ n ∈ Ioc 0 N, (Real.log n)^k*a n)-ρ*(∑ n ∈ Ioc 0 N, (Real.log n)^k)| ≤
      2*(Real.log N)^k*E := by
  have hE0 : 0 ≤ E := by simpa using hE 0 (Nat.zero_le N)
  by_cases hN : N = 0
  · simp only [hN, Ioc_self, sum_empty, mul_zero, sub_self, abs_zero]
    positivity
  let w := fun n : ℕ => (Real.log (n+1 : ℕ))^k
  let z := fun n : ℕ => a (n+1)-ρ
  have hw : Monotone w := by
    intro i j hij
    exact pow_le_pow_left₀ (Real.log_natCast_nonneg _) (monotone_log_natCast (Nat.add_le_add_right hij 1)) k
  have hp (j : ℕ) : (∑ n ∈ range j, z n) = (∑ n ∈ Ioc 0 j, a n)-ρ*j := by
    simp only [z, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      sum_Ioc_zero_eq_sum_range_succ]
    ring
  have hh := norm_monotone_weighted_prefix w hw (by dsimp [w]; positivity [Real.log_natCast_nonneg (0+1)])
    z N E (by intro j hj; rw [hp, Real.norm_eq_abs]; exact hE j hj)
  dsimp only [w] at hh
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hN)] at hh
  have he : (∑ n ∈ Ioc 0 N, (Real.log n)^k*a n)-ρ*(∑ n ∈ Ioc 0 N, (Real.log n)^k) =
      ∑ n ∈ range N, (Real.log (n+1 : ℕ))^k • z n := by
    simp only [sum_Ioc_zero_eq_sum_range_succ, smul_eq_mul, z, mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  simpa only [he, Real.norm_eq_abs] using hh

lemma logPower_polynomial_pair_error (α : ℝ) (N D E k : ℕ) (a b : ℕ → ℝ) (B : ℝ)
    (hlocal : ∀ j ≤ N, ∀ d ∈ Ioc 0 D, ∀ e ∈ Ioc 0 E,
      |((divisorPairs α j d e).card : ℝ)-(j : ℝ)/(d*e)| ≤ B) :
    |(∑ n ∈ Ioc 0 N, (Real.log n)^k*(divisorPolynomial D a n*divisorPolynomial E b (floorMul α n)))-
      (divisorMean D a*divisorMean E b)*(∑ n ∈ Ioc 0 N, (Real.log n)^k)| ≤
        2*(Real.log N)^k*(B*coefficientMass D a*coefficientMass E b) := by
  apply logPower_prefix_approx
  intro j hj
  have hh := polynomial_pair_error α j D E a b B (hlocal j hj)
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

/-- Prime-output arc estimates and ordinary joint-divisor estimates are
simultaneously available, at arbitrarily large common rational scales. -/
theorem exists_joint_prime_divisor_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 4*α ≤ u ∧ 2048 ≤ root64 u ∧
      (∀ m : ℕ, 0 < m → m ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
        |mangoldtArcSum (1/(α*m)) (-rowArcLeft (α*m)) (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) X-
          (1/(α*m))*Chebyshev.psi X| ≤ polynomialRowError u (root64 u)) ∧
      (∀ d e : ℕ, 0 < d → 0 < e → e ≤ root64 u → ∀ X ≤ scaleCutoff α u,
        |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤ 118*(root64 u : ℝ)*(u : ℝ)^4) := by
  let C := max B (⌈4*α⌉₊+1)
  obtain ⟨u, v, r, hu, hv, hvu, huv, rfl, hr, hlo, hhi, hrows⟩ :=
    exists_polynomial_beatty_arc_scale_data hα hI C
  have hu0 : 0 < u := (Nat.zero_le C).trans_lt hu
  have hαu : 4*α ≤ u := (Nat.le_ceil _).trans (by
    exact_mod_cast (Nat.le_succ ⌈4*α⌉₊).trans ((le_max_right B _).trans hu.le))
  have hv0 : 0 < root64 u := by omega
  refine ⟨u, (le_max_left B _).trans_lt hu, hαu, hv, hrows, ?_⟩
  intro d e hd he hev X hX
  apply reciprocal_scale_divisor_prefix_bound hα.le r hr hu0 hv0 hαu hlo hhi _ hd he hev
  have hα0 : 0 < α := by linarith
  have hh : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
  have hXR : (X : ℝ) ≤ scaleCutoff α u := Nat.cast_le.mpr hX
  have hh' := (le_div_iff₀ hα0).mp (hXR.trans hh)
  nlinarith only [hh']

/-- Even after summing the joint error over a square of small-divisor indices,
any fixed logarithmic loss is harmless at the chosen scales. -/
theorem squared_family_divisor_error_tendsto (k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)^3*(1+Real.log u)^k/(u : ℝ)^2) atTop (𝓝 0) := by
  have hh := root64_log_div_tendsto 1 (by norm_num) k
  simp only [one_mul] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  obtain ⟨hv, hvu, _⟩ := root64_bounds hu
  have hv0 : (0 : ℝ) < root64 u := Nat.cast_pos.mpr hv
  have hvsq : (root64 u)^2 ≤ u := (Nat.pow_le_pow_right hv (by norm_num : 2 ≤ 64)).trans hvu
  have hv4 : (root64 u : ℝ)^4 ≤ (u : ℝ)^2 := by
    have hcast : (root64 u : ℝ)^2 ≤ u := by exact_mod_cast hvsq
    convert pow_le_pow_left₀ (by positivity) hcast 2 using 1 <;> ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [Real.log_natCast_nonneg u])]
  apply (div_le_div_iff₀ (sq_pos_of_pos hu0) hv0).mpr
  have hm := mul_le_mul_of_nonneg_right hv4 (pow_nonneg (show 0 ≤ 1+Real.log u by positivity [Real.log_natCast_nonneg u]) k)
  nlinarith only [hm]

#print axioms exists_joint_prime_divisor_scale
#print axioms logPower_polynomial_pair_error
#print axioms squared_family_divisor_error_tendsto

end Erdos972DivisorCovariance
