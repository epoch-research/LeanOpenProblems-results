import Submission.GcdProfileCovariance
import Submission.MovingCenteredRows

/-! One-prime divisibility rows and their nonlinear gcd-profile covariances.
All analytic hypotheses concern only the already developed one-prime rows. -/
namespace Erdos972PrimeGcdRows

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972WeightedBeattyRows Erdos972ChebyshevRowMean
open Erdos972GcdProfileCovariance Erdos972GcdProfileExpansion Erdos972LipschitzLogWeights
open Erdos972LogarithmicCovariance

lemma sum_divisibility_row (f : ℕ → ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ Ioc 0 N, if d ∣ n then f n else 0) = ∑ k ∈ Ioc 0 (N/d), f (d*k) := by
  rw [← sum_filter]
  apply sum_bij' (fun n _ => n/d) (fun k _ => d*k)
  · intro n hn
    obtain ⟨hnI, hdn⟩ := mem_filter.mp hn
    have hn0 := (mem_Ioc.mp hnI).1
    apply mem_Ioc.mpr
    refine ⟨Nat.div_pos (Nat.le_of_dvd hn0 hdn) hd,
      Nat.div_le_div_right (mem_Ioc.mp hnI).2⟩
  · intro k hk
    apply mem_filter.mpr
    exact ⟨mem_Ioc.mpr ⟨Nat.mul_pos hd (mem_Ioc.mp hk).1,
      (Nat.mul_le_mul_left d (mem_Ioc.mp hk).2).trans (Nat.mul_div_le N d)⟩, dvd_mul_right _ _⟩
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  · intro k _
    exact Nat.mul_div_cancel_left k hd
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

lemma rowMean_endpoint {β y : ℝ} (hβ : 1 ≤ β) (hy : 1 ≤ y) (L : ℕ)
    (hlo : β*L ≤ y) (hhi : y ≤ β*((L:ℝ)+1)) :
    |rowMean β L-Chebyshev.psi y/β| ≤ 2*Real.log y := by
  have hβ0 : 0 < β := by linarith
  have hm := Chebyshev.psi_mono hlo
  rw [rowMean, ← sub_div, abs_div, abs_of_pos hβ0, abs_of_nonpos (sub_nonpos.mpr hm)]
  apply (div_le_iff₀ hβ0).mpr
  have hh := psi_interval_upper (mul_nonneg hβ0.le (Nat.cast_nonneg L)) hlo hy
  have hlog := Real.log_nonneg hy
  have hlen : y-β*L+1 ≤ 2*β := by nlinarith only [hhi, hβ]
  have hk := mul_le_mul_of_nonneg_right hlen hlog
  nlinarith only [hh, hk]

/-- Unlike the arc formulation, this row is indexed by the input cutoff.
All its divisors share the same prefix function rowMean alpha. -/
theorem prime_divisor_prefix_error {α E : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hE : 0 ≤ E) {N d j : ℕ} (hN : 0 < N) (hd : 0 < d) (hj : j ≤ N)
    (hrow : ∀ Q ≤ floorMul (α*d) (N/d),
      |outputRow (α*d) (fun q => Λ q) Q-(1/(α*d))*Chebyshev.psi Q| ≤ E) :
    |(∑ n ∈ Ioc 0 j, if d ∣ n then Λ (floorMul α n) else 0)-rowMean α j/d| ≤
      E+2*Real.log (α*N) := by
  have hα0 : 0 < α := by linarith
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hβ : 1 < α*d := by nlinarith only [hα, hd1]
  have hlogN : 0 ≤ Real.log (α*N) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le hα.le (by exact_mod_cast hN))
  by_cases hj0 : j = 0
  · simp only [hj0, Ioc_self, sum_empty, rowMean_zero, zero_div, sub_self, abs_zero]
    positivity
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hlo : (α*d)*(j/d:ℕ) ≤ α*j := by
    have hh : (d:ℝ)*(j/d:ℕ) ≤ j := by exact_mod_cast Nat.mul_div_le j d
    nlinarith only [mul_le_mul_of_nonneg_left hh hα0.le]
  have hhi : α*j ≤ (α*d)*((j/d:ℕ)+1) := by
    have hh : (j:ℝ) ≤ (d:ℝ)*((j/d:ℕ)+1) := by exact_mod_cast (Nat.lt_mul_div_succ j hd).le
    nlinarith only [mul_le_mul_of_nonneg_left hh hα0.le]
  have hy : 1 ≤ α*j := one_le_mul_of_one_le_of_one_le hα.le (by exact_mod_cast hjpos)
  have hend := rowMean_endpoint hβ.le hy (j/d) hlo hhi
  have hQ : floorMul (α*d) (j/d) ≤ floorMul (α*d) (N/d) :=
    (floorMul_strictMono hβ.le).monotone (Nat.div_le_div_right hj)
  have hR := hrow _ hQ
  have he : (1/(α*d))*Chebyshev.psi (floorMul (α*d) (j/d)) = rowMean (α*d) (j/d) := by
    rw [rowMean, floorMul, Erdos972RealLogCenter.psi_floor]
    ring
  rw [he] at hR
  have htarget : rowMean α j/d = Chebyshev.psi (α*j)/(α*d) := by rw [rowMean, div_div]
  rw [sum_divisibility_row _ j hd]
  have hfun (k : ℕ) : floorMul α (d*k) = floorMul (α*d) k := by simp only [floorMul, Nat.cast_mul, mul_assoc]
  simp_rw [hfun]
  rw [weightedRow_eq_outputRow hβ (hI.mul_natCast hd.ne'), htarget]
  have ht := abs_sub_le (outputRow (α*d) (fun q => Λ q) (floorMul (α*d) (j/d)))
    (rowMean (α*d) (j/d)) (Chebyshev.psi (α*j)/(α*d))
  have hlogs : Real.log (α*j) ≤ Real.log (α*N) := Real.log_le_log (by positivity)
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj) hα0.le)
  linarith only [ht, hR, hend, hlogs]

/-- A genuine signed covariance estimate for any of the finite nonlinear
profiles. The modulus F and its inversion cost remain explicit. -/
theorem prime_gcd_covariance_bound {α E : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hE : 0 ≤ E) {F N : ℕ} (hF : F ≠ 0) (hN : 0 < N)
    (Φ : ℕ → ℝ → ℝ) {H L : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ r ∈ F.divisors, ∀ x y, |Φ r x-Φ r y| ≤ L*|x-y|)
    (hend : ∀ r ∈ F.divisors, |Φ r (Real.log N)| ≤ H)
    (hrows : ∀ d ∈ F.divisors, ∀ Q ≤ floorMul (α*d) (N/d),
      |outputRow (α*d) (fun q => Λ q) Q-(1/(α*d))*Chebyshev.psi Q| ≤ E) :
    |covariance N (gcdWeight F Φ) (fun n => Λ (floorMul α n))| ≤
      L*centeredMeanBudget (rowMean α) 1 N+
      (H+L*Real.log N)*(profileCost F*(E+2*Real.log (α*N)+7)+E+2*Real.log (α*N)) := by
  have hα0 : 0 < α := by linarith
  have hy : 0 < α*N := by positivity
  have hX : |rowMean α N/N| ≤ 7 := by
    rw [rowMean, div_div, abs_of_nonneg (psi_ratio_bounds hy).1]
    exact (psi_ratio_bounds hy).2
  have hh := gcd_covariance_bound hF hN Φ (fun n => Λ (floorMul α n)) (rowMean α)
    (rowMean_zero α) hL hΦ hend hX (c := 1) (by
      intro d hd j hj
      exact prime_divisor_prefix_error hα hI hE hN (Nat.pos_of_mem_divisors hd) hj (hrows d hd))
  convert hh using 1; ring

#print axioms prime_divisor_prefix_error
#print axioms prime_gcd_covariance_bound

end Erdos972PrimeGcdRows
