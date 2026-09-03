import Submission.SelbergLowerTest
import Submission.GrowingCoprimeCandidates

/-! Prime inputs with outputs avoiding all primes up to a fixed power root
of the input scale. This is an almost-prime result, not prime output. -/
namespace Erdos972PrimeRoughOutputs

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SelbergWeights Erdos972SelbergLowerMain Erdos972SelbergLowerTest
open Erdos972GrowingCoprimeCandidates Erdos972PrimePowerError
open Erdos972DualPrimeRows Erdos972ScaledPrimeRows Erdos972PolynomialRowScales
open Erdos972ChebyshevPNT Erdos972PrimeRotation Erdos972InverseGoodApproximation

set_option maxHeartbeats 5000000
set_option exponentiation.threshold 8192

noncomputable def primeWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

lemma primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight n := by
  unfold primeWeight
  split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

lemma inputDivisorRow_prime_error (α : ℝ) (d N : ℕ) :
    0 ≤ inputDivisorRow α d N-row (Ioc 0 N) primeWeight (floorMul α) d ∧
      inputDivisorRow α d N-row (Ioc 0 N) primeWeight (floorMul α) d ≤
        Chebyshev.psi N-Chebyshev.theta N := by
  have he : inputDivisorRow α d N-row (Ioc 0 N) primeWeight (floorMul α) d =
      ∑ n ∈ Ioc 0 N, if d ∣ floorMul α n ∧ ¬n.Prime then vonMangoldt n else 0 := by
    simp only [inputDivisorRow, row, primeWeight, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    by_cases hd : d ∣ floorMul α n <;> by_cases hp : n.Prime <;>
      simp [hd, hp, vonMangoldt_apply_prime]
  rw [he]
  constructor
  · apply sum_nonneg
    intro n hn
    split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl
  · rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
    apply sum_le_sum
    intro n hn
    by_cases hd : d ∣ floorMul α n <;> by_cases hp : n.Prime <;>
      simp [hd, hp, vonMangoldt_nonneg]

lemma prime_row_discrepancy (α : ℝ) (d N : ℕ) {E : ℝ}
    (hrow : |inputDivisorRow α d N-Chebyshev.psi N/d| ≤ E) :
    |row (Ioc 0 N) primeWeight (floorMul α) d-Chebyshev.psi N/d| ≤
      E+(Chebyshev.psi N-Chebyshev.theta N) := by
  obtain ⟨hlo, hhi⟩ := inputDivisorRow_prime_error α d N
  have he : row (Ioc 0 N) primeWeight (floorMul α) d-Chebyshev.psi N/d =
      (inputDivisorRow α d N-Chebyshev.psi N/d)-
        (inputDivisorRow α d N-row (Ioc 0 N) primeWeight (floorMul α) d) := by ring
  rw [he]
  have hh := abs_sub (inputDivisorRow α d N-Chebyshev.psi N/d)
    (inputDivisorRow α d N-row (Ioc 0 N) primeWeight (floorMul α) d)
  rw [abs_of_nonneg hlo] at hh
  linarith only [hh, hrow, hhi]

lemma rough_prime_sum (α : ℝ) (Z N : ℕ) :
    (∑ n ∈ Ioc 0 N, if (floorMul α n).Coprime Z.factorial then primeWeight n else 0) =
      coprimePrimeWeight α Z.factorial N := by
  simp only [coprimePrimeWeight, primeWeight, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hc : (floorMul α n).Coprime Z.factorial <;> by_cases hp : n.Prime <;> simp [hc, hp]

/-- The extra square root leaves room for the fixed-power lower sieve and
its coefficient mass within the available divisor level root64(u). -/
def roughRoot (u : ℕ) : ℕ := Nat.sqrt (root64 (root64 (root64 u)))

lemma le_roughRoot_iff (k u : ℕ) : k ≤ roughRoot u ↔ k^524288 ≤ u := by
  rw [roughRoot, Nat.le_sqrt', le_root64_iff, le_root64_iff, le_root64_iff]
  norm_num only [← pow_mul, Nat.reduceMul]

lemma roughRoot_tendsto : Tendsto roughRoot atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (B^524288)] with u hu
  exact (le_roughRoot_iff B u).mpr hu

lemma roughRoot_power_level (u : ℕ) : (roughRoot u)^8192 ≤ root64 u := by
  apply (le_root64_iff _ _).mpr
  have hh := (le_roughRoot_iff (roughRoot u) u).mp le_rfl
  simpa only [← pow_mul, Nat.reduceMul] using hh

lemma sieveRoot_eligible {u : ℕ} (hu : 0 < u) :
    1 ≤ roughRoot u ∧ ((roughRoot u)^1024)^5*roughRoot u ≤ root64 u := by
  have hZ : 1 ≤ roughRoot u := (le_roughRoot_iff 1 u).mpr (by simpa using hu)
  refine ⟨hZ, ?_⟩
  calc
    _ = (roughRoot u)^5121 := by rw [← pow_mul, ← pow_succ]
    _ ≤ (roughRoot u)^8192 := Nat.pow_le_pow_right hZ (by decide)
    _ ≤ _ := roughRoot_power_level u

lemma scaledRowError_nonneg (K u v : ℕ) : 0 ≤ scaledRowError K u v := by
  unfold scaledRowError
  have hC := Erdos972PrimeRotation.rotationConstant_pos (256*K)
  have hlog := Real.log_natCast_nonneg u
  positivity

lemma eventually_rough_prime_budget :
    ∀ᶠ u : ℕ in atTop,
      ((u^6 : ℕ) : ℝ)/2 ≤ Chebyshev.psi (u^6 : ℕ) ∧
      scaledRowError 1 u (root64 u)+(Chebyshev.psi (u^6 : ℕ)-Chebyshev.theta (u^6 : ℕ)) ≤
        ((u^6 : ℕ) : ℝ)/(16*root64 u) := by
  have hE := summed_scaledRowError_tendsto 1 0
  simp only [pow_zero, mul_one] at hE
  have htotal : Tendsto (fun u : ℕ => (root64 u : ℝ)*
      (scaledRowError 1 u (root64 u)+(Chebyshev.psi (u^6 : ℕ)-Chebyshev.theta (u^6 : ℕ)))/(u:ℝ)^6)
      atTop (𝓝 0) := by
    simpa only [mul_add, add_div, add_zero] using hE.add sixth_scale_primePower_tendsto
  filter_upwards [eventually_coprime_prime_budget,
    (tendsto_order.mp htotal).2 (1/16) (by norm_num), eventually_ge_atTop (1:ℕ)] with u hθ ht hu
  refine ⟨hθ.1.trans (Chebyshev.theta_le_psi _), ?_⟩
  have huR : (0:ℝ) < u := Nat.cast_pos.mpr hu
  have hv : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
  have hh := (div_lt_iff₀ (show 0 < (u:ℝ)^6 by positivity)).mp ht
  apply (le_div_iff₀ (show 0 < 16*(root64 u:ℝ) by positivity)).mpr
  push_cast at hh ⊢
  nlinarith only [hh]

/-- A genuinely positive prime-input lower bound at polynomial sifting
radius. The outputs are not asserted to be prime. -/
theorem exists_prime_rough_output_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < roughRoot u ∧
      (u:ℝ)^6/(8*root64 u) ≤ coprimePrimeWeight α (roughRoot u).factorial (u^6) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp roughRoot_tendsto)).eventually_ge_atTop 1
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_rough_prime_budget.and ((root64_tendsto.eventually_ge_atTop 2048).and
      (hlog.and (roughRoot_tendsto.eventually_gt_atTop B))))
  let A := max T (B+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI (A^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hAu : A ≤ u := (le_fourth_root_iff A r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (B+1)).trans hAu
  have hBu : B < u := by have := (le_max_right T (B+1)).trans hAu; omega
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  change u^4 ≤ r.den at hlo
  change r.den ≤ 16*u^4 at hhi
  clear_value u
  obtain ⟨⟨hψ, hbudget⟩, hv, hlogZ, hBZ⟩ := hT u hTu
  obtain ⟨hZ, helig⟩ := sieveRoot_eligible hu
  let Z := roughRoot u
  let R := Z^1024
  have hR : 1 ≤ R := Nat.one_le_pow 1024 Z hZ
  have hmod : R^2*Z ≤ root64 u := by
    apply le_trans _ helig
    exact Nat.mul_le_mul_right Z (Nat.pow_le_pow_right hR (by decide : 2 ≤ 5))
  have hE : 0 ≤ scaledRowError 1 u (root64 u)+(Chebyshev.psi (u^6 : ℕ)-Chebyshev.theta (u^6 : ℕ)) := by
    apply add_nonneg
    · exact scaledRowError_nonneg 1 u (root64 u)
    · exact sub_nonneg.mpr (Chebyshev.theta_le_psi _)
  have hlower := rough_weight_positive_bound (Ioc 0 (u^6)) primeWeight (floorMul α)
    (fun n _ => primeWeight_nonneg n) hR hZ helig hE hψ (lowerMain_power_positive hZ hlogZ) hbudget
    (fun d hd hdR => prime_row_discrepancy α d (u^6) (input_divisor_row_discrepancy
      (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
      (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi) hd (hdR.trans hmod) le_rfl))
  rw [rough_prime_sum] at hlower
  refine ⟨u, hBu, hBZ, ?_⟩
  have hR5 : R^5 ≤ root64 u := (Nat.le_mul_of_pos_right _ hZ).trans helig
  have hR0 : (0:ℝ) < R := Nat.cast_pos.mpr hR
  have hvR : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
  change ((u^6 : ℕ):ℝ)/(8*(R:ℝ)^5) ≤ coprimePrimeWeight α (roughRoot u).factorial (u^6) at hlower
  clear_value R
  calc
    _ ≤ ((u^6 : ℕ):ℝ)/(8*(R:ℝ)^5) := by
      rw [Nat.cast_pow]
      apply div_le_div_of_nonneg_left (pow_nonneg (Nat.cast_nonneg u) 6)
        (mul_pos (by norm_num) (pow_pos hR0 5))
      have hh := Nat.cast_le (α := ℝ).mpr hR5
      rw [Nat.cast_pow] at hh
      exact mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ _ := hlower

#print axioms exists_prime_rough_output_scale

end Erdos972PrimeRoughOutputs
