import Submission.ScaledPrimeRows
import Submission.DivisorCovariance

/-! Prime inputs with a divisibility condition on the Beatty output. These
are dual one-prime rows, available on the original reciprocal scales. -/
namespace Erdos972DualPrimeRows

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972RationalRotationCount Erdos972BeattyRows
open Erdos972WeightedPrimeRotation Erdos972ScaledPrimeRows Erdos972PolynomialRowScales
open Erdos972InverseGoodApproximation Erdos972ReciprocalDivisorCounts
open Erdos972DivisorPairCount Erdos972CenteredRowScales Erdos972PrimeRotation

set_option maxHeartbeats 1000000

noncomputable def inputDivisorRow (α : ℝ) (e N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter (fun n => e ∣ floorMul α n), vonMangoldt n

lemma inputDivisorRow_one (α : ℝ) (N : ℕ) : inputDivisorRow α 1 N = Chebyshev.psi N := by
  simp [inputDivisorRow, Chebyshev.psi]

lemma inputDivisorRow_complement_arc {α : ℝ} (hα : 0 ≤ α) {e : ℕ} (he : 1 < e) (N : ℕ) :
    inputDivisorRow α e N+
      mangoldtArcSum (α/e) (-(1/(2*e))) (1/(2*e)) (1-1/(2*e)) N = Chebyshev.psi N := by
  have heR : (1 : ℝ) < e := by exact_mod_cast he
  have ha : (0 : ℝ) < 1/(2*e) := by positivity
  have ha2 : 1/(2*(e : ℝ)) < 1/2 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith only [heR]
  have hp (n : ℕ) : (1/(2*(e : ℝ)) ≤ Int.fract ((α/e)*n+-(1/(2*e))) ∧
      Int.fract ((α/e)*n+-(1/(2*e))) < 1-1/(2*e)) ↔ ¬ e ∣ floorMul α n := by
    rw [← sub_eq_add_neg, fract_sub_center ha ha2]
    rw [floorMul, floor_dvd_iff_fract_div_lt (by positivity) (by omega), not_lt]
    rw [show 2*(1/(2*(e : ℝ))) = 1/e by ring, show (α/(e : ℝ))*n = α*n/e by ring]
  simp only [inputDivisorRow, mangoldtArcSum, sum_filter, Chebyshev.psi, Nat.floor_natCast,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  simp only [hp n]
  by_cases hd : e ∣ floorMul α n <;> simp [hd]

/-- A growing family of dual one-prime rows. No prime condition is placed on
the output: only divisibility by a small integer. -/
theorem input_divisor_row_discrepancy {α : ℝ} (hα : 0 ≤ α)
    (r : ℚ) (hr : |α-r| ≤ 1/(r.den : ℝ)^2)
    {K u v : ℕ} (hK : 0 < K) (hv : 2048*K ≤ v) (hvu : v^64 ≤ u)
    (hlo : u^4 ≤ K*r.den) (hhi : r.den ≤ 16*K*u^4)
    {e X : ℕ} (he : 0 < e) (hev : e ≤ v) (hX : X ≤ u^6) :
    |inputDivisorRow α e X-Chebyshev.psi X/e| ≤ scaledRowError K u v := by
  have hv0 : 0 < v := (show 0 < 2048*K by positivity).trans_le hv
  have hE0 : 0 ≤ scaledRowError K u v := by
    unfold scaledRowError
    positivity [rotationConstant_pos (256*K), Real.log_natCast_nonneg u]
  by_cases he1 : e = 1
  · subst e
    simpa only [inputDivisorRow_one, Nat.cast_one, div_one, sub_self, abs_zero] using hE0
  have he2 : 1 < e := by omega
  have heR : (1 : ℝ) < e := by exact_mod_cast he2
  have hvR : (2 : ℝ) ≤ v := by exact_mod_cast he2.trans_le hev
  have hmargin : 1/(v : ℝ)^3 ≤ 1/(2*e) := by
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2*e)
    have hp : 2*(v : ℝ) ≤ (v : ℝ)^3 := by
      have hh : (v : ℝ) ≤ (v : ℝ)^2 := by nlinarith only [hvR]
      nlinarith only [hvR, hh, mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (v : ℝ))]
    have hevR : (e : ℝ) ≤ v := Nat.cast_le.mpr hev
    linarith only [hp, hevR]
  have hab : 1/(2*(e : ℝ)) ≤ 1-1/(2*e) := by
    have hh : 1/(2*(e : ℝ)) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num)
      (by linarith only [heR])
    linarith only [hh]
  have hh := scaled_arc_prefix_bound hα r hr K u v v hK hv0 le_rfl hv hvu hlo hhi
    (1/(2*e)) (1-1/(2*e)) (-(1/(2*e))) hab hmargin (by linarith only [hmargin])
    e X he hev hX
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Erdos972BeattyRowScales.mangoldtArcSum_nat_add] at hh
  have hc := inputDivisorRow_complement_arc hα he2 X
  have heq : inputDivisorRow α e X-Chebyshev.psi X/e =
      -(mangoldtArcSum (α/e) (-(1/(2*e))) (1/(2*e)) (1-1/(2*e)) X-
        ((1-1/(2*e))-1/(2*e))*Chebyshev.psi X) := by
    linear_combination hc
  rw [heq, abs_neg]
  exact hh

lemma summed_scaledRowError_tendsto (K k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)*(1+Real.log u)^k*scaledRowError K u (root64 u)/(u : ℝ)^6)
      atTop (𝓝 0) := by
  let C := 28+rotationConstant (256*K)
  have hC : 0 < C := by dsimp [C]; positivity [rotationConstant_pos (256*K)]
  have hi : Tendsto (fun u : ℕ => 1/(root64 u : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp root64_tendsto)
  have hh := (root64_log_div_tendsto C hC (k+5)).mul hi
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have hu0 : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hu)
  have hv0 : (root64 u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (root64_bounds hu).1)
  unfold scaledRowError
  rw [pow_add]
  dsimp [C]
  field_simp

#print axioms input_divisor_row_discrepancy
#print axioms summed_scaledRowError_tendsto

noncomputable def dualScaleLoss (α : ℝ) : ℕ := 64*⌈α⌉₊^3

lemma dualScaleLoss_pos {α : ℝ} (hα : 1 ≤ α) : 0 < dualScaleLoss α := by
  have hJ : (1 : ℝ) ≤ ⌈α⌉₊ := hα.trans (Nat.le_ceil α)
  have hJ0 : 0 < ⌈α⌉₊ := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hJ)
  unfold dualScaleLoss
  positivity

/-- Both orientations of the one-prime rows, and the ordinary joint-divisor
counts, hold at arbitrarily large common scales. -/
theorem exists_two_sided_prime_divisor_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 4*α ≤ u ∧ 2048*dualScaleLoss α ≤ root64 u ∧
      (∀ m : ℕ, 0 < m → m ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
        |mangoldtArcSum (1/(α*m)) (-rowArcLeft (α*m)) (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) X-
          (1/(α*m))*Chebyshev.psi X| ≤ polynomialRowError u (root64 u)) ∧
      (∀ e : ℕ, 0 < e → e ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
        |inputDivisorRow α e X-Chebyshev.psi X/e| ≤ scaledRowError (dualScaleLoss α) u (root64 u)) ∧
      (∀ d e : ℕ, 0 < d → 0 < e → e ≤ root64 u → ∀ X ≤ scaleCutoff α u,
        |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤ 118*(root64 u : ℝ)*(u : ℝ)^4) := by
  let K := dualScaleLoss α
  have hK : 0 < K := dualScaleLoss_pos hα.le
  let C := max B (max (⌈4*α⌉₊+1) ((2048*K)^64))
  obtain ⟨u, v, r, hu, hv, hvu, huv, rfl, hr, hlo, hhi, hrows⟩ :=
    exists_polynomial_beatty_arc_scale_data hα hI C
  have hu0 : 0 < u := (Nat.zero_le C).trans_lt hu
  have hαu : 4*α ≤ u := (Nat.le_ceil _).trans (by
    exact_mod_cast (Nat.le_succ ⌈4*α⌉₊).trans
      ((le_max_left (⌈4*α⌉₊+1) ((2048*K)^64)).trans ((le_max_right B _).trans hu.le)))
  have hKu : (2048*K)^64 ≤ u :=
    (le_max_right (⌈4*α⌉₊+1) _).trans ((le_max_right B _).trans hu.le)
  have hKv : 2048*K ≤ root64 u := (le_root64_iff _ _).mpr hKu
  have hq : 2*α ≤ r.den := by
    have hu4 : (u : ℝ) ≤ (u : ℝ)^4 := by exact_mod_cast Nat.le_self_pow (by norm_num : 4 ≠ 0) u
    have hloR : (u : ℝ)^4 ≤ r.den := by exact_mod_cast hlo
    linarith only [hα, hαu, hu4, hloR]
  obtain ⟨s, hslo, hshi, hs⟩ := inverse_good_approximant hα.le r hr hq (Nat.le_ceil α)
  change r.den ≤ K*s.den at hslo
  change s.den ≤ K*r.den at hshi
  have hslo' : u^4 ≤ K*s.den := hlo.trans hslo
  have hshi' : s.den ≤ 16*K*u^4 := by
    have hh := hshi.trans (Nat.mul_le_mul_left K hhi)
    nlinarith only [hh]
  refine ⟨u, (le_max_left B _).trans_lt hu, hαu, hKv, hrows, ?_, ?_⟩
  · intro e he hev X hX
    exact input_divisor_row_discrepancy (by linarith : 0 ≤ α) s hs hK hKv hvu hslo' hshi' he hev hX
  · intro d e hd he hev X hX
    apply reciprocal_scale_divisor_prefix_bound hα.le r hr hu0
      (show 0 < root64 u by omega) hαu hlo hhi _ hd he hev
    have hα0 : 0 < α := by linarith
    have hh : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
    have hXR : (X : ℝ) ≤ scaleCutoff α u := Nat.cast_le.mpr hX
    have hh' := (le_div_iff₀ hα0).mp (hXR.trans hh)
    nlinarith only [hh']

#print axioms exists_two_sided_prime_divisor_scale

end Erdos972DualPrimeRows
