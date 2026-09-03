import Submission.MobiusLaplace
import Submission.DoubleVaughan

/-!
Low multiplicative-frequency estimates for the actual divisor coefficient in
Vaughan's large-input part. These are not estimates for the full four-factor
correlation and do not settle the prime-pair conjecture.
-/
namespace Erdos972MellinDivisorCoefficient

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972CorrelationVaughan Erdos972MobiusPartialSums
open Erdos972MobiusLaplace Erdos972ExponentialSum

set_option maxHeartbeats 1000000

noncomputable def divisorCoeff (U n : ℕ) : ℝ :=
  (tail (μ : ArithmeticFunction ℝ) U * ζ) n

lemma divisorCoeff_eq (U n : ℕ) :
    divisorCoeff U n = (1 : ArithmeticFunction ℝ) n -
      (cutoff (μ : ArithmeticFunction ℝ) U * ζ) n := by
  unfold divisorCoeff tail
  rw [sub_mul, coe_moebius_mul_coe_zeta]
  rfl

lemma divisorCoeff_sum {U N : ℕ} (hU : 0 < U) (hUN : U ≤ N) :
    (∑ n ∈ Ioc 0 N, divisorCoeff U n) =
      1 - ∑ d ∈ Ioc 0 U, (μ d : ℝ) * (N / d : ℕ) := by
  have hN : 0 < N := hU.trans_le hUN
  have hh := weightedSum_convolution_support (cutoff (μ : ArithmeticFunction ℝ) U)
    (ζ : ArithmeticFunction ℝ) (fun _ => 1) U N
    (fun n hn => cutoff_eq_zero_of_lt _ hn)
  rw [min_eq_left hUN] at hh
  have hinner (d : ℕ) :
      (∑ n ∈ Ioc 0 (N/d), (ζ : ArithmeticFunction ℝ) n * 1) = (N/d : ℕ) := by
    calc
      _ = ∑ n ∈ Ioc 0 (N/d), (1 : ℝ) := by
        apply sum_congr rfl
        intro n hn
        simp only [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1),
          Nat.cast_one, one_mul]
      _ = _ := by simp
  simp only [mul_one] at hinner
  simp only [weightedSum, mul_one, hinner] at hh
  have hsum : (∑ n ∈ Ioc 0 N, (cutoff (μ : ArithmeticFunction ℝ) U * ζ) n) =
      ∑ d ∈ Ioc 0 U, (μ d : ℝ) * (N/d : ℕ) := by
    rw [hh]
    apply sum_congr rfl
    intro d hd
    rw [cutoff_eq_of_le _ (mem_Ioc.mp hd).2]
    rfl
  simp only [divisorCoeff_eq, sum_sub_distrib, hsum]
  congr 1
  simp only [one_apply, sum_ite_eq', mem_Ioc]
  simp [Nat.ne_of_gt hN]

/-- The signed center is essential: it is the reciprocal Möbius sum, not a
sum of the absolute values of its coefficients. -/
lemma divisorCoeff_prefix_error {U N : ℕ} (hU : 0 < U) (hUN : U ≤ N) :
    |(∑ n ∈ Ioc 0 N, divisorCoeff U n) + (N : ℝ)*reciprocalMoebius U - 1| ≤ U := by
  rw [divisorCoeff_sum hU hUN]
  have he : 1 - (∑ d ∈ Ioc 0 U, (μ d : ℝ)*(N/d : ℕ)) +
      (N : ℝ)*reciprocalMoebius U - 1 =
      ∑ d ∈ Ioc 0 U, (μ d : ℝ)*((N : ℝ)/d-(N/d : ℕ)) := by
    simp only [reciprocalMoebius, mul_sub, sum_sub_distrib, mul_sum]
    have hm : (∑ d ∈ Ioc 0 U, (N : ℝ)*((μ d : ℝ)/d)) =
        ∑ d ∈ Ioc 0 U, (μ d : ℝ)*((N : ℝ)/d) := by
      apply sum_congr rfl
      intro d hd
      ring
    rw [hm]
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Ioc 0 U, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hf0 : 0 ≤ (N : ℝ)/d-(N/d : ℕ) := sub_nonneg.mpr Nat.cast_div_le
      have hf1 : (N : ℝ)/d-(N/d : ℕ) ≤ 1 := by
        have hf := Nat.lt_floor_add_one ((N : ℝ)/d)
        rw [Nat.floor_div_eq_div] at hf
        linarith only [hf]
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
      rw [abs_mul, abs_of_nonneg hf0]
      exact (mul_le_mul hμ hf1 hf0 zero_le_one).trans_eq (by norm_num)
    _ = _ := by simp

lemma divisorCoeff_interval_prefix {U M j : ℕ} (hU : 0 < U) (hUM : U ≤ M) (hj : j ≤ M) :
    |∑ n ∈ Ioc M (M+j), divisorCoeff U n| ≤
      |reciprocalMoebius U| *(M : ℝ)+2*U := by
  have h₁ := divisorCoeff_prefix_error hU hUM
  have h₂ := divisorCoeff_prefix_error hU (hUM.trans (Nat.le_add_right M j))
  have he := sum_Ioc_consecutive (divisorCoeff U) (Nat.zero_le M) (Nat.le_add_right M j)
  have herr : |(∑ n ∈ Ioc M (M+j), divisorCoeff U n)+(j : ℝ)*reciprocalMoebius U| ≤ 2*U := by
    have ht := abs_sub ((∑ n ∈ Ioc 0 (M+j), divisorCoeff U n)+
        ((M+j : ℕ) : ℝ)*reciprocalMoebius U-1)
      ((∑ n ∈ Ioc 0 M, divisorCoeff U n)+(M : ℝ)*reciprocalMoebius U-1)
    have ht := ht.trans (add_le_add h₂ h₁)
    rw [← he] at ht
    push_cast at ht
    have hid : (∑ n ∈ Ioc 0 M, divisorCoeff U n) +
        (∑ n ∈ Ioc M (M+j), divisorCoeff U n) +
        ((M : ℝ)+j)*reciprocalMoebius U-1 -
        ((∑ n ∈ Ioc 0 M, divisorCoeff U n)+(M : ℝ)*reciprocalMoebius U-1) =
        (∑ n ∈ Ioc M (M+j), divisorCoeff U n)+(j : ℝ)*reciprocalMoebius U := by ring
    rw [hid] at ht
    linarith only [ht]
  have ht := abs_sub ((∑ n ∈ Ioc M (M+j), divisorCoeff U n)+(j : ℝ)*reciprocalMoebius U)
    ((j : ℝ)*reciprocalMoebius U)
  simp only [add_sub_cancel_right, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at ht
  have hjR : (j : ℝ) ≤ M := Nat.cast_le.mpr hj
  have hm := mul_le_mul_of_nonneg_right hjR (abs_nonneg (reciprocalMoebius U))
  linarith only [ht, herr, hm]

/-- A finite summation-by-parts bound with no monotonicity assumption on the
complex weight. -/
lemma norm_weighted_prefix (w z : ℕ → ℂ) (K : ℕ) (E A V : ℝ)
    (hE : ∀ j ≤ K, ‖∑ n ∈ range j, z n‖ ≤ E)
    (hA : ‖w (K-1)‖ ≤ A)
    (hV : (∑ n ∈ range (K-1), ‖w (n+1)-w n‖) ≤ V) :
    ‖∑ n ∈ range K, w n*z n‖ ≤ (A+V)*E := by
  have hE0 : 0 ≤ E := by simpa using hE 0 (Nat.zero_le K)
  have he := sum_range_by_parts w z K
  simp only [smul_eq_mul] at he
  rw [he]
  calc
    _ ≤ ‖w (K-1)*(∑ n ∈ range K, z n)‖ +
        ‖∑ n ∈ range (K-1), (w (n+1)-w n)*(∑ i ∈ range (n+1), z i)‖ := norm_sub_le _ _
    _ ≤ A*E+(∑ n ∈ range (K-1), ‖w (n+1)-w n‖)*E := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul hA (hE K le_rfl) (norm_nonneg _) ((norm_nonneg _).trans hA)
      · rw [sum_mul]
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hE (n+1) (by have := mem_range.mp hn; omega)) (norm_nonneg _)
    _ ≤ (A+V)*E := by
      have hh := mul_le_mul_of_nonneg_right hV hE0
      nlinarith only [hh]

lemma sum_shift_eq_Ioc {E : Type*} [AddCommMonoid E] (f : ℕ → E) (M j : ℕ) :
    (∑ n ∈ range j, f (M+n+1)) = ∑ n ∈ Ioc M (M+j), f n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, show M+(j+1) = M+j+1 by omega,
      sum_Ioc_succ_top (Nat.le_add_right M j)]

noncomputable def mellinPhase (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I*((t*Real.log x : ℝ) : ℂ))

lemma norm_mellinPhase (t x : ℝ) : ‖mellinPhase t x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

lemma mellinPhase_difference (t x y : ℝ) :
    ‖mellinPhase t x-mellinPhase t y‖ ≤ |t| * |Real.log x-Real.log y| := by
  have he : mellinPhase t x-mellinPhase t y =
      mellinPhase t y*(Complex.exp (Complex.I*((t*(Real.log x-Real.log y) : ℝ) : ℂ))-1) := by
    rw [mul_sub, mul_one]
    simp only [mellinPhase]
    rw [← Complex.exp_add]
    apply congrArg (fun z : ℂ => Complex.exp z - Complex.exp (Complex.I * ↑(t * Real.log y)))
    push_cast
    ring
  rw [he, norm_mul, norm_mellinPhase, one_mul]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*(Real.log x-Real.log y))
  simpa only [Real.norm_eq_abs, abs_mul] using hh

lemma log_nat_step_bound {M m : ℕ} (hM : 0 < M) (hMm : M ≤ m) :
    |Real.log (m+1 : ℕ)-Real.log m| ≤ 1/(M : ℝ) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (hM.trans_le hMm)
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlog : Real.log m ≤ Real.log (m+1 : ℕ) :=
    Real.log_le_log hm (by exact_mod_cast Nat.le_succ m)
  rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
  calc
    _ = Real.log (((m : ℝ)+1)/m) := by
      rw [Real.log_div (by positivity) hm.ne']
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ ((m : ℝ)+1)/m-1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 1/(m : ℝ) := by field_simp; ring
    _ ≤ 1/(M : ℝ) := one_div_le_one_div_of_le hM0 (Nat.cast_le.mpr hMm)

lemma mellinPhase_variation (t : ℝ) {M : ℕ} (hM : 0 < M) :
    (∑ n ∈ range (M-1),
      ‖mellinPhase t (M+(n+1)+1 : ℕ)-mellinPhase t (M+n+1 : ℕ)‖) ≤ |t| := by
  have hp (n : ℕ) :
      ‖mellinPhase t (M+(n+1)+1 : ℕ)-mellinPhase t (M+n+1 : ℕ)‖ ≤ |t|/(M : ℝ) := by
    have hh := mellinPhase_difference t (M+(n+1)+1 : ℕ) (M+n+1 : ℕ)
    have hl := log_nat_step_bound hM (show M ≤ M+n+1 by omega)
    rw [show M+(n+1)+1 = (M+n+1)+1 by omega] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hl (abs_nonneg t)).trans_eq (by ring))
  calc
    _ ≤ ∑ n ∈ range (M-1), |t|/(M : ℝ) := sum_le_sum (fun n _ => hp n)
    _ = ((M-1 : ℕ) : ℝ)*(|t|/(M : ℝ)) := by simp
    _ ≤ (M : ℝ)*(|t|/(M : ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M 1)) (by positivity)
    _ = |t| := by field_simp

/-- The genuine divisor coefficient has no persistent bounded-frequency
Mellin component on a dyadic interval when U grows but U/M tends to zero. -/
theorem divisorCoeff_mellin_bound (t : ℝ) {U M : ℕ} (hU : 0 < U) (hUM : U ≤ M) :
    ‖∑ n ∈ Ioc M (2*M), mellinPhase t n*(divisorCoeff U n : ℂ)‖ ≤
      (1+|t|)*(|reciprocalMoebius U| * (M : ℝ)+2*U) := by
  have hM : 0 < M := hU.trans_le hUM
  let w : ℕ → ℂ := fun n => mellinPhase t (M+n+1 : ℕ)
  let z : ℕ → ℂ := fun n => (divisorCoeff U (M+n+1) : ℂ)
  have hp (j : ℕ) (hj : j ≤ M) :
      ‖∑ n ∈ range j, z n‖ ≤ |reciprocalMoebius U| * (M : ℝ)+2*U := by
    dsimp only [z]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sum_shift_eq_Ioc]
    exact divisorCoeff_interval_prefix hU hUM hj
  have hh := norm_weighted_prefix w z M (|reciprocalMoebius U| * (M : ℝ)+2*U) 1 |t|
    hp (by dsimp only [w]; rw [norm_mellinPhase]) (mellinPhase_variation t hM)
  dsimp only [w, z] at hh
  rw [sum_shift_eq_Ioc (fun n => mellinPhase t n*(divisorCoeff U n : ℂ)) M M] at hh
  simpa only [two_mul] using hh

/-- Uniformity for all frequencies in a fixed compact interval. The error
term here does not assert uniformity for frequencies growing with the scale. -/
theorem divisorCoeff_mellin_uniform (U M : ℕ → ℕ)
    (hU : Tendsto U atTop atTop)
    (hUM : ∀ᶠ k : ℕ in atTop, U k ≤ M k)
    (hsmall : Tendsto (fun k => (U k : ℝ)/(M k : ℝ)) atTop (𝓝 0))
    {T : ℝ} (_hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Ioc (M k) (2*M k), mellinPhase t n*(divisorCoeff (U k) n : ℂ)‖ ≤
        ε*(M k : ℝ) := by
  have hs : Tendsto (fun k => |reciprocalMoebius (U k)|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (reciprocalMoebius_tendsto_zero.comp hU).abs
  have hb : Tendsto (fun k => (1+T)*(|reciprocalMoebius (U k)|+2*((U k : ℝ)/(M k : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hs.add (hsmall.const_mul 2)).const_mul (1+T)
  filter_upwards [(tendsto_order.mp hb).2 ε hε, hU.eventually_ge_atTop 1, hUM] with k hk hUk hUMk
  intro t ht
  have hU0 : 0 < U k := by omega
  have hM0 : (0 : ℝ) < M k := Nat.cast_pos.mpr (hU0.trans_le hUMk)
  have hbound := divisorCoeff_mellin_bound t hU0 hUMk
  have hfreq := mul_le_mul_of_nonneg_right (show 1+|t| ≤ 1+T by linarith only [ht])
    (show 0 ≤ |reciprocalMoebius (U k)| * (M k : ℝ)+2*U k by positivity)
  have hbudget := mul_le_mul_of_nonneg_right hk.le hM0.le
  have hid : (1+T)*(|reciprocalMoebius (U k)|+2*((U k : ℝ)/(M k : ℝ)))*(M k : ℝ) =
      (1+T)*(|reciprocalMoebius (U k)| * (M k : ℝ)+2*U k) := by
    field_simp
  rw [hid] at hbudget
  exact hbound.trans (hfreq.trans hbudget)

#print axioms divisorCoeff_prefix_error
#print axioms divisorCoeff_interval_prefix
#print axioms divisorCoeff_mellin_bound
#print axioms divisorCoeff_mellin_uniform

end Erdos972MellinDivisorCoefficient
