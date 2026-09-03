import Submission.MertensFromReciprocal

/-!
Uniform first-moment cancellation of the genuine large-input divisor
coefficient, including the range immediately above its cutoff. This does not
supply a four-factor correlation estimate.
-/
namespace Erdos972UniformDivisorCoefficient

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972CorrelationVaughan Erdos972MobiusPartialSums
open Erdos972MobiusLaplace Erdos972MellinDivisorCoefficient Erdos972MertensFromReciprocal

set_option maxHeartbeats 1000000

lemma tail_moebius_sum_zero {U j : ℕ} (hj : j ≤ U) :
    (∑ d ∈ Ioc 0 j, tail (μ : ArithmeticFunction ℝ) U d) = 0 := by
  apply sum_eq_zero
  intro d hd
  exact tail_eq_zero_of_le _ ((mem_Ioc.mp hd).2.trans hj)

lemma tail_moebius_sum {U j : ℕ} (hj : U ≤ j) :
    (∑ d ∈ Ioc 0 j, tail (μ : ArithmeticFunction ℝ) U d) = mertens j-mertens U := by
  have hf : (Ioc 0 j).filter (fun d => d ≤ U) = Ioc 0 U := by
    ext d
    simp only [mem_filter, mem_Ioc]
    omega
  simp only [tail, Erdos972Vaughan.sub_apply, cutoff_apply, sum_sub_distrib, ← sum_filter, hf]
  rfl

lemma divisorCoeff_sum_short {U N L : ℕ} (hLN : L ≤ N) (hN : N ≤ L*U) :
    (∑ n ∈ Ioc 0 N, divisorCoeff U n) =
      ∑ k ∈ Ioc 0 L, ∑ d ∈ Ioc 0 (N/k), tail (μ : ArithmeticFunction ℝ) U d := by
  have he := weightedSum_convolution (ζ : ArithmeticFunction ℝ)
    (tail (μ : ArithmeticFunction ℝ) U) (fun _ => 1) N
  rw [mul_comm (ζ : ArithmeticFunction ℝ)] at he
  simp only [weightedSum, mul_one] at he
  change (∑ n ∈ Ioc 0 N, divisorCoeff U n) = _ at he
  have hz (k : ℕ) (hk : k ∈ Ioc 0 N) : (ζ : ArithmeticFunction ℝ) k = 1 := by
    simp only [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hk).1), Nat.cast_one]
  rw [he]
  calc
    _ = ∑ k ∈ Ioc 0 N, ∑ d ∈ Ioc 0 (N/k), tail (μ : ArithmeticFunction ℝ) U d := by
      apply sum_congr rfl
      intro k hk
      rw [hz k hk, one_mul]
    _ = _ := by
      symm
      apply sum_subset (Ioc_subset_Ioc le_rfl hLN)
      intro k hk hkL
      have hLk : L < k := by simp only [mem_Ioc] at hk hkL; omega
      apply tail_moebius_sum_zero
      apply Nat.div_le_of_le_mul
      exact hN.trans (Nat.mul_le_mul_right U hLk.le)

lemma divisorCoeff_short_bound {U N L : ℕ} (hUN : U ≤ N) (hLN : L ≤ N) (hN : N ≤ L*U)
    {η : ℝ} (hη : 0 ≤ η) (hμ : ∀ n : ℕ, U ≤ n → |mertens n| ≤ η*n) :
    |∑ n ∈ Ioc 0 N, divisorCoeff U n| ≤ 2*η*(N : ℝ)*L := by
  rw [divisorCoeff_sum_short hLN hN]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Ioc 0 L, 2*η*(N : ℝ) := by
      apply sum_le_sum
      intro k hk
      by_cases hj : N/k ≤ U
      · rw [tail_moebius_sum_zero hj, abs_zero]
        positivity
      have hUj : U ≤ N/k := (lt_of_not_ge hj).le
      rw [tail_moebius_sum hUj]
      have ht := (abs_sub (mertens (N/k)) (mertens U)).trans
        (add_le_add (hμ (N/k) hUj) (hμ U le_rfl))
      have hh₁ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.div_le_self N k)) hη
      have hh₂ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hUN) hη
      linarith only [ht, hh₁, hh₂]
    _ = _ := by simp; ring

lemma divisorCoeff_long_bound {U N : ℕ} (hU : 0 < U) (hUN : U ≤ N) :
    |∑ n ∈ Ioc 0 N, divisorCoeff U n| ≤
      |reciprocalMoebius U| * (N : ℝ)+U+1 := by
  have he := divisorCoeff_prefix_error hU hUN
  have ht := abs_sub ((∑ n ∈ Ioc 0 N, divisorCoeff U n)+(N : ℝ)*reciprocalMoebius U-1)
    ((N : ℝ)*reciprocalMoebius U-1)
  have hid : (∑ n ∈ Ioc 0 N, divisorCoeff U n)+(N : ℝ)*reciprocalMoebius U-1 -
      ((N : ℝ)*reciprocalMoebius U-1) = ∑ n ∈ Ioc 0 N, divisorCoeff U n := by ring
  rw [hid] at ht
  have hh := abs_sub ((N : ℝ)*reciprocalMoebius U) 1
  simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N), abs_one] at hh
  linarith only [ht, he, hh]

/-- Uniformity in every endpoint N above the moving cutoff U. -/
theorem eventually_divisorCoeff_prefix_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U : ℕ in atTop, ∀ N : ℕ, U ≤ N →
      |∑ n ∈ Ioc 0 N, divisorCoeff U n| ≤ ε*(N : ℝ) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (4/ε)
  have hL0 : (0 : ℝ) < L := (by positivity : (0 : ℝ) < 4/ε).trans hL
  have hLε : (4 : ℝ) ≤ ε*L := by
    have hh := (div_lt_iff₀ hε).mp hL
    nlinarith only [hh]
  let η : ℝ := ε/(2*L)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_mertens_bound hη)
  have hs := reciprocalMoebius_tendsto_zero.abs
  simp only [abs_zero] at hs
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop L, eventually_ge_atTop (1 : ℕ),
    (tendsto_order.mp hs).2 (ε/2) (by positivity)] with U hUK hUL hU hsU
  intro N hUN
  have hU0 : 0 < U := by omega
  by_cases hN : N ≤ L*U
  · have hh := divisorCoeff_short_bound hUN (hUL.trans hUN) hN hη.le
      (fun n hn => hK n (hUK.trans hn))
    have hid : 2*η*(N : ℝ)*L = ε*(N : ℝ) := by dsimp [η]; field_simp
    exact hh.trans_eq hid
  · have hNU : (L : ℝ)*U ≤ N := by exact_mod_cast (lt_of_not_ge hN).le
    have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
    have h₁ := mul_le_mul_of_nonneg_left hNU (show 0 ≤ ε/2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hLε (Nat.cast_nonneg (α := ℝ) U)
    have h₃ := mul_le_mul_of_nonneg_right hsU.le (Nat.cast_nonneg (α := ℝ) N)
    have hh := divisorCoeff_long_bound hU0 hUN
    nlinarith only [h₁, h₂, h₃, hh, hUR]

/-- Bounded multiplicative frequencies are controlled uniformly on every
dyadic block above the cutoff, even when M is comparable to U. This is not
an estimate for high frequencies depending arbitrarily on the outer scale. -/
theorem eventually_divisorCoeff_mellin_uniform {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ U : ℕ in atTop, ∀ M : ℕ, U ≤ M → ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Ioc M (2*M), mellinPhase t n*(divisorCoeff U n : ℂ)‖ ≤ ε*(M : ℝ) := by
  let η : ℝ := ε/(3*(1+T))
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [eventually_divisorCoeff_prefix_small hη,
    eventually_ge_atTop (1 : ℕ)] with U hprefix hU
  intro M hUM t ht
  have hM : 0 < M := (show 0 < U by omega).trans_le hUM
  let w : ℕ → ℂ := fun n => mellinPhase t (M+n+1 : ℕ)
  let z : ℕ → ℂ := fun n => (divisorCoeff U (M+n+1) : ℂ)
  have hp (j : ℕ) (hj : j ≤ M) : ‖∑ n ∈ range j, z n‖ ≤ 3*η*(M : ℝ) := by
    dsimp only [z]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sum_shift_eq_Ioc]
    have h₁ := hprefix M hUM
    have h₂ := hprefix (M+j) (hUM.trans (Nat.le_add_right M j))
    have he := sum_Ioc_consecutive (divisorCoeff U) (Nat.zero_le M) (Nat.le_add_right M j)
    have hh := (abs_sub (∑ n ∈ Ioc 0 (M+j), divisorCoeff U n)
      (∑ n ∈ Ioc 0 M, divisorCoeff U n)).trans (add_le_add h₂ h₁)
    rw [← he, add_sub_cancel_left] at hh
    push_cast at hh
    have hjR := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj : (j : ℝ) ≤ M) hη.le
    nlinarith only [hh, hjR]
  have hh := norm_weighted_prefix w z M (3*η*(M : ℝ)) 1 T hp
    (by dsimp only [w]; rw [norm_mellinPhase]) ((mellinPhase_variation t hM).trans ht)
  dsimp only [w, z] at hh
  rw [sum_shift_eq_Ioc (fun n => mellinPhase t n*(divisorCoeff U n : ℂ)) M M] at hh
  have hid : (1+T)*(3*η*(M : ℝ)) = ε*(M : ℝ) := by
    dsimp [η]
    have hT0 : 1+T ≠ 0 := by positivity
    field_simp
  rw [hid] at hh
  simpa only [two_mul] using hh

#print axioms eventually_divisorCoeff_prefix_small
#print axioms eventually_divisorCoeff_mellin_uniform

end Erdos972UniformDivisorCoefficient
