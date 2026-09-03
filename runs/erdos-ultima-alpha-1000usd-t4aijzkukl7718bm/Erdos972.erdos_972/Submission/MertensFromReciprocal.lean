import Submission.MellinDivisorCoefficient

/-! Ordinary Möbius partial-sum cancellation derived from the already proved
reciprocal Möbius limit. -/
namespace Erdos972MertensFromReciprocal

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972MobiusPartialSums Erdos972MobiusLaplace Erdos972ExponentialSum

noncomputable def mertens (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, (μ n : ℝ)

lemma mertens_abel (N : ℕ) :
    mertens N = (N : ℝ)*reciprocalMoebius N - ∑ n ∈ range N, reciprocalMoebius n := by
  by_cases hN : N = 0
  · simp [hN, mertens, reciprocalMoebius]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let w : ℕ → ℝ := fun n => (n+1 : ℕ)
  let z : ℕ → ℝ := fun n => (μ (n+1) : ℝ)/(n+1 : ℕ)
  have hp (j : ℕ) : (∑ n ∈ range j, z n) = reciprocalMoebius j := by
    simp only [z, reciprocalMoebius, sum_Ioc_zero_eq_sum_range_succ]
  have hw (n : ℕ) : w n*z n = (μ (n+1) : ℝ) := by
    dsimp [w, z]
    field_simp
  have hd (n : ℕ) : w (n+1)-w n = 1 := by dsimp [w]; push_cast; ring
  have he := sum_range_by_parts w z N
  simp only [smul_eq_mul, hw, hp, hd, one_mul] at he
  dsimp only [w] at he
  rw [Nat.sub_add_cancel hNpos] at he
  have hs := sum_range_succ' reciprocalMoebius (N-1)
  have hzero : reciprocalMoebius 0 = 0 := by simp [reciprocalMoebius]
  rw [Nat.sub_add_cancel hNpos, hzero, add_zero] at hs
  rw [← hs] at he
  simpa only [mertens, sum_Ioc_zero_eq_sum_range_succ] using he

/-- The ordinary normalized Möbius sums also tend to zero. -/
theorem mertens_div_tendsto_zero :
    Tendsto (fun N : ℕ => mertens N/N) atTop (𝓝 0) := by
  have hc := reciprocalMoebius_tendsto_zero.cesaro
  have hh := reciprocalMoebius_tendsto_zero.sub hc
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [mertens_abel]
  field_simp

lemma eventually_mertens_bound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |mertens N| ≤ ε*(N : ℝ) := by
  have hh := mertens_div_tendsto_zero.abs
  simp only [abs_zero] at hh
  filter_upwards [(tendsto_order.mp hh).2 ε hε, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] at hN
  exact (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN1)).mp hN.le

#print axioms mertens_div_tendsto_zero
#print axioms eventually_mertens_bound

end Erdos972MertensFromReciprocal
