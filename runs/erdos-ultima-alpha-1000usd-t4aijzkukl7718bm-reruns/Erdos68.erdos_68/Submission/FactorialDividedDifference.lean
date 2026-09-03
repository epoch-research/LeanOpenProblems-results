import FormalConjecturesUtil

/-! Dividing an integer-factorial-coefficient series by 1-z preserves
integer factorial-scaled coefficients, with arbitrary integer numerator
parameters. This integrality does not assert cancellation at z=1. -/

namespace FactorialDividedDifference

open Filter
open scoped Topology

/-- Integer coefficients of (a-bF)/(1-z), in exponential normalization. -/
def quotientCoeff (a b : ℤ) (u : ℕ → ℤ) : ℕ → ℤ
  | 0 => a - b * u 0
  | n + 1 => (n + 1 : ℤ) * quotientCoeff a b u n - b * u (n + 1)

lemma quotientCoeff_formula {K : Type*} [Field K] [CharZero K]
    (a b : ℤ) (u : ℕ → ℤ) (n : ℕ) :
    (quotientCoeff a b u n : K) / (n.factorial : K) =
      a - b * ∑ k ∈ Finset.range (n+1), (u k : K) / (k.factorial : K) := by
  induction n with
  | zero => simp [quotientCoeff]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have he : (quotientCoeff a b u (n+1) : K) / ((n+1).factorial : K) =
        (quotientCoeff a b u n : K) / (n.factorial : K) -
          (b : K) * (u (n+1) : K) / ((n+1).factorial : K) := by
      simp only [quotientCoeff, Int.cast_sub, Int.cast_mul, Int.cast_add,
        Int.cast_natCast, Int.cast_one, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
    rw [he, ih]
    ring

noncomputable def series (u : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (u n : ℚ) / (n.factorial : ℚ))

/-- This identity holds for all a,b, whether or not a/b is the value at one. -/
theorem formal_quotient_identity (a b : ℤ) (u : ℕ → ℤ) :
    (1 - PowerSeries.X) * series (quotientCoeff a b u) =
      PowerSeries.C (a : ℚ) - PowerSeries.C (b : ℚ) * series u := by
  ext n
  rw [sub_mul, one_mul]
  cases n with
  | zero => simp [series, quotientCoeff]
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C,
      Nat.succ_ne_zero, ↓reduceIte, PowerSeries.coeff_C_mul, series, PowerSeries.coeff_mk]
    rw [quotientCoeff_formula, quotientCoeff_formula, Finset.sum_range_succ]
    ring

/-- The normalized coefficient limit records exactly the missing endpoint
cancellation; it is not forced to be zero by integrality. -/
theorem normalized_coeff_limit (a b : ℤ) (u : ℕ → ℤ) (x : ℝ)
    (hu : HasSum (fun n => (u n : ℝ) / (n.factorial : ℝ)) x) :
    Tendsto (fun n => (quotientCoeff a b u n : ℝ) / (n.factorial : ℝ))
      atTop (𝓝 ((a : ℝ) - b*x)) := by
  simp_rw [quotientCoeff_formula]
  exact tendsto_const_nhds.sub (tendsto_const_nhds.mul
    (hu.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)))

theorem normalized_coeff_zero_iff (a b : ℤ) (u : ℕ → ℤ) (x : ℝ)
    (hu : HasSum (fun n => (u n : ℝ) / (n.factorial : ℝ)) x) :
    Tendsto (fun n => (quotientCoeff a b u n : ℝ) / (n.factorial : ℝ))
      atTop (𝓝 0) ↔ (a : ℝ) = b*x := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (normalized_coeff_limit a b u x hu) h
    linarith
  · intro he
    simpa [he] using normalized_coeff_limit a b u x hu

end FactorialDividedDifference

#print axioms FactorialDividedDifference.formal_quotient_identity
#print axioms FactorialDividedDifference.normalized_coeff_zero_iff
