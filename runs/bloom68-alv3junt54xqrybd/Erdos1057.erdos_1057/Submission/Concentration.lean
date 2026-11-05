import Submission.Counting
import Submission.LargeLambda

/-!
# A fixed small-lambda reformulation of the Carmichael counting limit

For each fixed `δ > 0`, the logarithmic counting limit is equivalent to
all eventual power lower bounds for the count with `λ(n) < N ^ δ`.
The verified large-lambda upper bound supplies a positive power saving;
its logarithmic factor is absorbed using `log x = o(x ^ r)` for `r > 0`.

This is an exact conditional reformulation, not an unconditional density
assertion. No declaration from `Submission.Spec` is imported or used.
-/

open Set Real Filter
open scoped Topology

namespace Erdos1057.Concentration

/-- The number of Carmichael numbers `n ≤ N` with `λ(n) < N ^ δ`, as a real number. -/
noncomputable def smallLambdaCount (δ : ℝ) (N : ℕ) : ℝ :=
  ({n : ℕ | n ≤ N ∧ IsCarmichael n ∧
    (ArithmeticFunction.Carmichael n : ℝ) < (N : ℝ) ^ δ}.ncard : ℝ)

/-- The complementary count, including the boundary `N ^ δ ≤ λ(n)`. -/
noncomputable def largeLambdaCount (δ : ℝ) (N : ℕ) : ℝ :=
  ({n : ℕ | n ≤ N ∧ IsCarmichael n ∧
    (N : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ)}.ncard : ℝ)

theorem smallLambda_set_finite (δ : ℝ) (N : ℕ) :
    {n : ℕ | n ≤ N ∧ IsCarmichael n ∧
      (ArithmeticFunction.Carmichael n : ℝ) < (N : ℝ) ^ δ}.Finite :=
  (Set.finite_le_nat N).subset (fun _ hn => hn.1)

theorem largeLambda_set_finite (δ : ℝ) (N : ℕ) :
    {n : ℕ | n ≤ N ∧ IsCarmichael n ∧
      (N : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ)}.Finite :=
  (Set.finite_le_nat N).subset (fun _ hn => hn.1)

theorem smallLambdaCount_nonneg (δ : ℝ) (N : ℕ) : 0 ≤ smallLambdaCount δ N := by
  unfold smallLambdaCount
  positivity

theorem largeLambdaCount_nonneg (δ : ℝ) (N : ℕ) : 0 ≤ largeLambdaCount δ N := by
  unfold largeLambdaCount
  positivity

/-- Discarding the small-lambda restriction only increases the count. -/
theorem smallLambdaCount_le_count (δ : ℝ) (N : ℕ) :
    smallLambdaCount δ N ≤ Preparation.count (N : ℝ) := by
  apply Nat.cast_le.mpr
  apply Set.ncard_le_ncard _ (Preparation.count_set_finite (N : ℝ))
  intro n hn
  exact ⟨hn.2.1, Nat.cast_le.mpr hn.1⟩

/-- Exact finite partition at the lambda threshold, with equality in the large part. -/
theorem count_eq_large_add_small (δ : ℝ) (N : ℕ) :
    Preparation.count (N : ℝ) = largeLambdaCount δ N + smallLambdaCount δ N := by
  let large : Set ℕ := {n | n ≤ N ∧ IsCarmichael n ∧
    (N : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ)}
  let small : Set ℕ := {n | n ≤ N ∧ IsCarmichael n ∧
    (ArithmeticFunction.Carmichael n : ℝ) < (N : ℝ) ^ δ}
  have hunion : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ (N : ℝ)} = large ∪ small := by
    ext n
    constructor
    · intro hn
      have hnN : n ≤ N := Nat.cast_le.mp hn.2
      by_cases hLambda : (N : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ)
      · exact Or.inl ⟨hnN, hn.1, hLambda⟩
      · exact Or.inr ⟨hnN, hn.1, lt_of_not_ge hLambda⟩
    · rintro (hn | hn)
      · exact ⟨hn.2.1, Nat.cast_le.mpr hn.1⟩
      · exact ⟨hn.2.1, Nat.cast_le.mpr hn.1⟩
  have hdisjoint : Disjoint large small := by
    apply Set.disjoint_left.mpr
    intro n hnlarge hnsmall
    exact (not_lt_of_ge hnlarge.2.2) hnsmall.2.2
  have hcard := Set.ncard_union_eq hdisjoint
    (largeLambda_set_finite δ N) (smallLambda_set_finite δ N)
  change ({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ (N : ℝ)}.ncard : ℝ) =
    (large.ncard : ℝ) + (small.ncard : ℝ)
  rw [hunion, hcard, Nat.cast_add]

/-- A constant plus a fixed multiple of `log x` is eventually bounded by any
positive power. No sign condition on the multiple is needed. -/
private theorem eventually_four_add_mul_log_le_rpow {r : ℝ} (hr : 0 < r) (c : ℝ) :
    ∀ᶠ x : ℝ in atTop, 4 + c * Real.log x ≤ x ^ r := by
  have hconst : (fun _ : ℝ => (4 : ℝ)) =o[atTop] (fun x : ℝ => x ^ r) :=
    (Asymptotics.isLittleO_const_id_atTop (4 : ℝ)).comp_tendsto (tendsto_rpow_atTop hr)
  have hlog := (isLittleO_log_rpow_atTop hr).const_mul_left c
  filter_upwards [(hconst.add hlog).def zero_lt_one, eventually_ge_atTop (0 : ℝ)]
    with x hx hxnonneg
  apply (Real.le_norm_self (4 + c * Real.log x)).trans
  simpa only [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hxnonneg r)] using hx

/-- With `α = δ / (1 + 2 * δ) > 0`, the large-lambda count is eventually at most
`N ^ (1 - α / 2)`. This bound is unconditional for every fixed `δ > 0`. -/
theorem eventually_largeLambdaCount_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      largeLambdaCount δ N ≤ (N : ℝ) ^ (1 - CarmichaelLargeLambda.savingExponent δ / 2) := by
  let α : ℝ := CarmichaelLargeLambda.savingExponent δ
  have hα : 0 < α := (CarmichaelLargeLambda.savingExponent_properties hδ).1
  have hhalf : 0 < α / 2 := by linarith
  have hfactor : ∀ᶠ N : ℕ in atTop,
      4 + (1 - α) * Real.log (N : ℝ) ≤ (N : ℝ) ^ (α / 2) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_four_add_mul_log_le_rpow hhalf (1 - α))
  filter_upwards [hfactor, eventually_ge_atTop (2 : ℕ)] with N hf hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hbound : largeLambdaCount δ N ≤
      (N : ℝ) ^ (1 - α) * (4 + (1 - α) * Real.log (N : ℝ)) :=
    CarmichaelLargeLambda.ncard_carmichaels_with_large_lambda_le hδ hN
  calc
    largeLambdaCount δ N ≤
        (N : ℝ) ^ (1 - α) * (4 + (1 - α) * Real.log (N : ℝ)) := hbound
    _ ≤ (N : ℝ) ^ (1 - α) * (N : ℝ) ^ (α / 2) :=
      mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (1 - α / 2) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

/-- Under the counting-limit hypothesis, the small-lambda part has every eventual
power lower bound. Taking `η = min (ε / 2) (α / 4)` leaves positive gaps both
from `1 - α / 2` to `1 - η` and from `1 - ε` to `1 - η`. The argument works
for all `ε > 0`, including `ε ≥ 1`; it obtains positivity from the target's
lower bound and does not assume that `1 - ε` is positive. -/
theorem smallLambda_lower_bound_of_limit {δ : ℝ} (hδ : 0 < δ)
    (hlimit : Tendsto (fun x : ℝ => Real.log (Preparation.count x) / Real.log x)
      atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤ smallLambdaCount δ N := by
  intro ε hε
  let α : ℝ := CarmichaelLargeLambda.savingExponent δ
  let η : ℝ := min (ε / 2) (α / 4)
  have hα : 0 < α := (CarmichaelLargeLambda.savingExponent_properties hδ).1
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η ≤ ε / 2 := min_le_left _ _
  have hηα : η ≤ α / 4 := min_le_right _ _
  have hlargeGap : 0 < α / 2 - η := by linarith
  have hsmallGap : 0 < ε - η := by linarith
  have hlargePower : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (α / 2 - η) :=
    ((tendsto_rpow_atTop hlargeGap).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  have hsmallPower : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (ε - η) :=
    ((tendsto_rpow_atTop hsmallGap).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [Preparation.limit_iff_nat_lower_bound.mp hlimit η hη,
    eventually_largeLambdaCount_le_rpow hδ, hlargePower, hsmallPower,
    eventually_ge_atTop (1 : ℕ)] with N htotal hlarge hlgap hsgap hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hNreal
  change largeLambdaCount δ N ≤ (N : ℝ) ^ (1 - α / 2) at hlarge
  have hlargeHalf : 2 * (N : ℝ) ^ (1 - α / 2) ≤ (N : ℝ) ^ (1 - η) := by
    calc
      2 * (N : ℝ) ^ (1 - α / 2) ≤
          (N : ℝ) ^ (α / 2 - η) * (N : ℝ) ^ (1 - α / 2) :=
        mul_le_mul_of_nonneg_right hlgap (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (1 - η) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hsmallHalf : 2 * (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (1 - η) := by
    calc
      2 * (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (ε - η) * (N : ℝ) ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right hsgap (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (1 - η) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  linarith [count_eq_large_add_small δ N]

/-- For every fixed positive `δ`, the logarithmic counting limit is exactly the
family of eventual natural power lower bounds for the small-lambda count.
Neither side of this equivalence is asserted unconditionally. -/
theorem limit_iff_smallLambda_lower_bound {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => Real.log (Preparation.count x) / Real.log x) atTop (𝓝 1) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (1 - ε) ≤ smallLambdaCount δ N := by
  constructor
  · exact smallLambda_lower_bound_of_limit hδ
  · intro hlow
    apply Preparation.limit_iff_nat_lower_bound.mpr
    intro ε hε
    filter_upwards [hlow ε hε] with N hN
    exact hN.trans (smallLambdaCount_le_count δ N)

end Erdos1057.Concentration
