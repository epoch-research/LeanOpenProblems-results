import Submission.WeightedDivisor
import Submission.PrimeTail
import Submission.DivisorBounds

/-!
# A uniform finite upper bound for Carmichael numbers with large lambda

For `δ > 0`, put `α = δ / (1 + 2 * δ)`. The Carmichael numbers `n ≤ X`
with `X ^ δ ≤ λ(n)` are split at the prime cutoff `floor (X ^ α)`.
The large-prime tail costs at most `2 * X ^ (1 - α)`. In the remaining
case, weighted divisor selection supplies a divisor at most
`floor (X ^ (1 - α))` with lambda at least `ceil (X ^ α)`. The divisor
certificate bound then costs at most
`X ^ (1 - α) * (2 + (1 - α) * log X)`.

All statements are finite upper reductions. No density assertion, negation
of a density assertion, or declaration from `Submission.Spec` is used.
-/

namespace Erdos1057.CarmichaelLargeLambda

/-- The positive power saving used in the large-lambda upper reduction. -/
noncomputable def savingExponent (δ : ℝ) : ℝ := δ / (1 + 2 * δ)

/-- The saving is smaller than one half, is at most `δ`, and balances the
smooth-divisor exponent with the large-prime tail exponent. -/
theorem savingExponent_properties {δ : ℝ} (hδ : 0 < δ) :
    0 < savingExponent δ ∧ savingExponent δ < 1 / 2 ∧
      savingExponent δ ≤ δ ∧
      savingExponent δ + savingExponent δ / δ = 1 - savingExponent δ := by
  have hden : 0 < 1 + 2 * δ := by linarith
  dsimp only [savingExponent]
  refine ⟨div_pos hδ hden, ?_, ?_, ?_⟩
  · apply (div_lt_iff₀ hden).mpr
    linarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg δ]
  · field_simp [hδ.ne', hden.ne']
    ring

/-- Rounding a real cutoff at least one down loses at most a factor of two. -/
theorem half_le_nat_floor {y : ℝ} (hy : 1 ≤ y) :
    y / 2 ≤ (⌊y⌋₊ : ℝ) := by
  have hf : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).mpr hy
  have hfreal : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hf
  have hlt := Nat.lt_floor_add_one y
  linarith

/-- A smooth Carmichael number with `λ(n) ≥ X ^ δ` has a rounded divisor
certificate. The unrounded size bound is `X ^ (α + α / δ)`; no counting
or density hypothesis is assumed. -/
theorem exists_divisor_of_smooth_large_lambda {δ α : ℝ}
    (hδ : 0 < δ) (hα : 0 < α) (hαδ : α ≤ δ) {X n : ℕ}
    (hX : 2 ≤ X) (hnX : n ≤ X) (hn : IsCarmichael n)
    (hLambda : (X : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ))
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ (X : ℝ) ^ α) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ ⌊(X : ℝ) ^ (α + α / δ)⌋₊ ∧
      ⌈(X : ℝ) ^ α⌉₊ ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n := by
  have hXreal : 1 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hX)
  have hXpos : 0 < (X : ℝ) := zero_lt_one.trans hXreal
  have hn1 : 1 ≤ n :=
    Nat.one_le_of_lt (CarmichaelCertificates.divisor_pos hn (dvd_refl n))
  have hnSq : Squarefree n := (CarmichaelKorselt.isCarmichael_iff_korselt n).mp hn |>.2.1
  have hLambdaReal : 1 < (ArithmeticFunction.Carmichael n : ℝ) :=
    (Real.one_lt_rpow hXreal hδ).trans_le hLambda
  have hLambdaNat : 1 < ArithmeticFunction.Carmichael n := by
    exact_mod_cast hLambdaReal
  have hu : 1 < (X : ℝ) ^ α := Real.one_lt_rpow hXreal hα
  have huLambda : (X : ℝ) ^ α ≤ (ArithmeticFunction.Carmichael n : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hXreal.le hαδ).trans hLambda
  have hlogLambda : 0 < Real.log (ArithmeticFunction.Carmichael n : ℝ) :=
    Real.log_pos hLambdaReal
  have hlogLower : δ * Real.log (X : ℝ) ≤
      Real.log (ArithmeticFunction.Carmichael n : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXpos δ) hLambda
    rwa [Real.log_rpow hXpos] at h
  have hratioNonneg : 0 ≤ Real.log ((X : ℝ) ^ α) /
      Real.log (ArithmeticFunction.Carmichael n : ℝ) :=
    div_nonneg (Real.log_nonneg hu.le) hlogLambda.le
  have hratioLe : Real.log ((X : ℝ) ^ α) /
      Real.log (ArithmeticFunction.Carmichael n : ℝ) ≤ α / δ := by
    apply (div_le_div_iff₀ hlogLambda hδ).mpr
    rw [Real.log_rpow hXpos]
    nlinarith [mul_le_mul_of_nonneg_left hlogLower hα.le]
  obtain ⟨d, hdvd, hdLambda, hdSize⟩ :=
    WeightedDivisor.exists_divisor hnSq hn1 hLambdaNat hsmooth hu huLambda
  have hdBound : (d : ℝ) ≤ (X : ℝ) ^ (α + α / δ) := by
    calc
      (d : ℝ) ≤ (X : ℝ) ^ α * (n : ℝ) ^
          (Real.log ((X : ℝ) ^ α) / Real.log (ArithmeticFunction.Carmichael n : ℝ)) :=
        hdSize
      _ ≤ (X : ℝ) ^ α * (X : ℝ) ^
          (Real.log ((X : ℝ) ^ α) / Real.log (ArithmeticFunction.Carmichael n : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.cast_le.mpr hnX) hratioNonneg)
          (Real.rpow_pos_of_pos hXpos α).le
      _ ≤ (X : ℝ) ^ α * (X : ℝ) ^ (α / δ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hXreal.le hratioLe)
          (Real.rpow_pos_of_pos hXpos α).le
      _ = (X : ℝ) ^ (α + α / δ) := (Real.rpow_add hXpos α (α / δ)).symm
  exact ⟨d, Nat.one_le_of_lt (CarmichaelCertificates.divisor_pos hn hdvd),
    Nat.le_floor hdBound, Nat.ceil_le.mpr hdLambda, hdvd⟩

/-- The smooth portion of the large-lambda set is covered by the weighted
small divisors and hence satisfies the logarithmic certificate bound. -/
theorem ncard_smooth_carmichaels_with_large_lambda_le {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ} (hX : 2 ≤ X) :
    ({n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      (X : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ) ∧
      ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ (X : ℝ) ^ savingExponent δ}.ncard : ℝ) ≤
      (X : ℝ) ^ (1 - savingExponent δ) *
        (2 + (1 - savingExponent δ) * Real.log (X : ℝ)) := by
  let α : ℝ := savingExponent δ
  let B : ℝ := (X : ℝ) ^ (1 - α)
  let D : ℕ := ⌊B⌋₊
  let V : ℕ := ⌈(X : ℝ) ^ α⌉₊
  let s : Set ℕ := {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
    (X : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ) ∧
    ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ (X : ℝ) ^ α}
  change (s.ncard : ℝ) ≤ B * (2 + (1 - α) * Real.log (X : ℝ))
  have hprop : 0 < α ∧ α < 1 / 2 ∧ α ≤ δ ∧ α + α / δ = 1 - α :=
    savingExponent_properties hδ
  obtain ⟨hαpos, hαhalf, hαδ, hbalance⟩ := hprop
  have hXreal : 1 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hX)
  have hXpos : 0 < (X : ℝ) := zero_lt_one.trans hXreal
  have hβpos : 0 < 1 - α := by linarith
  have hBpos : 0 < B := Real.rpow_pos_of_pos hXpos (1 - α)
  have hB1 : 1 ≤ B := Real.one_le_rpow hXreal.le hβpos.le
  have hD1 : 1 ≤ D := (Nat.one_le_floor_iff B).mpr hB1
  have hDreal1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hDpos : 0 < (D : ℝ) := zero_lt_one.trans_le hDreal1
  have hDle : (D : ℝ) ≤ B := Nat.floor_le hBpos.le
  have hV1 : 1 ≤ V := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hXpos α)
  have hVle : (X : ℝ) ^ α ≤ (V : ℝ) := Nat.le_ceil ((X : ℝ) ^ α)
  have hbounded : ∀ n ∈ s, n ≤ X ∧ IsCarmichael n := by
    rintro n ⟨hnX, hn, _, _⟩
    exact ⟨hnX, hn⟩
  have hcover : ∀ n ∈ s, ∃ d : ℕ,
      1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n := by
    rintro n ⟨hnX, hn, hLambda, hsmooth⟩
    obtain ⟨d, hd1, hdD, hdLambda, hdvd⟩ :=
      exists_divisor_of_smooth_large_lambda hδ hαpos hαδ hX hnX hn hLambda hsmooth
    rw [hbalance] at hdD
    exact ⟨d, hd1, hdD, hdLambda, hdvd⟩
  have hCount := CarmichaelCertificates.ncard_le_log_of_large_lambda_divisor_cover
    hV1 hbounded hcover
  have hRatio : (X : ℝ) / (V : ℝ) ≤ B := by
    calc
      (X : ℝ) / (V : ℝ) ≤ (X : ℝ) / (X : ℝ) ^ α :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg X)
          (Real.rpow_pos_of_pos hXpos α) hVle
      _ = B := by
        dsimp only [B]
        rw [Real.rpow_sub hXpos, Real.rpow_one]
  have hlogD : Real.log (D : ℝ) ≤ (1 - α) * Real.log (X : ℝ) := by
    calc
      Real.log (D : ℝ) ≤ Real.log B := Real.log_le_log hDpos hDle
      _ = (1 - α) * Real.log (X : ℝ) := Real.log_rpow hXpos (1 - α)
  have hlogDnonneg : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg hDreal1
  calc
    (s.ncard : ℝ) ≤ (D : ℝ) + (X : ℝ) / (V : ℝ) * (1 + Real.log (D : ℝ)) := hCount
    _ ≤ B + B * (1 + Real.log (D : ℝ)) :=
      add_le_add hDle (mul_le_mul_of_nonneg_right hRatio (by linarith))
    _ ≤ B + B * (1 + (1 - α) * Real.log (X : ℝ)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlogD) hBpos.le)
    _ = B * (2 + (1 - α) * Real.log (X : ℝ)) := by ring

/-- The finite large-prime tail at the rounded power cutoff. This generic
bound needs only `α ≥ 0` and `X ≥ 1`. -/
theorem ncard_carmichaels_with_prime_above_power_le {α : ℝ} (hα : 0 ≤ α)
    {X : ℕ} (hX : 1 ≤ X) :
    ({n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      ∃ p : ℕ, p.Prime ∧ ⌊(X : ℝ) ^ α⌋₊ < p ∧ p ∣ n}.ncard : ℝ) ≤
      2 * (X : ℝ) ^ (1 - α) := by
  have hXreal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := zero_lt_one.trans_le hXreal
  have hu1 : 1 ≤ (X : ℝ) ^ α := Real.one_le_rpow hXreal hα
  have hy1 : 1 ≤ ⌊(X : ℝ) ^ α⌋₊ := (Nat.one_le_floor_iff _).mpr hu1
  calc
    _ ≤ (X : ℝ) / (⌊(X : ℝ) ^ α⌋₊ : ℝ) :=
      CarmichaelPrimeTail.ncard_carmichaels_with_large_prime_factor_le_real hy1 X
    _ ≤ (X : ℝ) / ((X : ℝ) ^ α / 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg X)
        (div_pos (Real.rpow_pos_of_pos hXpos α) (by norm_num))
        (half_le_nat_floor hu1)
    _ = 2 * ((X : ℝ) / (X : ℝ) ^ α) := by
      rw [div_div_eq_mul_div]
      ring
    _ = 2 * (X : ℝ) ^ (1 - α) := by
      rw [Real.rpow_sub hXpos, Real.rpow_one]

/-- Uniform finite upper reduction for large lambda. For every real `δ > 0`
and natural `X ≥ 2`, with `α = δ / (1 + 2 * δ)`, the large-lambda Carmichael
count is at most `X ^ (1 - α) * (4 + (1 - α) * log X)`.
This is not a density theorem or a negation of one. -/
theorem ncard_carmichaels_with_large_lambda_le {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ} (hX : 2 ≤ X) :
    ({n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      (X : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ)}.ncard : ℝ) ≤
      (X : ℝ) ^ (1 - δ / (1 + 2 * δ)) *
        (4 + (1 - δ / (1 + 2 * δ)) * Real.log (X : ℝ)) := by
  let α : ℝ := savingExponent δ
  let B : ℝ := (X : ℝ) ^ (1 - α)
  let large : Set ℕ := {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
    (X : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ)}
  let tail : Set ℕ := {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
    ∃ p : ℕ, p.Prime ∧ ⌊(X : ℝ) ^ α⌋₊ < p ∧ p ∣ n}
  let smooth : Set ℕ := {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
    (X : ℝ) ^ δ ≤ (ArithmeticFunction.Carmichael n : ℝ) ∧
    ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ (X : ℝ) ^ α}
  change (large.ncard : ℝ) ≤ B * (4 + (1 - α) * Real.log (X : ℝ))
  have hαpos : 0 < α := (savingExponent_properties hδ).1
  have hXreal : 1 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hX)
  have hXpos : 0 < (X : ℝ) := zero_lt_one.trans hXreal
  have htailFinite : tail.Finite :=
    CarmichaelPrimeTail.carmichaels_with_large_prime_factor_finite ⌊(X : ℝ) ^ α⌋₊ X
  have hsmoothFinite : smooth.Finite := (Set.finite_le_nat X).subset (by
    intro n hn
    exact hn.1)
  have hsplit : large ⊆ tail ∪ smooth := by
    rintro n ⟨hnX, hn, hLambda⟩
    by_cases hlargePrime : ∃ p : ℕ, p.Prime ∧ ⌊(X : ℝ) ^ α⌋₊ < p ∧ p ∣ n
    · exact Or.inl ⟨hnX, hn, hlargePrime⟩
    · apply Or.inr
      refine ⟨hnX, hn, hLambda, ?_⟩
      intro p hp hpn
      have hpfloor : p ≤ ⌊(X : ℝ) ^ α⌋₊ :=
        le_of_not_gt (fun h => hlargePrime ⟨p, hp, h, hpn⟩)
      calc
        (p : ℝ) ≤ (⌊(X : ℝ) ^ α⌋₊ : ℝ) := Nat.cast_le.mpr hpfloor
        _ ≤ (X : ℝ) ^ α := Nat.floor_le (Real.rpow_pos_of_pos hXpos α).le
  have hcard : (large.ncard : ℝ) ≤ (tail.ncard : ℝ) + (smooth.ncard : ℝ) := by
    exact_mod_cast
      (Set.ncard_le_ncard hsplit (htailFinite.union hsmoothFinite)).trans
        (Set.ncard_union_le tail smooth)
  have htail : (tail.ncard : ℝ) ≤ 2 * B :=
    ncard_carmichaels_with_prime_above_power_le hαpos.le (by omega : 1 ≤ X)
  have hsmooth : (smooth.ncard : ℝ) ≤ B * (2 + (1 - α) * Real.log (X : ℝ)) :=
    ncard_smooth_carmichaels_with_large_lambda_le hδ hX
  calc
    (large.ncard : ℝ) ≤ (tail.ncard : ℝ) + (smooth.ncard : ℝ) := hcard
    _ ≤ 2 * B + B * (2 + (1 - α) * Real.log (X : ℝ)) := add_le_add htail hsmooth
    _ = B * (4 + (1 - α) * Real.log (X : ℝ)) := by ring

end Erdos1057.CarmichaelLargeLambda
