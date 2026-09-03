import Submission.VaughanMean

/-!
# A balanced-range primitive-character mean estimate

In the regime `2N ≤ VQ²` and `2N ≤ (U+1)Q²`, every active Type II block
has both side lengths at most Q². Its dyadic majorant then simplifies to
an explicit `Q² sqrt(N)` bound with logarithmic factors.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

lemma large_sieve_kernel_le (Q X : ℕ) (hQ : 0 < Q) (hX : X ≤ Q ^ 2) :
    2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1) ≤ 64 * (Q : ℝ) ^ 2 := by
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hX' : (X : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hX
  have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Nat.cast_nonneg (α := ℝ) X)
  nlinarith

lemma typeIIBlockMajorant_balanced_le (Q X Y : ℕ) (hQ : 0 < Q)
    (hX : X ≤ Q ^ 2) (hY : Y ≤ Q ^ 2)
    (T H : ℝ) (hT : 0 ≤ T) (hH : 1 ≤ H) (hXY : (X : ℝ) * Y ≤ T ^ 2)
    (hlogX : 1 + Real.log X ≤ H) (hlogY : Real.log Y ≤ H) :
    typeIIBlockMajorant Q X Y ≤ 64 * (Q : ℝ) ^ 2 * T * H ^ 3 := by
  have hH0 : 0 ≤ H := by linarith
  have hLX : 0 ≤ 1 + Real.log X := by linarith [Real.log_natCast_nonneg X]
  have hLY : 0 ≤ Real.log Y := Real.log_natCast_nonneg Y
  have hkX := large_sieve_kernel_le Q X hQ hX
  have hkY := large_sieve_kernel_le Q Y hQ hY
  have hkk : (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
      (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) ≤ (64 * (Q : ℝ) ^ 2) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hkX hkY (by positivity) (by positivity)
  have hlog : (1 + Real.log X) ^ 3 * (Real.log Y) ^ 2 ≤ H ^ 6 := by
    calc
      _ ≤ H ^ 3 * H ^ 2 := mul_le_mul
        (pow_le_pow_left₀ hLX hlogX 3) (pow_le_pow_left₀ hLY hlogY 2) (by positivity) (by positivity)
      _ ≤ H ^ 6 := by
        have h := mul_nonneg (pow_nonneg hH0 5) (sub_nonneg.mpr hH)
        nlinarith
  unfold typeIIBlockMajorant
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · calc
      _ = ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1))) * ((X : ℝ) * Y) *
          ((1 + Real.log X) ^ 3 * (Real.log Y) ^ 2) := by ring
      _ ≤ (64 * (Q : ℝ) ^ 2) ^ 2 * T ^ 2 * H ^ 6 :=
        mul_le_mul (mul_le_mul hkk hXY (by positivity) (by positivity)) hlog
          (by positivity) (by positivity)
      _ = _ := by ring

noncomputable def balancedTypeIIMajorant (N Q : ℕ) : ℝ :=
  (6 + 2 * Real.log ((N : ℝ) + 1)) * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
    (128 * (Q : ℝ) ^ 2 * Real.sqrt N * (1 + Real.log (2 * (N : ℝ) + 1)) ^ 3)

lemma dyadic_majorant_balanced_le (U V N Q : ℕ) (hV : 1 ≤ V) (hQ : 0 < Q)
    (hNU : 2 * N ≤ (U + 1) * Q ^ 2) (hNV : 2 * N ≤ V * Q ^ 2) :
    (6 + 2 * Real.log ((N : ℝ) + 1)) *
        (∑ j ∈ typeIILevels N U V, typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j)) ≤
      balancedTypeIIMajorant N Q := by
  have hscale (j : ℕ) (hj : j ∈ typeIILevels N U V) :
      typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j) ≤
        128 * (Q : ℝ) ^ 2 * Real.sqrt N * (1 + Real.log (2 * (N : ℝ) + 1)) ^ 3 := by
    obtain ⟨hjrange, hVj, hUj⟩ := mem_filter.mp hj
    have ha : 0 < 2 ^ j := by positivity
    have hprod := Nat.mul_div_le N (2 ^ j)
    have hXQ : 2 ^ (j + 1) ≤ Q ^ 2 := by
      rw [pow_succ]
      nlinarith
    have hYQ : N / 2 ^ j ≤ Q ^ 2 := by
      rw [pow_succ] at hVj
      have h' : V * (N / 2 ^ j) ≤ 2 * N := by nlinarith
      nlinarith
    have hX : 2 ^ (j + 1) ≤ 2 * N := by
      rw [pow_succ]
      nlinarith
    have hY : N / 2 ^ j ≤ N := Nat.div_le_self _ _
    have hXYnat : 2 ^ (j + 1) * (N / 2 ^ j) ≤ 2 * N := by rw [pow_succ]; nlinarith
    have hXY : ((2 ^ (j + 1) : ℕ) : ℝ) * (N / 2 ^ j : ℕ) ≤ (2 * Real.sqrt N) ^ 2 := by
      have hcast : ((2 ^ (j + 1) : ℕ) : ℝ) * (N / 2 ^ j : ℕ) ≤ 2 * (N : ℝ) := by
        exact_mod_cast hXYnat
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N), Nat.cast_nonneg (α := ℝ) N]
    have hH : 1 ≤ 1 + Real.log (2 * (N : ℝ) + 1) := by
      have := Real.log_nonneg (show 1 ≤ 2 * (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
      linarith
    have hlogX : 1 + Real.log (2 ^ (j + 1) : ℕ) ≤ 1 + Real.log (2 * (N : ℝ) + 1) := by
      have h := log_nat_mono (show 2 ^ (j + 1) ≤ 2 * N + 1 by omega)
      push_cast at h
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using add_le_add (a := (1 : ℝ)) le_rfl h
    have hlogY : Real.log (N / 2 ^ j : ℕ) ≤ 1 + Real.log (2 * (N : ℝ) + 1) := by
      have h := log_nat_mono (show N / 2 ^ j ≤ 2 * N + 1 by omega)
      push_cast at h
      linarith
    have h := typeIIBlockMajorant_balanced_le Q _ _ hQ hXQ hYQ
      (2 * Real.sqrt N) _ (by positivity) hH hXY hlogX hlogY
    convert h using 1; ring
  have hlog : 0 ≤ Real.log (2 * (N : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hK : 0 ≤ 128 * (Q : ℝ) ^ 2 * Real.sqrt N * (1 + Real.log (2 * (N : ℝ) + 1)) ^ 3 := by positivity
  have hcard : (typeIILevels N U V).card ≤ Nat.log 2 N + 1 := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  unfold balancedTypeIIMajorant
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by
    have := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
    positivity)
  calc
    _ ≤ ∑ j ∈ typeIILevels N U V,
        128 * (Q : ℝ) ^ 2 * Real.sqrt N * (1 + Real.log (2 * (N : ℝ) + 1)) ^ 3 :=
      Finset.sum_le_sum hscale
    _ = ((typeIILevels N U V).card : ℝ) *
        (128 * (Q : ℝ) ^ 2 * Real.sqrt N * (1 + Real.log (2 * (N : ℝ) + 1)) ^ 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hK

/-- A balanced-range mean bound with no unevaluated dyadic sum. -/
theorem primitive_vonMangoldt_balanced_mean_bound
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, 2 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (U V N : ℕ) (hV : 1 ≤ V)
    (hNU : 2 * N ≤ (U + 1) * Q ^ 2) (hNV : 2 * N ≤ V * Q ^ 2)
    (R : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hR : ∀ q ∈ M, ∀ χ ∈ C q, R q χ ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖twistedArithmeticSum χ vonMangoldt (R q χ)‖) ≤
      (Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q + balancedTypeIIMajorant N Q := by
  apply (primitive_vonMangoldt_mean_bound M Q hQ hM C hC U V N hV R hR).trans
  exact add_le_add le_rfl (dyadic_majorant_balanced_le U V N Q hV hQ hNU hNV)

end Erdos821.AnalyticSieve
