import Submission.ProductConductorMean

/-!
# An unbalanced Vaughan mean majorant

The Type II block estimate retains both the Q-squared term and the short-side
saving. This allows small conductor groups to be estimated without requiring
both block lengths to be at most Q-squared.
-/

open Nat Finset ArithmeticFunction
open scoped Classical BigOperators

namespace Erdos821.AnalyticSieve

set_option maxHeartbeats 2000000

lemma large_sieve_kernel_sqrt_le (Q X : ℕ) (hX : 1 ≤ X) :
    Real.sqrt (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) ≤
      2 * (Q : ℝ) + 6 * Real.sqrt X := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Nat.cast_nonneg (α := ℝ) X)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hroot := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) X)
    have hcross : 0 ≤ (Q : ℝ) * Real.sqrt X := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    nlinarith

lemma typeIIBlockMajorant_unbalanced_le (Q X Y : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (T R H : ℝ) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 1 ≤ H)
    (hXY : (X : ℝ) * Y ≤ T ^ 2)
    (hroots : Real.sqrt X + Real.sqrt Y ≤ R)
    (hlogX : 1 + Real.log X ≤ H) (hlogY : Real.log Y ≤ H) :
    typeIIBlockMajorant Q X Y ≤ 36 * T * H ^ 3 * ((Q : ℝ) ^ 2 + Q * R + T) := by
  let A : ℝ := 2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)
  let B : ℝ := 2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)
  let Z : ℝ := (1 + Real.log X) ^ 3 * Real.log Y ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 ≤ Z := by
    have hx := Real.log_natCast_nonneg X
    dsimp [Z]
    positivity
  have hH0 : 0 ≤ H := by linarith
  have hlog : Z ≤ H ^ 6 := by
    calc
      _ ≤ H ^ 3 * H ^ 2 := mul_le_mul
        (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg X]) hlogX 3)
        (pow_le_pow_left₀ (Real.log_natCast_nonneg Y) hlogY 2)
        (sq_nonneg _) (pow_nonneg hH0 _)
      _ ≤ H ^ 6 := by
        have h := mul_nonneg (pow_nonneg hH0 5) (sub_nonneg.mpr hH)
        nlinarith
  have hlogroot : Real.sqrt Z ≤ H ^ 3 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨pow_nonneg hH0 _, by simpa only [← pow_mul] using hlog⟩
  have hXYroot : Real.sqrt ((X : ℝ) * Y) ≤ T := Real.sqrt_le_iff.mpr ⟨hT, hXY⟩
  have hrootprod : Real.sqrt X * Real.sqrt Y ≤ T := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) X)]
    exact hXYroot
  have hk : Real.sqrt A * Real.sqrt B ≤ 36 * ((Q : ℝ) ^ 2 + Q * R + T) := by
    calc
      _ ≤ (2 * (Q : ℝ) + 6 * Real.sqrt X) * (2 * (Q : ℝ) + 6 * Real.sqrt Y) :=
        mul_le_mul (large_sieve_kernel_sqrt_le Q X hX) (large_sieve_kernel_sqrt_le Q Y hY)
          (Real.sqrt_nonneg _) (by positivity)
      _ ≤ _ := by
        have hsum := mul_le_mul_of_nonneg_left hroots (Nat.cast_nonneg (α := ℝ) Q)
        have hQR : 0 ≤ (Q : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR
        nlinarith [sq_nonneg (Q : ℝ)]
  have heq : typeIIBlockMajorant Q X Y =
      (Real.sqrt A * Real.sqrt B) * Real.sqrt ((X : ℝ) * Y) * Real.sqrt Z := by
    unfold typeIIBlockMajorant
    have hrad : (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
        (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
        ((X : ℝ) * (1 + Real.log X) ^ 3) * ((Y : ℝ) * Real.log Y ^ 2) =
        (A * B) * ((X : ℝ) * Y) * Z := by dsimp only [A, B, Z]; ring
    rw [hrad, Real.sqrt_mul (mul_nonneg (mul_nonneg hA hB)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))),
      Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_mul hA]
  rw [heq]
  calc
    _ ≤ (36 * ((Q : ℝ) ^ 2 + Q * R + T)) * T * H ^ 3 :=
      mul_le_mul (mul_le_mul hk hXYroot (Real.sqrt_nonneg _) (by positivity))
        hlogroot (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

noncomputable def unbalancedTypeIIMajorant (N Q B : ℕ) : ℝ :=
  (6 + 2 * Real.log ((N : ℝ) + 1)) * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
    (288 * (1 + Real.log (2 * (N : ℝ) + 1)) ^ 3 *
      ((Q : ℝ) ^ 2 * Real.sqrt N + (Q : ℝ) * N / B + N))

lemma unbalancedTypeIIMajorant_nonneg (N Q B : ℕ) :
    0 ≤ unbalancedTypeIIMajorant N Q B := by
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hlog2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
  unfold unbalancedTypeIIMajorant
  positivity

lemma dyadic_majorant_unbalanced_le (U V N Q B : ℕ) (hB : 1 ≤ B)
    (hBU : B ^ 2 ≤ U + 1) (hBV : B ^ 2 ≤ V) :
    (6 + 2 * Real.log ((N : ℝ) + 1)) *
        (∑ j ∈ typeIILevels N U V, typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j)) ≤
      unbalancedTypeIIMajorant N Q B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hV : 1 ≤ V := by nlinarith
  let H : ℝ := 1 + Real.log (2 * (N : ℝ) + 1)
  have hH : 1 ≤ H := by
    dsimp [H]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hscale (j : ℕ) (hj : j ∈ typeIILevels N U V) :
      typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j) ≤
        288 * H ^ 3 * ((Q : ℝ) ^ 2 * Real.sqrt N + (Q : ℝ) * N / B + N) := by
    obtain ⟨hjrange, hVj, hUj⟩ := mem_filter.mp hj
    have hp : 0 < 2 ^ j := by positivity
    have hX : 1 ≤ 2 ^ (j + 1) := Nat.one_le_of_lt (by positivity)
    have hY : 1 ≤ N / 2 ^ j := by
      apply (Nat.le_div_iff_mul_le hp).mpr
      nlinarith
    have hprod := Nat.mul_div_le N (2 ^ j)
    have hXbound : 2 ^ (j + 1) * B ^ 2 ≤ 2 * N := by
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul_right (2 ^ j) hBU]
    have hYbound : (N / 2 ^ j) * B ^ 2 ≤ 2 * N := by
      rw [pow_succ] at hVj
      have h := Nat.mul_le_mul_right (N / 2 ^ j) hBV
      nlinarith
    have hrootbound (X : ℕ) (hXN : X * B ^ 2 ≤ 2 * N) :
        Real.sqrt X ≤ 2 * Real.sqrt N / B := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [div_pow]
      apply (le_div_iff₀ (pow_pos hBpos 2)).mpr
      have hcast : (X : ℝ) * (B : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by exact_mod_cast hXN
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N), Nat.cast_nonneg (α := ℝ) N]
    have hroots : Real.sqrt (2 ^ (j + 1) : ℕ) + Real.sqrt (N / 2 ^ j : ℕ) ≤
        4 * Real.sqrt N / B := by
      have hx := hrootbound _ hXbound
      have hy := hrootbound _ hYbound
      calc
        _ ≤ 2 * Real.sqrt N / B + 2 * Real.sqrt N / B := _root_.add_le_add hx hy
        _ = _ := by ring
    have hXY : ((2 ^ (j + 1) : ℕ) : ℝ) * (N / 2 ^ j : ℕ) ≤ (2 * Real.sqrt N) ^ 2 := by
      have hXYnat : 2 ^ (j + 1) * (N / 2 ^ j) ≤ 2 * N := by rw [pow_succ]; nlinarith
      have hcast : ((2 ^ (j + 1) : ℕ) : ℝ) * (N / 2 ^ j : ℕ) ≤ 2 * (N : ℝ) := by
        exact_mod_cast hXYnat
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N), Nat.cast_nonneg (α := ℝ) N]
    have hXle : 2 ^ (j + 1) ≤ 2 * N := by rw [pow_succ]; nlinarith
    have hlogX : 1 + Real.log (2 ^ (j + 1) : ℕ) ≤ H := by
      have h := log_nat_mono (show 2 ^ (j + 1) ≤ 2 * N + 1 by omega)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
      dsimp only [H]
      linarith
    have hlogY : Real.log (N / 2 ^ j : ℕ) ≤ H := by
      have h := log_nat_mono ((Nat.div_le_self N (2 ^ j)).trans (show N ≤ 2 * N + 1 by omega))
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
      dsimp only [H]
      linarith
    have h := typeIIBlockMajorant_unbalanced_le Q _ _ hX hY
      (2 * Real.sqrt N) (4 * Real.sqrt N / B) H (by positivity) (by positivity)
      hH hXY hroots hlogX hlogY
    apply h.trans
    have heq : 36 * (2 * Real.sqrt N) * H ^ 3 *
        ((Q : ℝ) ^ 2 + Q * (4 * Real.sqrt N / B) + 2 * Real.sqrt N) =
        H ^ 3 * (72 * (Q : ℝ) ^ 2 * Real.sqrt N + 288 * (Q : ℝ) * N / B + 144 * N) := by
      have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
      field_simp
      nlinarith only [hs]
    rw [heq]
    have hterm : 72 * (Q : ℝ) ^ 2 * Real.sqrt N + 288 * (Q : ℝ) * N / B + 144 * N ≤
        288 * ((Q : ℝ) ^ 2 * Real.sqrt N + (Q : ℝ) * N / B + N) := by
      have hnon : 0 ≤ 216 * (Q : ℝ) ^ 2 * Real.sqrt N + 144 * N := by positivity
      calc
        _ = 288 * ((Q : ℝ) ^ 2 * Real.sqrt N + (Q : ℝ) * N / B + N) -
            (216 * (Q : ℝ) ^ 2 * Real.sqrt N + 144 * N) := by ring
        _ ≤ _ := sub_le_self _ hnon
    have hmul := mul_le_mul_of_nonneg_left hterm (pow_nonneg (show 0 ≤ H by linarith) 3)
    convert hmul using 1; ring
  have hcard : (typeIILevels N U V).card ≤ Nat.log 2 N + 1 :=
    (card_filter_le _ _).trans_eq (card_range _)
  have hK : 0 ≤ 288 * H ^ 3 * ((Q : ℝ) ^ 2 * Real.sqrt N + (Q : ℝ) * N / B + N) := by
    have hH0 : 0 ≤ H := by linarith
    positivity
  unfold unbalancedTypeIIMajorant
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith)
  calc
    _ ≤ ∑ _j ∈ typeIILevels N U V,
        288 * H ^ 3 * ((Q : ℝ) ^ 2 * Real.sqrt N + (Q : ℝ) * N / B + N) := sum_le_sum hscale
    _ = ((typeIILevels N U V).card : ℝ) * _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hK

/-- A general primitive-character mean estimate with a closed Type II bound.
No comparison between Q-squared and the individual block lengths is needed. -/
theorem primitive_vonMangoldt_unbalanced_mean_bound
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, 2 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (U V N B : ℕ) (hB : 1 ≤ B) (hBU : B ^ 2 ≤ U + 1) (hBV : B ^ 2 ≤ V)
    (R : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hR : ∀ q ∈ M, ∀ χ ∈ C q, R q χ ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖twistedArithmeticSum χ vonMangoldt (R q χ)‖) ≤
      (Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q + unbalancedTypeIIMajorant N Q B := by
  have hV : 1 ≤ V := by nlinarith
  apply (primitive_vonMangoldt_mean_bound M Q hQ hM C hC U V N hV R hR).trans
  exact _root_.add_le_add le_rfl (dyadic_majorant_unbalanced_le U V N Q B hB hBU hBV)

end Erdos821.AnalyticSieve

namespace Erdos821

open AnalyticSieve

noncomputable def productUnbalancedMajorant (U V N B s m : ℕ) : ℝ :=
  let Q := (progressionScaleN (m + 1)) ^ s
  ((Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q + unbalancedTypeIIMajorant N Q B) /
    (progressionScaleN m : ℝ) ^ s

lemma productUnbalancedMajorant_nonneg (U V N B s m : ℕ) :
    0 ≤ productUnbalancedMajorant U V N B s m := by
  unfold productUnbalancedMajorant
  exact div_nonneg (add_nonneg
    (mul_nonneg (sq_nonneg _) (vaughanShortMajorant_nonneg _ _ _ _))
    (unbalancedTypeIIMajorant_nonneg _ _ _)) (pow_nonneg (Nat.cast_nonneg _) _)

lemma productVaughanMajorant_le_unbalanced (U V N B s m : ℕ) (hB : 1 ≤ B)
    (hBU : B ^ 2 ≤ U + 1) (hBV : B ^ 2 ≤ V) :
    productVaughanMajorant U V N s m ≤ productUnbalancedMajorant U V N B s m := by
  unfold productVaughanMajorant productUnbalancedMajorant
  exact div_le_div_of_nonneg_right
    (_root_.add_le_add le_rfl (dyadic_majorant_unbalanced_le U V N _ B hB hBU hBV))
    (pow_nonneg (Nat.cast_nonneg _) _)

theorem primitiveProductMangoldtMean_le_unbalanced (U V N B s m : ℕ)
    (hs : 1 ≤ s) (hB : 1 ≤ B) (hBU : B ^ 2 ≤ U + 1) (hBV : B ^ 2 ≤ V) :
    primitiveProductMangoldtMean s m N ≤ productUnbalancedMajorant U V N B s m := by
  have hV : 1 ≤ V := by nlinarith
  exact (primitiveProductMangoldtMean_le_vaughan U V N s m hs hV).trans
    (productVaughanMajorant_le_unbalanced U V N B s m hB hBU hBV)

end Erdos821
