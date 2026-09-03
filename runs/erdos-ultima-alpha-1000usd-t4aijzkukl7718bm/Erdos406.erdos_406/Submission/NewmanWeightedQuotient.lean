import Submission.NewmanQuotientCertificate

/-! Weighted dominant-coefficient certificates for Newman divisors.
The radius is rational and every certificate inequality can be checked using
exact arithmetic. This is a certificate framework, not a global factor bound. -/
namespace Erdos406WeightedQuotient
open Polynomial Erdos406Quotient

def weightedWeight (ρ : ℚ) : List ℤ → ℚ
  | [] => 0
  | a :: w => |(a : ℚ)| + ρ * weightedWeight ρ w

lemma weightedWeight_nonneg (ρ : ℚ) (hρ : 0 ≤ ρ) (w : List ℤ) :
    0 ≤ weightedWeight ρ w := by
  induction w with
  | nil => simp [weightedWeight]
  | cons a w ih => simp only [weightedWeight]; positivity

lemma weighted_listPoly_mul_bound (ρ : ℚ) (hρ : 0 ≤ ρ) (w : List ℤ)
    (R : ℤ[X]) (M : ℚ) (hM : 0 ≤ M)
    (hR : ∀ i, |(R.coeff i : ℚ)| * ρ ^ i ≤ M) (n : ℕ) :
    |((listPoly w * R).coeff n : ℚ)| * ρ ^ n ≤ weightedWeight ρ w * M := by
  induction w generalizing n with
  | nil => simp [listPoly, weightedWeight]
  | cons a w ih =>
    cases n with
    | zero =>
      have hh := mul_le_mul_of_nonneg_left (hR 0) (abs_nonneg (a : ℚ))
      have hw := weightedWeight_nonneg ρ hρ w
      have hwM := mul_nonneg hρ (mul_nonneg hw hM)
      simp only [pow_zero, mul_one] at hh
      simp only [listPoly, add_mul, mul_assoc, coeff_add, coeff_C_mul,
        coeff_X_mul_zero, add_zero, Int.cast_mul, abs_mul, weightedWeight,
        pow_zero, mul_one]
      nlinarith
    | succ n =>
      have ha := mul_le_mul_of_nonneg_left (hR (n + 1)) (abs_nonneg (a : ℚ))
      have ht := mul_le_mul_of_nonneg_left (ih n) hρ
      have hh := mul_le_mul_of_nonneg_right
        (abs_add_le ((a : ℚ) * (R.coeff (n + 1) : ℚ))
          (((listPoly w * R).coeff n : ℤ) : ℚ)) (pow_nonneg hρ (n + 1))
      simp only [listPoly, add_mul, mul_assoc, coeff_add, coeff_C_mul,
        coeff_X_mul, Int.cast_add, Int.cast_mul, weightedWeight]
      rw [abs_mul] at hh
      rw [pow_succ] at ha hh ⊢
      nlinarith

lemma exists_max_weighted_coeff (ρ : ℚ) (hρ : 0 ≤ ρ) (R : ℤ[X]) :
    ∃ j, ∀ i, |(R.coeff i : ℚ)| * ρ ^ i ≤ |(R.coeff j : ℚ)| * ρ ^ j := by
  obtain ⟨j, hj, hmax⟩ := (Finset.range (R.natDegree + 1)).exists_max_image
    (fun i => |(R.coeff i : ℚ)| * ρ ^ i) (by simp)
  refine ⟨j, fun i => ?_⟩
  by_cases hi : i ≤ R.natDegree
  · exact hmax i (by simpa using Nat.lt_succ_of_le hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < i)]
    simp only [Int.cast_zero, abs_zero, zero_mul]
    positivity

/-- Soundness of a rationally weighted dominant-coefficient identity. -/
theorem weighted_quotient_bound (ρ : ℚ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (Q P R : ℤ[X]) (S E : List ℤ) (a : ℤ) (m : ℕ)
    (hPR : P = Q * R)
    (hcert : listPoly S * Q = monomial m a + listPoly E)
    (hP : ∀ i, |P.coeff i| ≤ 1) :
    ∀ i, (|(a : ℚ)| * ρ ^ m - weightedWeight ρ E) *
      (|(R.coeff i : ℚ)| * ρ ^ i) ≤ weightedWeight ρ S := by
  obtain ⟨j, hj⟩ := exists_max_weighted_coeff ρ hρ R
  let M : ℚ := |(R.coeff j : ℚ)| * ρ ^ j
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : ∀ i, |(R.coeff i : ℚ)| * ρ ^ i ≤ M := hj
  have hP' : ∀ i, |(P.coeff i : ℚ)| * ρ ^ i ≤ 1 := by
    intro i
    have ha : |(P.coeff i : ℚ)| ≤ 1 := by exact_mod_cast hP i
    have hp : ρ ^ i ≤ 1 := pow_le_one₀ hρ hρ1
    nlinarith [pow_nonneg hρ i, abs_nonneg (P.coeff i : ℚ)]
  have hcoefZ : a * R.coeff j =
      (listPoly S * P).coeff (j + m) - (listPoly E * R).coeff (j + m) := by
    have he : monomial m a * R = listPoly S * P - listPoly E * R := by
      rw [hPR, ← mul_assoc, hcert]
      ring
    have hh := congrArg (fun p : ℤ[X] => p.coeff (j + m)) he
    simpa only [coeff_monomial_mul, coeff_sub] using hh
  have hcoef : (a : ℚ) * (R.coeff j : ℚ) =
      ((listPoly S * P).coeff (j + m) : ℚ) -
        ((listPoly E * R).coeff (j + m) : ℚ) := by exact_mod_cast hcoefZ
  have hS := weighted_listPoly_mul_bound ρ hρ S P 1 (by norm_num) hP' (j + m)
  have hE := weighted_listPoly_mul_bound ρ hρ E R M hM hR (j + m)
  have hb : (|(a : ℚ)| * ρ ^ m) * M ≤
      weightedWeight ρ S + weightedWeight ρ E * M := by
    calc
      _ = |(a : ℚ) * (R.coeff j : ℚ)| * ρ ^ (j + m) := by
        rw [abs_mul, pow_add]
        dsimp [M]
        ring
      _ ≤ (|((listPoly S * P).coeff (j + m) : ℚ)| +
          |((listPoly E * R).coeff (j + m) : ℚ)|) * ρ ^ (j + m) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ _)
        rw [hcoef]
        exact abs_sub _ _
      _ ≤ _ := by nlinarith
  intro i
  by_cases he : 0 ≤ |(a : ℚ)| * ρ ^ m - weightedWeight ρ E
  · have hh := mul_le_mul_of_nonneg_left (hR i) he
    nlinarith
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge he)
      (show 0 ≤ |(R.coeff i : ℚ)| * ρ ^ i by positivity)
    exact hh.trans (weightedWeight_nonneg ρ hρ S)

/-- A convenient integer cutoff extracted from the weighted inequality.
The last two inequalities are exact rational arithmetic checks. -/
lemma weighted_quotient_integer_bound (ρ : ℚ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Q P R : ℤ[X]) (S E : List ℤ) (a : ℤ) (m i : ℕ) (B : ℤ)
    (hPR : P = Q * R)
    (hcert : listPoly S * Q = monomial m a + listPoly E)
    (hP : ∀ j, |P.coeff j| ≤ 1)
    (hgap : 0 < |(a : ℚ)| * ρ ^ m - weightedWeight ρ E)
    (hB : weightedWeight ρ S <
      (|(a : ℚ)| * ρ ^ m - weightedWeight ρ E) * ρ ^ i * ((B : ℚ) + 1)) :
    |R.coeff i| ≤ B := by
  have hb := weighted_quotient_bound ρ hρ.le hρ1 Q P R S E a m hPR hcert hP i
  by_contra hh
  have hbi : B + 1 ≤ |R.coeff i| := by omega
  have hbiQ : (B : ℚ) + 1 ≤ |(R.coeff i : ℚ)| := by exact_mod_cast hbi
  have ht := mul_le_mul_of_nonneg_left hbiQ (le_of_lt (mul_pos hgap (pow_pos hρ i)))
  nlinarith

#print axioms weighted_quotient_bound
#print axioms weighted_quotient_integer_bound
end Erdos406WeightedQuotient
