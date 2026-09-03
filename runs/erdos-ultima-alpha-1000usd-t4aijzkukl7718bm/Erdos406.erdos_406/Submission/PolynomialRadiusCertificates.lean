import Submission.NewmanQuotientCertificate

/-! Exact polynomial identities certifying root-radius bounds. These bounds
are independent of any assertion that a polynomial divides a Newman polynomial. -/
namespace Erdos406RadiusCertificate
open Polynomial Erdos406Quotient

def weightAt (r : ℝ) : List ℤ → ℝ
  | [] => 0
  | a :: w => |(a : ℝ)| + r * weightAt r w

lemma weightAt_nonneg (r : ℝ) (hr : 0 ≤ r) (w : List ℤ) : 0 ≤ weightAt r w := by
  induction w with
  | nil => simp [weightAt]
  | cons a w ih => simp only [weightAt]; positivity

lemma norm_eval_listPoly_le (w : List ℤ) (z : ℂ) :
    ‖((listPoly w).map (Int.castRingHom ℂ)).eval z‖ ≤ weightAt ‖z‖ w := by
  induction w with
  | nil => simp [listPoly, weightAt]
  | cons a w ih =>
    have hh := norm_add_le (a : ℂ) (z * ((listPoly w).map (Int.castRingHom ℂ)).eval z)
    rw [norm_mul, Complex.norm_intCast] at hh
    simp only [listPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, eval_add, eval_C, eval_mul, eval_X, weightAt]
    exact hh.trans (by gcongr)

lemma weightAt_scale_bound (ρ r : ℝ) (hρ : 0 ≤ ρ) (hr : ρ ≤ r)
    (w : List ℤ) (m : ℕ) (hm : w.length ≤ m) :
    ρ ^ m * weightAt r w ≤ r ^ m * weightAt ρ w := by
  have hr0 : 0 ≤ r := hρ.trans hr
  induction w generalizing m with
  | nil => simp [weightAt]
  | cons a w ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      have ht := ih m (by simpa using hm)
      have htm := mul_le_mul_of_nonneg_left ht (mul_nonneg hρ hr0)
      have ha := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hr (m + 1))
        (abs_nonneg (a : ℝ))
      simp only [weightAt]
      simp only [pow_succ] at ha ⊢
      nlinarith

/-- If X^m equals a short remainder modulo Q, and the remainder has smaller
weighted coefficient sum at radiusρ, then every root of Q lies insideρ. -/
theorem root_norm_lt_of_remainder (Q : ℤ[X]) (S R : List ℤ) (m : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hlen : R.length ≤ m)
    (hcert : listPoly S * Q = X ^ m - listPoly R)
    (hsmall : weightAt ρ R < ρ ^ m) (z : ℂ)
    (hz : (Q.map (Int.castRingHom ℂ)).eval z = 0) : ‖z‖ < ρ := by
  have he := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℂ)).eval z) hcert
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    eval_mul, eval_sub, eval_pow, eval_X, hz, mul_zero] at he
  have hb := norm_eval_listPoly_le R z
  rw [← sub_eq_zero.mp he.symm, norm_pow] at hb
  by_contra hh
  have hr := le_of_not_gt hh
  have hr0 : 0 < ‖z‖ := hρ.trans_le hr
  have hs := weightAt_scale_bound ρ ‖z‖ hρ.le hr R m hlen
  have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hρ.le m)
  have ht := mul_lt_mul_of_pos_left hsmall (pow_pos hr0 m)
  nlinarith

#print axioms root_norm_lt_of_remainder
end Erdos406RadiusCertificate
