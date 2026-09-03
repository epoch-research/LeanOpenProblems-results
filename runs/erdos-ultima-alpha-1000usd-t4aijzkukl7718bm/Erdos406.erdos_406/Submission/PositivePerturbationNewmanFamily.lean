import Submission.NewmanJointFlipRigidity

/-! An unbounded-degree positive-perturbation family that DOES divide binary
polynomials. Its values at three lie strictly between consecutive squares,
so it cannot occur as a factor of an Erdos406 candidate. This separates
Newman divisibility from the essential pure-power evaluation hypothesis. -/
namespace Erdos406PositiveNewman
open Polynomial Erdos406ReciprocalFlip Erdos406Cyclotomic Erdos406FactorParity

noncomputable def Q (m : ℕ) : ℤ[X] := 1+X^(2*m+2)+(X-1)^2*X^m
noncomputable def R (m : ℕ) : ℤ[X] := (X+1)*(X^(m+1)+1)
noncomputable def P (m : ℕ) : ℤ[X] :=
  1+X+X^m+X^(m+3)+X^(2*m+1)+X^(2*m+4)+X^(3*m+3)+X^(3*m+4)

lemma product_identity (m : ℕ) : Q m * R m = P m := by
  unfold Q R P
  simp only [pow_add, pow_mul]
  ring

lemma binary_product (m : ℕ) (hm : 3 ≤ m) : Binary (P m) := by
  intro i
  simp only [P, coeff_add, coeff_one, coeff_X, coeff_X_pow]
  omega

lemma monic_shape (m : ℕ) (hm : 3 ≤ m) : (Q m).IsMonicOfDegree (2*m+2) := by
  have hT : (((X-1 : ℤ[X])^2)*X^m).natDegree ≤ m+2 := by
    have hh := natDegree_mul_le (p := (X-1 : ℤ[X])^2) (q := X^m)
    have hpow := natDegree_pow_le (p := (X-1 : ℤ[X])) (n := 2)
    have hsub : (X-1 : ℤ[X]).natDegree = 1 := by compute_degree!
    rw [hsub] at hpow
    rw [natDegree_X_pow] at hh
    omega
  have hsmall : (1+(X-1 : ℤ[X])^2*X^m).natDegree < 2*m+2 := by
    have hh := natDegree_add_le (1 : ℤ[X]) ((X-1)^2*X^m)
    rw [natDegree_one] at hh
    omega
  have hh := (isMonicOfDegree_X_pow ℤ (2*m+2)).add_right hsmall
  have he : Q m = X^(2*m+2)+(1+(X-1)^2*X^m) := by unfold Q; ring
  rwa [he]

lemma constant_one (m : ℕ) (hm : 3 ≤ m) : (Q m).coeff 0 = 1 := by
  simp [Q, coeff_zero_eq_eval_zero, show m ≠ 0 by omega]

lemma eval_one (m : ℕ) : (Q m).eval 1 = 2 := by simp [Q]

lemma positive_on_ray (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 < ((Q m).map (Int.castRingHom ℝ)).eval x := by
  simp only [Q, Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_mul, Polynomial.map_sub, eval_add,
    Polynomial.eval_one, eval_pow, eval_X, eval_mul, eval_sub]
  have hp := pow_nonneg hx (2*m+2)
  have hs := mul_nonneg (sq_nonneg (x-1)) (pow_nonneg hx m)
  linarith

/-- The low perturbation is too small to reach the next square. -/
lemma eval_three_not_square (m : ℕ) : ¬ IsSquare ((Q m).eval 3) := by
  rintro ⟨y, hy⟩
  have he : y^2 = ((3 : ℤ)^(m+1))^2+4*(3 : ℤ)^m+1 := by
    have hp : (3 : ℤ)^(2*m+2) = ((3 : ℤ)^(m+1))^2 := by
      rw [← pow_mul]
      congr 1
      omega
    simp only [Q, eval_add, Polynomial.eval_one, eval_pow, eval_X, eval_mul, eval_sub] at hy
    rw [hp] at hy
    nlinarith only [hy]
  have h3 : (0 : ℤ) < 3^m := by positivity
  have ha : (0 : ℤ) ≤ 3^(m+1) := by positivity
  have hy0 := abs_nonneg y
  have hlo : (3 : ℤ)^(m+1) < |y| := (sq_lt_sq₀ ha hy0).mp (by
    rw [sq_abs, he]
    omega)
  have hhi : |y| < (3 : ℤ)^(m+1)+1 := (sq_lt_sq₀ hy0 (by positivity)).mp (by
    rw [sq_abs, he]
    have ha3 : (3 : ℤ)^(m+1) = 3^m*3 := pow_succ _ _
    nlinarith only [h3, ha3])
  omega

/-- These are genuine binary-polynomial divisors of unbounded degrees,
not candidates for the original missing-digit problem. -/
theorem newman_family (m : ℕ) (hm : 3 ≤ m) :
    (Q m).Monic ∧ (Q m).natDegree = 2*m+2 ∧ (Q m).coeff 0 = 1 ∧
    (Q m).eval 1 = 2 ∧ Binary (P m) ∧ (P m).coeff 0 = 1 ∧ Q m ∣ P m := by
  have hs := monic_shape m hm
  refine ⟨hs.monic, hs.natDegree_eq, constant_one m hm, eval_one m,
    binary_product m hm, ?_, ⟨R m, (product_identity m).symm⟩⟩
  simp [P, coeff_zero_eq_eval_zero, show m ≠ 0 by omega]

/-- No member can divide an actual power-of-two candidate polynomial. -/
theorem no_candidate_occurrence (m k : ℕ) (hm : 3 ≤ m)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) :
    ¬ Q m ∣ digitPoly (Nat.digits 3 (2^k)) := by
  intro hd
  obtain ⟨_, t, _, ht⟩ := candidate_monic_factor k hg (Q m) (monic_shape m hm).monic hd
  apply eval_three_not_square m
  rw [ht]
  exact (show IsSquare (4 : ℤ) from ⟨2, by norm_num⟩).pow t

#print axioms newman_family
#print axioms no_candidate_occurrence
end Erdos406PositiveNewman
