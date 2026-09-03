import Submission.NewmanReciprocalCubicModTwo

/-! Classification when the residual reduction modulo two is a Frobenius
power of a polynomial of degree at most three. The degree restriction is
explicit and is not proved for arbitrary candidates. -/
namespace Erdos406LowDegreeFrobenius
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406ModTwoCubic Erdos406ModTwoFrobenius
  Erdos406CubicHighBase Erdos406ReciprocalCubicModTwo
  Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma mod_two_degree_three_shapes (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1)
    (hD : R.natDegree ≤ 3) :
    (∃ d : ℕ, R = (X+1)^d) ∨
    (∃ e : ℕ, R = (X+1)^e*(X^2+X+1)) ∨
    R = X^3+X+1 ∨ R = X^3+X^2+1 := by
  have hform := R.as_sum_range_C_mul_X_pow' (by omega : R.natDegree < 4)
  have hb (i : ℕ) : R.coeff i = 0 ∨ R.coeff i = 1 := by
    have hh (x : ZMod 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp
    exact hh _
  rcases hb 1 with h1 | h1 <;> rcases hb 2 with h2 | h2 <;>
    rcases hb 3 with h3 | h3 <;>
    simp [Finset.sum_range_succ,hR,h1,h2,h3] at hform
  · exact Or.inl ⟨0,by simpa using hform⟩
  · right; left
    refine ⟨1,?_⟩
    rw [hform,pow_one]
    have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    calc
      _ = (X+1)*(X^2+X+1)-2*(X+X^2) := by ring
      _ = _ := by rw [hc]; ring
  · left
    refine ⟨2,?_⟩
    rw [hform,mod_two_X_add_one_square]
    ring
  · right; right; right
    rw [hform]
    ring
  · exact Or.inl ⟨1,by rw [hform]; ring⟩
  · right; right; left
    rw [hform]
    ring
  · exact Or.inr (Or.inl ⟨0,by rw [hform]; ring⟩)
  · left
    refine ⟨3,?_⟩
    rw [hform]
    have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    calc
      _ = (X+1)^3-2*(X+X^2) := by ring
      _ = _ := by rw [hc]; ring

/-- In this entire unbounded-degree family the only pure-power-valued
binary polynomials are those representing 1, 4, and 256. -/
theorem binary_low_degree_frobenius_classification (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (hD : R.natDegree ≤ 3) (a t k : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R^(2^t))
    (he : P.eval 3 = (2 : ℤ)^k) :
    P = 1 ∨ P = X+1 ∨ P = 1+X+X^2+X^5 := by
  rcases mod_two_degree_three_shapes R hR hD with ⟨d,hd⟩ | ⟨e,hr⟩ | hr | hr
  · have hm' : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(a+d*2^t) := by
      simpa only [hd,← pow_mul,← pow_add] using hm
    rcases binary_binomial_mod_two_power_classification P hP (a+d*2^t) k hm' he with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hm' : P.map (Int.castRingHom (ZMod 2)) =
        (X+1)^(a+e*2^t)*(X^2+X+1)^(2^t) := by
      simpa only [hr,mul_pow,← pow_mul,← mul_assoc,← pow_add] using hm
    exact (quadratic_two_power_mod_two_exclusion t P hP (a+e*2^t) 1 k
      (by decide) hm' (by simpa using he)).elim
  · rw [hr] at hm
    exact Or.inr (Or.inr (cubic_two_power_mod_two_classification t P hP a 1 k
      (by decide) hm (by simpa using he)).2.2)
  · rw [hr] at hm
    exact (reciprocal_cubic_two_power_mod_two_exclusion t P hP a 1 k
      (by decide) hm (by simpa using he)).elim

/-- Direct classification under the same explicit low residual-degree
hypothesis; arbitrary residual complexity is not covered. -/
theorem candidate_low_degree_frobenius_classification (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1)
    (hD : R.natDegree ≤ 3) (a t : ℕ)
    (hm : (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
      (X+1)^a*R^(2^t)) : n = 1 ∨ n = 4 ∨ n = 256 := by
  obtain ⟨k,rfl⟩ := hn
  have he : (digitPoly (Nat.digits 3 (2^k))).eval 3 = (2 : ℤ)^k := by
    rw [digitPoly_eval_three]
    norm_cast
  have hh := binary_low_degree_frobenius_classification _ (binary_digitPoly _ hg)
    R hR hD a t k hm he
  rcases hh with h | h | h
  · left
    have hv := congrArg (eval (3 : ℤ)) h
    rw [digitPoly_eval_three] at hv
    norm_num at hv
    exact_mod_cast hv
  · right; left
    have hv := congrArg (eval (3 : ℤ)) h
    rw [digitPoly_eval_three] at hv
    norm_num at hv
    exact_mod_cast hv
  · right; right
    have hv := congrArg (eval (3 : ℤ)) h
    rw [digitPoly_eval_three] at hv
    norm_num at hv
    exact_mod_cast hv

/-- Every additional candidate must have residual degree at least four
even after all possible pure Frobenius deflations of the residual. -/
theorem additional_candidate_frobenius_residual_degree (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (h1 : n ≠ 1) (h4 : n ≠ 4) (h256 : n ≠ 256)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a t : ℕ)
    (hm : (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
      (X+1)^a*R^(2^t)) : 4 ≤ R.natDegree := by
  by_contra hD
  have hh := candidate_low_degree_frobenius_classification n hn hg R hR (by omega) a t hm
  exact hh.elim h1 (fun hh => hh.elim h4 h256)

#print axioms binary_low_degree_frobenius_classification
#print axioms candidate_low_degree_frobenius_classification
#print axioms additional_candidate_frobenius_residual_degree
end Erdos406LowDegreeFrobenius
