import FormalConjecturesUtil

/-!
# Degree of a factorial root

Auxiliary arithmetic for Erdős 68, not a settlement of its irrationality
conjecture. Cancelling just one root does not lower the degree of a rational
polynomial vanishing at that root.
-/

namespace FactorialRootDegree

open Polynomial

lemma exists_prime_factor_once (d : ℕ) (hd : 2 ≤ d) :
    ∃ p : ℕ, p.Prime ∧ p ∣ d.factorial ∧ ¬ p ^ 2 ∣ d.factorial := by
  obtain ⟨p, hp, hpl, hpu⟩ := Nat.exists_prime_lt_and_le_two_mul (d / 2) (by omega)
  have hpd : p ≤ d := by omega
  have hdp : d < 2 * p := by omega
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv : d / p = 1 := Nat.div_eq_of_lt_le (by simpa using hpd) (by simpa using hdp)
  have hv : padicValNat p d.factorial = 1 := by
    rw [← padicValNat_mul_div_factorial, hdiv, padicValNat_factorial_mul]
    simp
  refine ⟨p, hp, hp.dvd_factorial.mpr hpd, ?_⟩
  intro hh
  have := (padicValNat_dvd_iff_le (Nat.factorial_ne_zero d)).mp hh
  omega

lemma factorial_binomial_eisenstein (d : ℕ) (hd : 2 ≤ d) :
    ∃ p : ℕ, p.Prime ∧
      (X ^ d - C (d.factorial : ℤ)).IsEisensteinAt
        (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  obtain ⟨p, hp, hpf, hpf2⟩ := exists_prime_factor_once d hd
  have hm : (X ^ d - C (d.factorial : ℤ)).Monic :=
    monic_X_pow_sub_C _ (by omega)
  refine ⟨p, hp, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
    exact_mod_cast hp.not_dvd_one
  · intro n hn
    rw [natDegree_X_pow_sub_C] at hn
    rw [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, coeff_C]
    by_cases hn0 : n = 0
    · subst n
      simp only [show ¬ (0 : ℕ) = d by omega, ↓reduceIte, zero_sub]
      exact dvd_neg.mpr (show (p : ℤ) ∣ (d.factorial : ℤ) by exact_mod_cast hpf)
    · simp [hn0, show n ≠ d by omega]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      coeff_sub, coeff_X_pow, coeff_C]
    simp only [show ¬ (0 : ℕ) = d by omega, ↓reduceIte, zero_sub, dvd_neg]
    exact_mod_cast hpf2

lemma factorial_binomial_irreducible_int (d : ℕ) (hd : 2 ≤ d) :
    Irreducible (X ^ d - C (d.factorial : ℤ)) := by
  obtain ⟨p, hp, he⟩ := factorial_binomial_eisenstein d hd
  have hm : (X ^ d - C (d.factorial : ℤ)).Monic :=
    monic_X_pow_sub_C _ (by omega)
  have hi : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := by
    apply (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    exact Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  exact he.irreducible hi hm.isPrimitive (by rw [natDegree_X_pow_sub_C]; omega)

lemma factorial_binomial_irreducible_rat (d : ℕ) (hd : 2 ≤ d) :
    Irreducible (X ^ d - C (d.factorial : ℚ)) := by
  have hm : (X ^ d - C (d.factorial : ℤ)).Monic :=
    monic_X_pow_sub_C _ (by omega)
  have h := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    hm.isPrimitive).mp (factorial_binomial_irreducible_int d hd)
  simpa using h

lemma minpoly_factorial_root {d : ℕ} (hd : 2 ≤ d) {x : ℝ}
    (hx : x ^ d = d.factorial) :
    minpoly ℚ x = X ^ d - C (d.factorial : ℚ) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
    (factorial_binomial_irreducible_rat d hd)
  · simp [hx]
  · exact monic_X_pow_sub_C _ (by omega)

/-- Any nonzero rational polynomial vanishing at a d-th root of d! has degree
at least d. This does not assert a nonvanishing result for the original sum. -/
theorem degree_ge_of_factorial_root {d : ℕ} (hd : 2 ≤ d) {x : ℝ}
    (hx : x ^ d = d.factorial) {P : ℚ[X]} (hP : P ≠ 0) (hPx : aeval x P = 0) :
    d ≤ P.natDegree := by
  have hdiv : minpoly ℚ x ∣ P := minpoly.dvd ℚ x hPx
  rw [minpoly_factorial_root hd hx] at hdiv
  simpa only [natDegree_X_pow_sub_C] using Polynomial.natDegree_le_of_dvd hdiv hP


lemma factorial_root_ne_zero {d : ℕ} (hd : 2 ≤ d) {x : ℝ}
    (hx : x ^ d = d.factorial) : x ≠ 0 := by
  intro hx0
  rw [hx0, zero_pow (by omega)] at hx
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)) hx.symm

lemma reverse_vanishes_of_inv_root {x : ℝ} (hx : x ≠ 0) {P : ℚ[X]}
    (hP : aeval x⁻¹ P = 0) : aeval x P.reverse = 0 := by
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := (eval₂_reverse_eq_zero_iff (algebraMap ℚ ℝ) x⁻¹ P).mpr
    (by simpa only [← aeval_def] using hP)
  simpa only [invOf_eq_inv, inv_inv, ← aeval_def] using h

/-- Taking the inverse of a factorial root does not decrease its rational
annihilation degree. -/
theorem degree_ge_of_inv_factorial_root {d : ℕ} (hd : 2 ≤ d) {x : ℝ}
    (hx : x ^ d = d.factorial) {P : ℚ[X]} (hP : P ≠ 0)
    (hPx : aeval x⁻¹ P = 0) : d ≤ P.natDegree := by
  have hrev : P.reverse ≠ 0 := fun h => hP (reverse_eq_zero.mp h)
  exact (degree_ge_of_factorial_root hd hx hrev
    (reverse_vanishes_of_inv_root (factorial_root_ne_zero hd hx) hPx)).trans
    P.reverse_natDegree_le

lemma factorial_binomials_coprime {d e : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e)
    (hne : d ≠ e) :
    IsCoprime (X ^ d - C (d.factorial : ℚ)) (X ^ e - C (e.factorial : ℚ)) := by
  have hi := factorial_binomial_irreducible_rat d hd
  have hj := factorial_binomial_irreducible_rat e he
  apply hi.coprime_iff_not_dvd.mpr
  intro hdiv
  rcases hj.dvd_iff.mp hdiv with hu | ha
  · exact hi.not_isUnit hu
  · have hde := Polynomial.natDegree_le_of_dvd hdiv hj.ne_zero
    have hed := Polynomial.natDegree_le_of_dvd ha.dvd hi.ne_zero
    simp only [natDegree_X_pow_sub_C] at hde hed
    exact hne (Nat.le_antisymm hde hed)

/-- Distinct factorial-root degrees impose additive costs on every nonzero
rational polynomial vanishing at all the selected roots. -/
theorem degree_ge_sum_of_factorial_roots (s : Finset ℕ) (x : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hx : ∀ d ∈ s, x d ^ d = d.factorial)
    {P : ℚ[X]} (hP : P ≠ 0) (hPx : ∀ d ∈ s, aeval (x d) P = 0) :
    ∑ d ∈ s, d ≤ P.natDegree := by
  let f : ℕ → ℚ[X] := fun d => X ^ d - C (d.factorial : ℚ)
  have hcop : (↑s : Set ℕ).Pairwise (Function.onFun IsCoprime f) := by
    intro d hd e he hne
    exact factorial_binomials_coprime (hs d hd) (hs e he) hne
  have hdiv (d : ℕ) (hd : d ∈ s) : f d ∣ P := by
    have h := minpoly.dvd ℚ (x d) (hPx d hd)
    rwa [minpoly_factorial_root (hs d hd) (hx d hd)] at h
  have hdeg := Polynomial.natDegree_le_of_dvd
    (Finset.prod_dvd_of_coprime hcop hdiv) hP
  rw [natDegree_prod_of_monic s f (fun d hd =>
    monic_X_pow_sub_C _ (by have := hs d hd; omega))] at hdeg
  simpa only [f, natDegree_X_pow_sub_C] using hdeg

/-- In particular, selecting only one real inverse root from each row still
requires the sum of the row periods in rational polynomial degree. -/
theorem degree_ge_sum_of_inv_factorial_roots (s : Finset ℕ) (x : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hx : ∀ d ∈ s, x d ^ d = d.factorial)
    {P : ℚ[X]} (hP : P ≠ 0) (hPx : ∀ d ∈ s, aeval (x d)⁻¹ P = 0) :
    ∑ d ∈ s, d ≤ P.natDegree := by
  have hrev : P.reverse ≠ 0 := fun h => hP (reverse_eq_zero.mp h)
  exact (degree_ge_sum_of_factorial_roots s x hs hx hrev
    (fun d hd => reverse_vanishes_of_inv_root
      (factorial_root_ne_zero (hs d hd) (hx d hd)) (hPx d hd))).trans
    P.reverse_natDegree_le

end FactorialRootDegree

#print axioms FactorialRootDegree.factorial_binomial_irreducible_rat
#print axioms FactorialRootDegree.degree_ge_of_factorial_root

#print axioms FactorialRootDegree.degree_ge_of_inv_factorial_root
#print axioms FactorialRootDegree.degree_ge_sum_of_factorial_roots
#print axioms FactorialRootDegree.degree_ge_sum_of_inv_factorial_roots
