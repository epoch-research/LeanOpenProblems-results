import FormalConjecturesUtil

/-! Top homogeneous components and degree reduction for multivariate polynomials. -/
namespace Erdos322Research.HomogeneousTopComponents
noncomputable section
open Polynomial MvPolynomial
set_option Elab.async false
set_option maxHeartbeats 0

variable {R σ : Type*} [CommRing R]

private def ray : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j ↦ Polynomial.C (MvPolynomial.X j) * Polynomial.X)

private lemma ray_monomial (d : σ →₀ ℕ) (a : R) :
    ray (monomial d a) = Polynomial.C (monomial d a) * Polynomial.X ^ d.degree := by
  classical
  simp only [ray, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
    Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  simp [MvPolynomial.monomial_eq]

private lemma ray_coeff (P : MvPolynomial σ R) (n : ℕ) :
    (ray P).coeff n = homogeneousComponent n P := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [homogeneousComponent_apply]
  simp only [map_sum, Polynomial.finset_sum_coeff, ray_monomial,
    Polynomial.coeff_C_mul_X_pow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hn : n = d.degree
  · simp [hn]
  · simp [hn, Ne.symm hn]

private lemma ray_degree (P : MvPolynomial σ R) :
    (ray P).natDegree ≤ P.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [ray_coeff]
  exact homogeneousComponent_eq_zero n P hn

/-- The top possible homogeneous component of a product is the product
of the top possible components of its factors. -/
theorem top_mul (P Q : MvPolynomial σ R) (m n : ℕ)
    (hP : P.totalDegree ≤ m) (hQ : Q.totalDegree ≤ n) :
    homogeneousComponent (m + n) (P * Q) =
      homogeneousComponent m P * homogeneousComponent n Q := by
  rw [← ray_coeff, map_mul, Polynomial.coeff_mul_add_eq_of_natDegree_le
    ((ray_degree P).trans hP) ((ray_degree Q).trans hQ), ray_coeff, ray_coeff]

/-- The top possible component of a power. -/
theorem top_pow (P : MvPolynomial σ R) (m n : ℕ) (hP : P.totalDegree ≤ m) :
    homogeneousComponent (n * m) (P ^ n) = homogeneousComponent m P ^ n := by
  rw [← ray_coeff, map_pow, Polynomial.coeff_pow_of_natDegree_le
    ((ray_degree P).trans hP), ray_coeff]

/-- Removing a top homogeneous component strictly lowers the degree,
provided the proposed degree bound is positive. -/
theorem sub_top_degree_lt (P : MvPolynomial σ R) (D : ℕ) (hD : 0 < D)
    (hP : P.totalDegree ≤ D) :
    (P - homogeneousComponent D P).totalDegree < D := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hD]
  intro d hd
  have hc : coeff d (P - homogeneousComponent D P) ≠ 0 := mem_support_iff.mp hd
  simp only [coeff_sub, coeff_homogeneousComponent] at hc
  have he : d.degree ≠ D := by
    intro he
    simp [he] at hc
  have hp : coeff d P ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hb := le_totalDegree (mem_support_iff.mpr hp)
  change d.degree ≤ P.totalDegree at hb
  change d.degree < D
  omega

end
end Erdos322Research.HomogeneousTopComponents
