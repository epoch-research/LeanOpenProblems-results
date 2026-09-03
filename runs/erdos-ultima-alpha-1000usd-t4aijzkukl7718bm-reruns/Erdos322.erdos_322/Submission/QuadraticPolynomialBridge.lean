import FormalConjecturesUtil

/-! Every homogeneous polynomial of degree two evaluates to a quadratic form. -/
namespace Erdos322Research.QuadraticPolynomialBridge

open Finset MvPolynomial QuadraticMap

private lemma degree_two {σ : Type*} (d : σ →₀ ℕ) (hd : d.degree=2) :
    ∃ i j : σ, d=Finsupp.single i 1+Finsupp.single j 1 := by
  classical
  have hc : d.toMultiset.card=2 := by
    simpa only [Finsupp.card_toMultiset, Finsupp.degree_apply] using hd
  obtain ⟨i,j,hij⟩ := Multiset.card_eq_two.mp hc
  refine ⟨i,j,?_⟩
  ext a
  have h := congrArg (fun s : Multiset σ => s.count a) hij
  simpa [Finsupp.single_apply, Multiset.count_cons, Multiset.count_singleton, eq_comm, add_comm] using h

/-- The construction works over any commutative ring, including characteristic
two; it does not use polarization or division by two. -/
theorem exists_quadratic_eval {σ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (hP : P.IsHomogeneous 2) :
    ∃ Q : QuadraticForm R (σ → R), ∀ x, Q x=eval x P := by
  classical
  have hd (d : P.support) : d.val.degree=2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.mp d.property)
  choose i j hij using fun d : P.support => degree_two d.val (hd d)
  let Q : QuadraticForm R (σ → R) := ∑ d : P.support,
    coeff d.val P • linMulLin (LinearMap.proj (i d)) (LinearMap.proj (j d))
  refine ⟨Q, fun x => ?_⟩
  have hm (d : P.support) : monomial d.val (coeff d.val P) =
      C (coeff d.val P)*X (i d)*X (j d) := by
    rw [hij d]
    simp only [X, C_apply, monomial_mul, zero_add, mul_one]
  have he : P=∑ d : P.support, C (coeff d.val P)*X (i d)*X (j d) := by
    simp_rw [← hm]
    exact P.as_sum.trans (Finset.sum_coe_sort P.support
      (fun d => monomial d (coeff d P))).symm
  rw [he]
  simp [Q, QuadraticMap.sum_apply, QuadraticMap.smul_apply, linMulLin_apply, mul_assoc]

end Erdos322Research.QuadraticPolynomialBridge
