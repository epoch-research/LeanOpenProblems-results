import FormalConjecturesUtil

/-!
Every nonzero polynomial solution f^3+g^3=S*q^3, for a nonzero constant S,
has f and g proportional to q. The proof uses polynomial Fermat-Catalan
after taking out the gcd, not a theorem about integer point counts.
-/
namespace Erdos1206.WeightedPolynomialCubes
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- A polynomial parametrization of a fixed nonzero weighted Fermat cubic
is projectively constant. -/
theorem proportional_to_common_cube {f g q : K[X]} {S : K}
    (hf : f ≠ 0) (hg : g ≠ 0) (hq : q ≠ 0) (hS : S ≠ 0)
    (he : f^3+g^3=C S*q^3) :
    ∃ u v : K, f=C u*q ∧ g=C v*q := by
  classical
  let d := gcd f g
  have hd : d ≠ 0 := gcd_ne_zero_of_left hf
  obtain ⟨f',ef⟩ := gcd_dvd_left f g
  obtain ⟨g',eg⟩ := gcd_dvd_right f g
  change f=d*f' at ef
  change g=d*g' at eg
  have hdq : d ∣ q := by
    apply (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : 3 ≠ 0)).mp
    apply (isUnit_C.mpr hS.isUnit).dvd_mul_left.mp
    rw [← he,ef,eg]
    exact ⟨f'^3+g'^3,by ring⟩
  obtain ⟨q',eq⟩ := hdq
  have hf' : f' ≠ 0 := by intro hz; rw [hz,mul_zero] at ef; exact hf ef
  have hg' : g' ≠ 0 := by intro hz; rw [hz,mul_zero] at eg; exact hg eg
  have hq' : q' ≠ 0 := by intro hz; rw [hz,mul_zero] at eq; exact hq eq
  have hcop : IsCoprime f' g' := by
    have ef' : f'=f/d := EuclideanDomain.eq_div_of_mul_eq_left hd (by rw [ef]; ring)
    have eg' : g'=g/d := EuclideanDomain.eq_div_of_mul_eq_left hd (by rw [eg]; ring)
    rw [ef',eg']
    exact isCoprime_div_gcd_div_gcd hg
  have he' : C (1:K)*f'^3+C (1:K)*g'^3+C (-S)*q'^3=0 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hd)
    rw [ef,eg,eq] at he
    simp only [map_one,map_neg]
    linear_combination he
  obtain ⟨hdf,hdg,hdq⟩ := Polynomial.flt_catalan
    (by decide : 3 ≠ 0) (by decide : 3 ≠ 0) (by decide : 3 ≠ 0) (by decide)
    (by norm_num : (3:K) ≠ 0) (by norm_num : (3:K) ≠ 0) (by norm_num : (3:K) ≠ 0)
    hf' hg' hq' hcop one_ne_zero one_ne_zero (neg_ne_zero.mpr hS) he'
  have hfC := eq_C_of_natDegree_eq_zero hdf
  have hgC := eq_C_of_natDegree_eq_zero hdg
  have hqC := eq_C_of_natDegree_eq_zero hdq
  have hz : q'.coeff 0 ≠ 0 := by
    intro hz
    exact hq' (by rw [hqC,hz,map_zero])
  have hconst (r : K) : C (r/q'.coeff 0)*C (q'.coeff 0)=C r := by
    rw [← map_mul,div_mul_cancel₀ r hz]
  refine ⟨f'.coeff 0/q'.coeff 0,g'.coeff 0/q'.coeff 0,?_,?_⟩
  · rw [ef,eq,hfC,hqC]
    simp only [coeff_C,ite_true]
    calc
      _ = C (f'.coeff 0)*d := mul_comm _ _
      _ = C (f'.coeff 0/q'.coeff 0)*C (q'.coeff 0)*d := by rw [hconst]
      _ = _ := by ring
  · rw [eg,eq,hgC,hqC]
    simp only [coeff_C,ite_true]
    calc
      _ = C (g'.coeff 0)*d := mul_comm _ _
      _ = C (g'.coeff 0/q'.coeff 0)*C (q'.coeff 0)*d := by rw [hconst]
      _ = _ := by ring

#print axioms proportional_to_common_cube
end Erdos1206.WeightedPolynomialCubes
