import FormalConjecturesUtil

/-!
An auxiliary obstruction: four distinct projective squares in a two-dimensional
pencil of polynomial squares cannot vary nontrivially in characteristic zero.
This is not a proof or disproof of the density conjecture.
-/

namespace Erdos1206.PolynomialSquarePencil
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private lemma unitC {u : K} (hu : u ≠ 0) : IsUnit (C u : K[X]) :=
  isUnit_C.mpr hu.isUnit

omit [CharZero K] in
private lemma rotate_coprime {f g h : K[X]} {a b c : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hfg : IsCoprime f g)
    (he : C a*f^2+C b*g^2+C c*h^2=0) : IsCoprime g h := by
  rw [← IsCoprime.pow_iff (by decide : 0 < 2) (by decide : 0 < 2),
    ← isCoprime_mul_units_left (unitC ha) (unitC hb)] at hfg
  rw [add_eq_zero_iff_neg_eq] at he
  rw [← IsCoprime.pow_iff (by decide : 0 < 2) (by decide : 0 < 2),
    ← isCoprime_mul_units_left (unitC hb) (unitC hc),
    ← he, IsCoprime.neg_right_iff]
  convert hfg.symm.add_mul_left_right 1 using 2
  rw [mul_one]

omit [CharZero K] in
private lemma coprime_of_square_sum {f g h : K[X]} {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hfg : IsCoprime f g)
    (he : h^2=C a*f^2+C b*g^2) :
    IsCoprime f h ∧ IsCoprime g h := by
  have hz : C a*f^2+C b*g^2+C (-1:K)*h^2=0 := by
    rw [← he]
    simp
  constructor
  · apply rotate_coprime hb ha (neg_ne_zero.mpr one_ne_zero) hfg.symm
    linear_combination hz
  · exact rotate_coprime ha hb (neg_ne_zero.mpr one_ne_zero) hfg hz

/-- A third square in the pencil divides the Wronskian of the first two. -/
private lemma dvd_wronskian_of_square_sum {f g h : K[X]} {a b : K}
    (hb : b ≠ 0) (hhg : IsCoprime h g)
    (he : h^2=C a*f^2+C b*g^2) : h ∣ wronskian f g := by
  have hd := congrArg derivative he
  simp only [derivative_pow, derivative_add, derivative_C_mul,
    Nat.reduceSub, pow_one, map_natCast] at hd
  have hw : h * wronskian f h = C b*g*wronskian f g := by
    apply mul_left_cancel₀ (by norm_num : (2 : K[X]) ≠ 0)
    dsimp [wronskian]
    linear_combination f*hd - 2*(derivative f)*he
  have hh : h ∣ C b*g*wronskian f g := by
    rw [← hw]
    exact dvd_mul_right _ _
  have hcop : IsCoprime h (C b*g) :=
    (isCoprime_mul_unit_left_right (unitC hb) _ _).mpr hhg
  exact hcop.dvd_of_dvd_mul_left hh

private lemma derivative_square_sum_zero {f g h : K[X]} {a b : K}
    (hh : h ≠ 0) (hf : derivative f=0) (hg : derivative g=0)
    (he : h^2=C a*f^2+C b*g^2) : derivative h=0 := by
  have hd := congrArg derivative he
  simp only [derivative_pow, derivative_add, derivative_C_mul,
    Nat.reduceSub, pow_one, hf, hg, mul_zero, add_zero] at hd
  exact (mul_eq_zero.mp hd).resolve_left
    (mul_ne_zero (by norm_num) hh)

/-- The coprime, nondegenerate four-square pencil has only constant solutions.
The result holds for polynomials of arbitrary degree, not only quadratics. -/
theorem four_square_pencil_constant
    {f g h j : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0) (hj : j ≠ 0)
    (hfg : IsCoprime f g) {a b c d : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hdet : a*d-b*c ≠ 0)
    (heh : h^2=C a*f^2+C b*g^2)
    (hej : j^2=C c*f^2+C d*g^2) :
    f.natDegree=0 ∧ g.natDegree=0 ∧ h.natDegree=0 ∧ j.natDegree=0 := by
  let Δ := a*d-b*c
  have hΔ : Δ ≠ 0 := hdet
  have hf' : f^2=C (d/Δ)*h^2+C (-b/Δ)*j^2 := by
    have he : C Δ*f^2=C d*h^2-C b*j^2 := by
      dsimp [Δ]
      simp only [map_sub, map_mul]
      linear_combination -C d*heh + C b*hej
    calc
      f^2 = C (Δ⁻¹)*(C Δ*f^2) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hΔ, map_one, one_mul]
      _ = C (d/Δ)*h^2+C (-b/Δ)*j^2 := by
        rw [he]
        simp only [div_eq_mul_inv, map_mul, map_neg]
        ring
  have hg' : g^2=C (-c/Δ)*h^2+C (a/Δ)*j^2 := by
    have he : C Δ*g^2= -C c*h^2+C a*j^2 := by
      dsimp [Δ]
      simp only [map_sub, map_mul]
      linear_combination C c*heh - C a*hej
    calc
      g^2 = C (Δ⁻¹)*(C Δ*g^2) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hΔ, map_one, one_mul]
      _ = C (-c/Δ)*h^2+C (a/Δ)*j^2 := by
        rw [he]
        simp only [div_eq_mul_inv, map_mul, map_neg]
        ring
  obtain ⟨hfh, hgh⟩ := coprime_of_square_sum ha hb hfg heh
  obtain ⟨hfj, hgj⟩ := coprime_of_square_sum hc hd hfg hej
  have hhj : IsCoprime h j := by
    have he : C Δ*g^2+C c*h^2+C (-a)*j^2=0 := by
      dsimp [Δ]
      simp only [map_sub, map_mul, map_neg]
      linear_combination C c*heh-C a*hej
    exact rotate_coprime hΔ hc (neg_ne_zero.mpr ha) hgh he
  by_cases hw : wronskian f g=0
  · obtain ⟨hdf,hdg⟩ := hfg.wronskian_eq_zero_iff.mp hw
    exact ⟨natDegree_eq_zero_of_derivative_eq_zero hdf,
      natDegree_eq_zero_of_derivative_eq_zero hdg,
      natDegree_eq_zero_of_derivative_eq_zero
        (derivative_square_sum_zero hh hdf hdg heh),
      natDegree_eq_zero_of_derivative_eq_zero
        (derivative_square_sum_zero hj hdf hdg hej)⟩
  by_cases hw' : wronskian h j=0
  · obtain ⟨hdh,hdj⟩ := hhj.wronskian_eq_zero_iff.mp hw'
    exact ⟨natDegree_eq_zero_of_derivative_eq_zero
        (derivative_square_sum_zero hf hdh hdj hf'),
      natDegree_eq_zero_of_derivative_eq_zero
        (derivative_square_sum_zero hg hdh hdj hg'),
      natDegree_eq_zero_of_derivative_eq_zero hdh,
      natDegree_eq_zero_of_derivative_eq_zero hdj⟩
  have hdiv : h*j ∣ wronskian f g := hhj.mul_dvd
    (dvd_wronskian_of_square_sum hb hgh.symm heh)
    (dvd_wronskian_of_square_sum hd hgj.symm hej)
  have hdiv' : f*g ∣ wronskian h j := hfg.mul_dvd
    (dvd_wronskian_of_square_sum (div_ne_zero (neg_ne_zero.mpr hb) hΔ) hfj hf')
    (dvd_wronskian_of_square_sum (div_ne_zero ha hΔ) hgj hg')
  have h₁ := (natDegree_le_of_dvd hdiv hw).trans_lt (natDegree_wronskian_lt_add hw)
  have h₂ := (natDegree_le_of_dvd hdiv' hw').trans_lt (natDegree_wronskian_lt_add hw')
  rw [natDegree_mul hh hj] at h₁
  rw [natDegree_mul hf hg] at h₂
  omega

/-- Without the coprimality normalization, every solution is a common
polynomial factor times four constants. -/
theorem four_square_pencil_common_factor
    {f g h j : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0) (hj : j ≠ 0)
    {a b c d : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hdet : a*d-b*c ≠ 0)
    (heh : h^2=C a*f^2+C b*g^2)
    (hej : j^2=C c*f^2+C d*g^2) :
    ∃ q : K[X], ∃ u v w z : K, q ≠ 0 ∧
      f=C u*q ∧ g=C v*q ∧ h=C w*q ∧ j=C z*q := by
  classical
  let q := gcd f g
  have hq : q ≠ 0 := gcd_ne_zero_of_left hf
  obtain ⟨f', ef⟩ := gcd_dvd_left f g
  obtain ⟨g', eg⟩ := gcd_dvd_right f g
  change f=q*f' at ef
  change g=q*g' at eg
  have qh : q ∣ h := by
    apply (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    rw [heh, ef, eg]
    refine ⟨C a*f'^2+C b*g'^2, ?_⟩
    ring
  have qj : q ∣ j := by
    apply (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    rw [hej, ef, eg]
    refine ⟨C c*f'^2+C d*g'^2, ?_⟩
    ring
  obtain ⟨h', eh⟩ := qh
  obtain ⟨j', ej⟩ := qj
  have hf' : f' ≠ 0 := by intro hz; simp [hz] at ef; exact hf ef
  have hg' : g' ≠ 0 := by intro hz; simp [hz] at eg; exact hg eg
  have hh' : h' ≠ 0 := by intro hz; simp [hz] at eh; exact hh eh
  have hj' : j' ≠ 0 := by intro hz; simp [hz] at ej; exact hj ej
  have hcop : IsCoprime f' g' := by
    have ef' : f'=f/q := EuclideanDomain.eq_div_of_mul_eq_left hq (by rw [ef]; ring)
    have eg' : g'=g/q := EuclideanDomain.eq_div_of_mul_eq_left hq (by rw [eg]; ring)
    rw [ef', eg']
    exact isCoprime_div_gcd_div_gcd hg
  have heh' : h'^2=C a*f'^2+C b*g'^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hq)
    rw [ef, eg, eh] at heh
    linear_combination heh
  have hej' : j'^2=C c*f'^2+C d*g'^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hq)
    rw [ef, eg, ej] at hej
    linear_combination hej
  obtain ⟨hdf,hdg,hdh,hdj⟩ :=
    four_square_pencil_constant hf' hg' hh' hj' hcop ha hb hc hd hdet heh' hej'
  refine ⟨q, f'.coeff 0, g'.coeff 0, h'.coeff 0, j'.coeff 0, hq, ?_, ?_, ?_, ?_⟩
  · rw [ef, eq_C_of_natDegree_eq_zero hdf, mul_comm]; simp
  · rw [eg, eq_C_of_natDegree_eq_zero hdg, mul_comm]; simp
  · rw [eh, eq_C_of_natDegree_eq_zero hdh, mul_comm]; simp
  · rw [ej, eq_C_of_natDegree_eq_zero hdj, mul_comm]; simp

#print axioms four_square_pencil_common_factor

#print axioms four_square_pencil_constant

end Erdos1206.PolynomialSquarePencil
