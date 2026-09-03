import Submission.PolynomialSquarePencil

/-!
Three polynomial representations of a cube sum with distinct proportional
pair sums must be a common dilation of a constant configuration. This is an
auxiliary result, not a settlement of the density conjecture.
-/

namespace Erdos1206.PolynomialTriplePairSums
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

private lemma difference_square {A B D E : K[X]} {r : K}
    (hr : r ≠ 0) (hL : A+B ≠ 0)
    (hs : D+E=C r*(A+B)) (he : D^3+E^3=A^3+B^3) :
    (D-E)^2=C ((1-r^3)/(3*r))*(A+B)^2+C (1/r)*(A-B)^2 := by
  have hh : (A+B)*((C r)^3*(A+B)^2+3*C r*(D-E)^2)=
      (A+B)*((A+B)^2+3*(A-B)^2) := by
    calc
      _ = (D+E)^3+3*(D+E)*(D-E)^2 := by rw [hs]; ring
      _ = 4*(D^3+E^3) := by ring
      _ = 4*(A^3+B^3) := by rw [he]
      _ = _ := by ring
  have hh' := mul_left_cancel₀ hL hh
  have hc : C (3*r)*(D-E)^2=C (1-r^3)*(A+B)^2+3*(A-B)^2 := by
    simp only [map_mul, map_ofNat, map_sub, map_one, map_pow]
    linear_combination hh'
  have h3r : (3:K)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h₁ : (3*r)*((1-r^3)/(3*r))=1-r^3 := by field_simp
  have h₂ : (3*r)*(1/r)=(3:K) := by field_simp
  apply mul_left_cancel₀ (C_ne_zero.mpr h3r)
  rw [hc]
  symm
  calc
    _ = C ((3*r)*((1-r^3)/(3*r)))*(A+B)^2+
        C ((3*r)*(1/r))*(A-B)^2 := by simp only [map_mul]; ring
    _ = _ := by rw [h₁,h₂]; simp only [map_ofNat]

private lemma half_C (x : K) : (2:K[X])*C (x/2)=C x := by
  have hh : (2:K)*(x/2)=x := by field_simp
  calc
    _ = C ((2:K)*(x/2)) := by rw [map_mul]; simp only [map_ofNat]
    _ = _ := by rw [hh]

private lemma pair_of_sum_difference {A B q : K[X]} {u v : K}
    (hs : A+B=C u*q) (hd : A-B=C v*q) :
    A=C ((u+v)/2)*q ∧ B=C ((u-v)/2)*q := by
  constructor
  · apply mul_left_cancel₀ (by norm_num : (2:K[X]) ≠ 0)
    calc
      2*A = (A+B)+(A-B) := by ring
      _ = C (u+v)*q := by rw [hs,hd,map_add]; ring
      _ = 2*(C ((u+v)/2)*q) := by rw [← mul_assoc,half_C]
  · apply mul_left_cancel₀ (by norm_num : (2:K[X]) ≠ 0)
    calc
      2*B = (A+B)-(A-B) := by ring
      _ = C (u-v)*q := by rw [hs,hd,map_sub]; ring
      _ = 2*(C ((u-v)/2)*q) := by rw [← mul_assoc,half_C]

/-- The three proportional pair sums cannot vary in a genuinely
nonconstant projective family. No bound on polynomial degree is needed.
The nonzero differences exclude equal coordinates within a pair. -/
theorem proportional_pair_sums_common_factor
    {A B D E F G : K[X]} {r s : K}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hr₃ : r^3 ≠ 1) (hs₃ : s^3 ≠ 1) (hrs₃ : r^3 ≠ s^3)
    (hL : A+B ≠ 0) (hX : A-B ≠ 0) (hY : D-E ≠ 0) (hZ : F-G ≠ 0)
    (hS₁ : D+E=C r*(A+B)) (hS₂ : F+G=C s*(A+B))
    (hC₁ : D^3+E^3=A^3+B^3) (hC₂ : F^3+G^3=A^3+B^3) :
    ∃ q : K[X], ∃ a b d e f g : K, q ≠ 0 ∧
      A=C a*q ∧ B=C b*q ∧ D=C d*q ∧ E=C e*q ∧ F=C f*q ∧ G=C g*q := by
  have h₁ := difference_square hr hL hS₁ hC₁
  have h₂ := difference_square hs hL hS₂ hC₂
  have ha : (1-r^3)/(3*r) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hr₃.symm) (mul_ne_zero (by norm_num) hr)
  have hb : (1:K)/r ≠ 0 := div_ne_zero one_ne_zero hr
  have hc : (1-s^3)/(3*s) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hs₃.symm) (mul_ne_zero (by norm_num) hs)
  have hd : (1:K)/s ≠ 0 := div_ne_zero one_ne_zero hs
  have hdet : ((1-r^3)/(3*r))*(1/s)-(1/r)*((1-s^3)/(3*s)) ≠ 0 := by
    have he : ((1-r^3)/(3*r))*(1/s)-(1/r)*((1-s^3)/(3*s))=
        (s^3-r^3)/(3*r*s) := by field_simp; ring
    rw [he]
    exact div_ne_zero (sub_ne_zero.mpr hrs₃.symm)
      (mul_ne_zero (mul_ne_zero (by norm_num) hr) hs)
  obtain ⟨q,u,v,w,z,hq,hLu,hXv,hYw,hZz⟩ :=
    PolynomialSquarePencil.four_square_pencil_common_factor
      hL hX hY hZ ha hb hc hd hdet h₁ h₂
  have hDu : D+E=C (r*u)*q := by rw [hS₁,hLu,map_mul]; ring
  have hFu : F+G=C (s*u)*q := by rw [hS₂,hLu,map_mul]; ring
  obtain ⟨hA,hB⟩ := pair_of_sum_difference hLu hXv
  obtain ⟨hD,hE⟩ := pair_of_sum_difference hDu hYw
  obtain ⟨hF,hG⟩ := pair_of_sum_difference hFu hZz
  exact ⟨q,(u+v)/2,(u-v)/2,(r*u+w)/2,(r*u-w)/2,(s*u+z)/2,(s*u-z)/2,
    hq,hA,hB,hD,hE,hF,hG⟩

#print axioms proportional_pair_sums_common_factor
end Erdos1206.PolynomialTriplePairSums
