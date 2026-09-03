import FormalConjecturesUtil

/-! An exact elliptic-curve reduction for a two-pair quintic construction.
No assertion about the rational rank of this elliptic curve is assumed here. -/
namespace Erdos322Research.QuinticTwoPair

/-- These are the centered coefficient equations obtained by expressing
`u^4 - 5*u^3 + 10*u^2 - 10*u + 5` as the sum of two weighted pairs of fifth
powers of affine forms with opposite slopes. They force an affine rational
point on a fixed elliptic curve. -/
theorem coefficients_force_elliptic_point (p q X Y : ℚ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (h₂ : -q*X+p*Y = (p-q)*(5/4+3*p*q))
    (h₃ : p*q*(Y-X) = (p-q)*(p*q*(p+q)-5/4))
    (h₄ : -q*(X^2+10*X*p^2+5*p^4)+p*(Y^2+10*Y*q^2+5*q^4) =
      (p-q)*(1025/16)) :
    (256*(8*p*q*(p+q)-10))^2 =
      (256*p*q)^3+80*(256*p*q)^2+256000*(256*p*q)+8192000 := by
  have hd : p-q ≠ 0 := sub_ne_zero.mpr hpq
  have hX₀ : (p-q)*(q*X-(-p^2*q+2*p*q^2+5*(q+1)/4)) = 0 := by
    linear_combination q*h₂-h₃
  have hY₀ : (p-q)*(p*Y-(2*p^2*q-p*q^2+5*(p+1)/4)) = 0 := by
    linear_combination p*h₂-h₃
  have hX : X = (-p^2*q+2*p*q^2+5*(q+1)/4)/q := by
    apply (eq_div_iff hq).mpr
    have he := (mul_eq_zero.mp hX₀).resolve_left hd
    linear_combination he
  have hY : Y = (2*p^2*q-p*q^2+5*(p+1)/4)/p := by
    apply (eq_div_iff hp).mpr
    have he := (mul_eq_zero.mp hY₀).resolve_left hd
    linear_combination he
  let E : ℚ := 64*p^2*q^2*(p-q)^2-80*p^2*q^2-160*p*q*(p+q)-1000*p*q-25
  have he : -q*(((-p^2*q+2*p*q^2+5*(q+1)/4)/q)^2+
        10*((-p^2*q+2*p*q^2+5*(q+1)/4)/q)*p^2+5*p^4)+
      p*(((2*p^2*q-p*q^2+5*(p+1)/4)/p)^2+
        10*((2*p^2*q-p*q^2+5*(p+1)/4)/p)*q^2+5*q^4)-
        (p-q)*(1025/16) = (p-q)*E/(16*p*q) := by
    dsimp [E]
    field_simp
    ring
  rw [hX, hY] at h₄
  have hz := sub_eq_zero.mpr h₄
  rw [he] at hz
  have hE : E = 0 := by
    have hn := (div_eq_zero_iff.mp hz).resolve_right
      (mul_ne_zero (mul_ne_zero (by norm_num) hp) hq)
    exact (mul_eq_zero.mp hn).resolve_left hd
  dsimp [E] at hE
  linear_combination 65536*hE

end Erdos322Research.QuinticTwoPair
