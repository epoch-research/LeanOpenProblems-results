import FormalConjecturesUtil

/-!
An algebraic distinction between the balanced-pair section and the additive-triple
section of the quartic form. No representation-count bound is asserted here.
-/
namespace Erdos322Research.QuarticBalancedSection

/-- Four elements of a characteristic-zero field cannot have equal nonzero cubes
and sum zero. -/
theorem four_equal_cubes_sum_zero {K : Type*} [Field K] [CharZero K]
    (a b c d : K) (ha : a^3=d^3) (hb : b^3=d^3) (hc : c^3=d^3)
    (hs : a+b+c+d=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  have hd : d=0 := by
    by_contra hd
    have ha0 : a ≠ 0 := by
      intro h
      exact (pow_ne_zero 3 hd) (by simpa [h] using ha.symm)
    have hb0 : b ≠ 0 := by
      intro h
      exact (pow_ne_zero 3 hd) (by simpa [h] using hb.symm)
    have hc0 : c ≠ 0 := by
      intro h
      exact (pow_ne_zero 3 hd) (by simpa [h] using hc.symm)
    have hsum : d=-(a+b+c) := by linear_combination hs
    have h5 : 6*(a^5+b^5+c^5+d^5) =
        5*(a^2+b^2+c^2+d^2)*(a^3+b^3+c^3+d^3) := by
      rw [hsum]
      ring
    have ha5 : a^5=a^2*d^3 := by rw [show a^5=a^2*a^3 by ring, ha]
    have hb5 : b^5=b^2*d^3 := by rw [show b^5=b^2*b^3 by ring, hb]
    have hc5 : c^5=c^2*d^3 := by rw [show c^5=c^2*c^3 by ring, hc]
    rw [ha5, hb5, hc5, ha, hb, hc] at h5
    have hm : d^3*(a^2+b^2+c^2+d^2)=0 := by
      linear_combination (-1/14 : K)*h5
    have h2 : a^2+b^2+c^2+d^2=0 :=
      (mul_eq_zero.mp hm).resolve_left (pow_ne_zero 3 hd)
    have h4 : a^4+b^4+c^4+d^4=0 := by
      calc
        a^4+b^4+c^4+d^4 = d^3*(a+b+c+d) := by
          linear_combination a*ha+b*hb+c*hc
        _ = 0 := by rw [hs, mul_zero]
    have hid : 2*(a^4+b^4+c^4+d^4) =
        (a^2+b^2+c^2+d^2)^2-8*a*b*c*d := by
      rw [hsum]
      ring
    rw [h4, h2] at hid
    have hp : a*b*c*d=0 := by linear_combination (1/8 : K)*hid
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0) hd) hp
  have ha0 : a=0 := by apply eq_zero_of_pow_eq_zero (n := 3); simpa [hd] using ha
  have hb0 : b=0 := by apply eq_zero_of_pow_eq_zero (n := 3); simpa [hd] using hb
  have hc0 : c=0 := by apply eq_zero_of_pow_eq_zero (n := 3); simpa [hd] using hc
  exact ⟨ha0,hb0,hc0,hd⟩

/-- The normalized partial derivatives of
`a^4+b^4+c^4+(a+b-c)^4` vanish together only at the origin.
This holds over any characteristic-zero field, including `ℂ`. -/
theorem balanced_section_gradient_zero {K : Type*} [Field K] [CharZero K]
    (a b c : K)
    (ha : a^3+(a+b-c)^3=0)
    (hb : b^3+(a+b-c)^3=0)
    (hc : c^3-(a+b-c)^3=0) : a=0 ∧ b=0 ∧ c=0 := by
  have h := four_equal_cubes_sum_zero (-a) (-b) c (a+b-c)
    (by linear_combination -ha) (by linear_combination -hb)
    (sub_eq_zero.mp hc) (by ring)
  exact ⟨neg_eq_zero.mp h.1, neg_eq_zero.mp h.2.1, h.2.2.1⟩

end Erdos322Research.QuarticBalancedSection
