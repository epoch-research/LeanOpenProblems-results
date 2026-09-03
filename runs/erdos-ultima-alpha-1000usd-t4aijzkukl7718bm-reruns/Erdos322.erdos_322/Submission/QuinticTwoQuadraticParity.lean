import FormalConjecturesUtil

/-! Classification of two rational quadratics whose fifth-power sum is even. -/
namespace Erdos322Research.QuinticTwoQuadraticParity
set_option maxHeartbeats 0

private theorem equal_up_to_sign {x y : ℚ} {n : ℕ} (hn : n ≠ 0)
    (h : x^n = y^n) : x = y ∨ x = -y := by
  rcases (pow_eq_pow_iff_of_ne_zero hn).mp h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- With both linear coefficients nonzero, an even fifth-power sum of two
quadratics is obtained either by reflection or by exact cancellation. -/
theorem coefficient_classification (a b c d e f : ℚ) (hb : b ≠ 0) (he0 : e ≠ 0)
    (h0 : b*c^4+e*f^4 = 0)
    (h1 : 4*a*b*c^3+2*b^3*c^2+4*d*e*f^3+2*e^3*f^2 = 0)
    (h2 : 30*a^2*b*c^2+20*a*b^3*c+b^5+30*d^2*e*f^2+20*d*e^3*f+e^5 = 0)
    (h4 : b*a^4+e*d^4 = 0) :
    (d=a ∧ e= -b ∧ f=c) ∨ (d= -a ∧ e= -b ∧ f= -c) := by
  by_cases ha : a = 0
  · have hd : d = 0 := by
      rw [ha] at h4
      norm_num at h4
      exact h4.resolve_left he0
    subst a
    subst d
    have he : e = -b := by
      apply (show Odd 5 by decide).pow_injective
      norm_num at h2 ⊢
      linarith
    have hcf : f^4 = c^4 := by
      rw [he] at h0
      have hh : b*(c^4-f^4) = 0 := by linear_combination h0
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hb)).symm
    rcases equal_up_to_sign (by decide : 4 ≠ 0) hcf with hf | hf
    · exact Or.inl ⟨rfl, he, hf⟩
    · exact Or.inr ⟨by norm_num, he, hf⟩
  by_cases hc : c = 0
  · have hf : f = 0 := by
      rw [hc] at h0
      norm_num at h0
      exact h0.resolve_left he0
    subst c
    subst f
    have he : e = -b := by
      apply (show Odd 5 by decide).pow_injective
      norm_num at h2 ⊢
      linarith
    have had : d^4 = a^4 := by
      rw [he] at h4
      have hh : b*(a^4-d^4) = 0 := by linear_combination h4
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hb)).symm
    rcases equal_up_to_sign (by decide : 4 ≠ 0) had with hd | hd
    · exact Or.inl ⟨hd, he, rfl⟩
    · exact Or.inr ⟨hd, he, by norm_num⟩
  have hd0 : d ≠ 0 := by
    intro hz
    rw [hz] at h4
    norm_num at h4
    exact h4.elim hb ha
  let u : ℚ := d/a
  have hu : u ≠ 0 := div_ne_zero hd0 ha
  have hd : d = u*a := by dsimp [u]; field_simp
  have heb : b+e*u^4 = 0 := by
    have hh : a^4*(b+e*u^4) = 0 := by rw [hd] at h4; linear_combination h4
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 4 ha)
  have he : e = -b/u^4 := by
    apply (eq_div_iff (pow_ne_zero 4 hu)).mpr
    linarith
  have hcross : (a*f)^4 = (c*d)^4 := by
    have hh : b*((a*f)^4-(c*d)^4) = 0 := by
      linear_combination f^4*h4-d^4*h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hb)
  rcases equal_up_to_sign (by decide : 4 ≠ 0) hcross with hcross | hcross
  · have hf : f = u*c := by
      apply mul_left_cancel₀ ha
      rw [hd] at hcross
      linear_combination hcross
    rw [hd, he, hf] at h1
    have hclear : u^10*(4*a*b*c^3+2*b^3*c^2+
        4*(u*a)*(-b/u^4)*(u*c)^3+2*(-b/u^4)^3*(u*c)^2) =
        2*b^3*c^2*(u^10-1) := by field_simp; ring
    have hz : (2*b^3*c^2)*(u^10-1) = 0 := by rw [← hclear, h1, mul_zero]
    have hu10 : u^10 = 1 := sub_eq_zero.mp
      ((mul_eq_zero.mp hz).resolve_left (by positivity))
    rcases equal_up_to_sign (by decide : 10 ≠ 0)
      (show u^10 = (1 : ℚ)^10 by simpa using hu10) with hu1 | hu1
    · left
      have hh := And.intro hd (And.intro he hf)
      norm_num [hu1] at hh
      exact hh
    · right
      have hh := And.intro hd (And.intro he hf)
      norm_num [hu1] at hh
      exact hh
  · have hf : f = -u*c := by
      apply mul_left_cancel₀ ha
      rw [hd] at hcross
      linear_combination hcross
    rw [hd, he, hf] at h1 h2
    have hclear1 : u^10*(4*a*b*c^3+2*b^3*c^2+
        4*(u*a)*(-b/u^4)*(-u*c)^3+2*(-b/u^4)^3*(-u*c)^2) =
        (2*b*c^2)*(4*a*c*u^10+b^2*(u^10-1)) := by field_simp; ring
    have hclear2 : u^20*(30*a^2*b*c^2+20*a*b^3*c+b^5+
        30*(u*a)^2*(-b/u^4)*(-u*c)^2+20*(u*a)*(-b/u^4)^3*(-u*c)+(-b/u^4)^5) =
        b^3*(20*a*c*u^10*(u^10+1)+b^2*(u^20-1)) := by field_simp; ring
    have hA : 4*a*c*u^10+b^2*(u^10-1) = 0 := by
      have hh : (2*b*c^2)*(4*a*c*u^10+b^2*(u^10-1)) = 0 := by
        rw [← hclear1, h1, mul_zero]
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hb)
        (pow_ne_zero 2 hc))
    have hB : 20*a*c*u^10*(u^10+1)+b^2*(u^20-1) = 0 := by
      have hh : b^3*(20*a*c*u^10*(u^10+1)+b^2*(u^20-1)) = 0 := by
        rw [← hclear2, h2, mul_zero]
      exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 3 hb)
    have hh : b^2*(u^20-1) = 0 := by linear_combination (5*(u^10+1)*hA-hB)/4
    have hu20 : u^20 = 1 := sub_eq_zero.mp
      ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 hb))
    have hu10 : u^10 = 1 := by
      rcases equal_up_to_sign (by decide : 20 ≠ 0)
        (show u^20 = (1 : ℚ)^20 by simpa using hu20) with hu1 | hu1 <;> norm_num [hu1]
    rw [hu10] at hA
    norm_num at hA
    exact False.elim (hA.elim ha hc)

end Erdos322Research.QuinticTwoQuadraticParity
