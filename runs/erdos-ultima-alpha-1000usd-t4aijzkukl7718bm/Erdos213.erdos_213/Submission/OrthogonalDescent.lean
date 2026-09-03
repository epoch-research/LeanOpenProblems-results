import FormalConjecturesUtil

/-!
A checked local obstruction in the 2-isogeny descent for the orthogonal-grid
specialization. This file does not claim the full rational-point classification
of either elliptic curve and does not settle Erdős 213.
-/

namespace Erdos213.OrthogonalDescent

private lemma quartic_mod_nine : ∀ a b c : ZMod 9,
    c^2 = 3*a^4-10*a^2*b^2+3*b^4 → a.val % 3 = 0 ∧ b.val % 3 = 0 := by
  decide

lemma quartic_three_dvd {a b c : ℤ}
    (h : c^2 = 3*a^4-10*a^2*b^2+3*b^4) : 3 ∣ a ∧ 3 ∣ b := by
  have hm : (c : ZMod 9)^2 =
      3*(a : ZMod 9)^4-10*(a : ZMod 9)^2*(b : ZMod 9)^2+3*(b : ZMod 9)^4 := by
    have hc := congrArg (fun z : ℤ => (z : ZMod 9)) h
    push_cast at hc
    exact hc
  have hh := quartic_mod_nine _ _ _ hm
  have ha : (((a : ZMod 9).val : ℤ) % 3) = 0 := by exact_mod_cast hh.1
  have hb : (((b : ZMod 9).val : ℤ) % 3) = 0 := by exact_mod_cast hh.2
  rw [ZMod.val_intCast] at ha hb
  norm_num only [Nat.cast_ofNat] at ha hb
  rw [Int.emod_emod_of_dvd _ (by norm_num : (3 : ℤ) ∣ 9)] at ha hb
  exact ⟨Int.dvd_of_emod_eq_zero ha, Int.dvd_of_emod_eq_zero hb⟩

/-- The nontrivial positive square class in this 2-isogeny descent has no
rational point. A separate global argument is needed to deduce rank zero. -/
lemma quartic_not_square (u : ℚ) : ¬ IsSquare (3*u^4-10*u^2+3) := by
  rintro ⟨v,hv⟩
  have hd : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_ne_zero
  have hn : (u.num : ℚ) = u*(u.den : ℚ) := by
    calc
      (u.num : ℚ) = ((u.num : ℚ)/(u.den : ℚ))*(u.den : ℚ) := by field_simp
      _ = u*(u.den : ℚ) := by rw [Rat.num_div_den]
  have hs : IsSquare ((3*u.num^4-10*u.num^2*(u.den : ℤ)^2+3*(u.den : ℤ)^4 : ℤ) : ℚ) := by
    refine ⟨v*(u.den : ℚ)^2, ?_⟩
    push_cast
    rw [hn]
    linear_combination (u.den : ℚ)^4*hv
  obtain ⟨c,hc⟩ := Rat.isSquare_intCast_iff.mp hs
  have hdiv := quartic_three_dvd (by simpa only [pow_two] using hc.symm)
  obtain ⟨r,s,hrs⟩ := u.isCoprime_num_den
  have hh : (3 : ℤ) ∣ 1 := by
    rw [← hrs]
    exact dvd_add (dvd_mul_of_dvd_right hdiv.1 r) (dvd_mul_of_dvd_right hdiv.2 s)
  norm_num at hh

/-- The simultaneous square conditions give a point on the conductor-24
elliptic curve. This is an algebraic reduction, not a rational-point bound. -/
lemma curve_point {u v w : ℚ} (hv : v^2 = u^2+1) (hw : w^2 = u^2+4) :
    (u*v*w)^2 = (u^2)*(u^2+1)*(u^2+4) := by
  rw [mul_pow, mul_pow, hv, hw]

/-- Explicit image under the 2-isogeny. -/
lemma isogenous_curve_point {u v w : ℚ} (hu : u ≠ 0)
    (hv : v^2 = u^2+1) (hw : w^2 = u^2+4) :
    (v*w*(4-u^4)/u^3)^2 =
      ((v*w/u)^2)*((v*w/u)^2-1)*((v*w/u)^2-9) := by
  simp only [mul_pow, div_pow]
  rw [hv, hw]
  field_simp
  ring

#print axioms quartic_not_square
#print axioms curve_point
#print axioms isogenous_curve_point

end Erdos213.OrthogonalDescent
