import FormalConjecturesUtil

/-!
A rational obstruction in the exceptional chart of a degree-eleven quintic
polynomial construction. This is not an unrestricted representation-count bound.
-/
namespace Erdos322Research.QuinticWeightedAffineExceptional

noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

private instance : Fact (Nat.Prime 43) := ⟨by decide⟩

private def sexticHom {R : Type*} [CommRing R] (a b : R) : R :=
  69625000000000*a^6 + 6870000000000*a^5*b + 204750000000*a^4*b^2 +
    2200000000*a^3*b^3 + 11150000*a^2*b^4 + 29200*a*b^5 + 31*b^6

private theorem mod43_no_root : ∀ a : ZMod 43,
    27*a^6+20*a^5+42*a^4+30*a^3+14*a^2+3*a+31 ≠ 0 := by
  decide +kernel

private theorem mod43_hom_zero (a b : ZMod 43) (h : sexticHom a b = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · have ha : a = 0 := by
      norm_num [sexticHom, hb] at h
      exact h.resolve_left (by decide)
    exact ⟨ha, hb⟩
  · have he : sexticHom (a/b) 1 = sexticHom a b / b^6 := by
      unfold sexticHom
      field_simp
    have hz : sexticHom (a/b) 1 = 0 := by rw [he, h, zero_div]
    norm_num [sexticHom] at hz
    exact (mod43_no_root (a/b) hz).elim

/-- The sextic forced by the exceptional coefficient equations has no
rational zero. Primitive numerator and denominator handle all denominators. -/
theorem sextic_no_rational_root (D : ℚ) :
    69625000000000*D^6+6870000000000*D^5+204750000000*D^4+
      2200000000*D^3+11150000*D^2+29200*D+31 ≠ 0 := by
  intro h
  have hd : (D.den : ℚ) ≠ 0 := by exact_mod_cast D.den_ne_zero
  have hh : sexticHom (D.num : ℚ) (D.den : ℚ) = 0 := by
    rw [← D.num_div_den] at h
    field_simp at h
    dsimp [sexticHom]
    linear_combination h
  have hi : sexticHom D.num (D.den : ℤ) = 0 := by
    unfold sexticHom at hh ⊢
    exact_mod_cast hh
  have hm : sexticHom (D.num : ZMod 43) (D.den : ZMod 43) = 0 := by
    have he := congrArg (Int.castRingHom (ZMod 43)) hi
    simpa [sexticHom] using he
  obtain ⟨ha, hb⟩ := mod43_hom_zero _ _ hm
  obtain ⟨u, v, huv⟩ := D.isCoprime_num_den
  have he := congrArg (Int.castRingHom (ZMod 43)) huv
  norm_num [ha, hb] at he

/-- Two fifth powers with vanishing constant and quadratic coefficients
satisfy this relation between their odd moments. -/
theorem two_affine_odd_moments (a b c d : ℚ)
    (h0 : a^5+c^5 = 0) (h2 : a^3*b^2+c^3*d^2 = 0) :
    (a^4*b+c^4*d)*(b^5+d^5) = (a^2*b^3+c^2*d^3)^2 := by
  have hc : c = -a := (show StrictMono (fun x : ℚ => x^5) from
      (by decide : Odd 5).strictMono_pow).injective (by
    simp only [neg_pow, show (-1 : ℚ)^5 = -1 by norm_num, neg_mul, one_mul]
    linarith)
  subst c
  by_cases ha : a = 0
  · simp [ha]
  · have he : a^3*(b^2-d^2) = 0 := by linear_combination h2
    have hs : b^2 = d^2 := sub_eq_zero.mp
      ((mul_eq_zero.mp he).resolve_left (pow_ne_zero _ ha))
    obtain hb | hb := (sq_eq_sq_iff_eq_or_eq_neg).mp hs
    · subst b; ring
    · rw [hb]; ring

private def a₂ (D : ℚ) : ℚ :=
  131/125*D^4+128/3125*D^3+24/78125*D^2+2/1953125*D+1/781250000
private def a₄ (D : ℚ) : ℚ :=
  28/25*D^3+71/1250*D^2+6/15625*D+1/1562500
private def a₆ (D : ℚ) : ℚ := 2/5*D^2+3/125*D+7/50000

private def affineFifth (a b : ℚ) : ℚ[X] := (C b*X+C a)^5
private def basePolynomial (D : ℚ) : ℚ[X] :=
  C (a₆ D)*X^6+C (a₄ D)*X^4+C (a₂ D)*X^2

private theorem affineFifth_coeff (a b : ℚ) (j : ℕ) :
    (affineFifth a b).coeff j = (Nat.choose 5 j : ℚ)*(a^(5-j)*b^j) := by
  have he : affineFifth a b = ((X+C a)^5).comp (C b*X) := by simp [affineFifth]
  rw [he, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  ring

/-- No two rational affine fifth powers can supply the remainder in the
exceptional chart. There are no sign or nonvanishing hypotheses. -/
theorem no_affine_remainder (D a b c d : ℚ) :
    ¬ (∀ t : ℚ, a₆ D*t^6+a₄ D*t^4+a₂ D*t^2+
      t*((a+b*t)^5+(c+d*t)^5) = 0) := by
  intro hid
  have hp : basePolynomial D+X*(affineFifth a b+affineFifth c d) = 0 := by
    apply Polynomial.funext
    intro t
    simpa [basePolynomial, affineFifth, add_comm] using hid t
  have hc (j : ℕ) : (basePolynomial D).coeff (j+1)+
      (affineFifth a b).coeff j+(affineFifth c d).coeff j = 0 := by
    have he := congrArg (fun P : ℚ[X] => P.coeff (j+1)) hp
    simpa only [coeff_add, coeff_X_mul, coeff_zero, add_assoc] using he
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h5 := hc 5
  norm_num [basePolynomial, affineFifth_coeff, coeff_C_mul, coeff_X_pow,
    Nat.choose] at h0 h1 h2 h3 h5
  have hm := two_affine_odd_moments a b c d h0 (by linarith)
  have hm1 : a^4*b+c^4*d = -a₂ D/5 := by linarith
  have hm3 : a^2*b^3+c^2*d^3 = -a₄ D/10 := by linarith
  have hm5 : b^5+d^5 = -a₆ D := by linarith
  rw [hm1, hm3, hm5] at hm
  apply sextic_no_rational_root D
  dsimp [a₂, a₄, a₆] at hm
  linear_combination 976562500000000*hm

/-- The normalized exceptional degree-eleven construction is impossible
over the rationals. This is only one coefficient chart, not a count bound. -/
theorem no_exceptional_identity (D a b c d : ℚ) :
    ¬ (∀ t : ℚ,
      t*((-t/10+(t^2+D))^5+(-t/10-(t^2+D))^5+(a+b*t)^5+(c+d*t)^5)+
        (t^2+4*D/5+1/250)^5 = (4*D/5+1/250)^5) := by
  intro hid
  apply no_affine_remainder D a b c d
  intro t
  have he :
      t*((-t/10+(t^2+D))^5+(-t/10-(t^2+D))^5+(a+b*t)^5+(c+d*t)^5)+
        (t^2+4*D/5+1/250)^5-(4*D/5+1/250)^5 =
      a₆ D*t^6+a₄ D*t^4+a₂ D*t^2+t*((a+b*t)^5+(c+d*t)^5) := by
    dsimp [a₂, a₄, a₆]
    ring
  rw [← he]
  exact sub_eq_zero.mpr (hid t)

private def baseFamily (S H c₀ D z q : ℚ) : ℚ[X] :=
  let P := C S+C H*X
  let A := X^2+C c₀*X+C D
  let Y := X^2+C z*X+C q
  X*(C (1/16)*P^5+C (5/2)*P^3*A^2+C 5*P*A^4)+Y^5-C (q^5)

private theorem high_coefficients (S H c₀ D z q : ℚ) :
    (baseFamily S H c₀ D z q).coeff 10 = 5*H+1 ∧
    (baseFamily S H c₀ D z q).coeff 9 = 20*H*c₀+5*S+5*z ∧
    (baseFamily S H c₀ D z q).coeff 8 =
      5/2*H^3+30*H*c₀^2+20*S*c₀+20*H*D+10*z^2+5*q ∧
    (baseFamily S H c₀ D z q).coeff 7 =
      5*H^3*c₀+20*H*c₀^3+15/2*S*H^2+30*S*c₀^2+
        60*H*c₀*D+10*z^3+20*S*D+20*z*q := by
  dsimp [baseFamily]
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_mul_C,
    coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num
  ring_nf
  simp

/-- Every pointwise identity in the normalized family with equal middle
coefficients `c₀ = z` is impossible. This includes all signs and degeneracies
of the two affine remainders. -/
theorem no_equal_middle_identity (S H c₀ D z q a b c d : ℚ) (hz : c₀ = z) :
    ¬ (∀ t : ℚ,
      t*((((S+H*t)/2)+(t^2+c₀*t+D))^5+
        (((S+H*t)/2)-(t^2+c₀*t+D))^5+(a+b*t)^5+(c+d*t)^5)+
      (t^2+z*t+q)^5 = q^5) := by
  intro hid
  have hp : baseFamily S H c₀ D z q+X*(affineFifth a b+affineFifth c d) = 0 := by
    apply Polynomial.funext
    intro t
    simp only [baseFamily, affineFifth, eval_add, eval_sub, eval_mul, eval_pow,
      eval_C, eval_X, eval_zero]
    have hh := hid t
    linear_combination hh
  have hc (j : ℕ) : (baseFamily S H c₀ D z q).coeff (j+1)+
      (affineFifth a b).coeff j+(affineFifth c d).coeff j = 0 := by
    have he := congrArg (fun P : ℚ[X] => P.coeff (j+1)) hp
    simpa only [coeff_add, coeff_X_mul, coeff_zero, add_assoc] using he
  obtain ⟨h10, h9, h8, h7⟩ := high_coefficients S H c₀ D z q
  have he10 := hc 9
  have he9 := hc 8
  have he8 := hc 7
  have he7 := hc 6
  norm_num only [show 9+1=10 by rfl, show 8+1=9 by rfl,
    show 7+1=8 by rfl, show 6+1=7 by rfl] at he10 he9 he8 he7
  rw [h10] at he10
  rw [h9] at he9
  rw [h8] at he8
  rw [h7] at he7
  norm_num [affineFifth_coeff, Nat.choose] at he10 he9 he8 he7
  have hH : H = -1/5 := by linarith
  have hS : S = -c₀/5 := by rw [← hz, hH] at he9; linarith
  rw [← hz, hH, hS] at he8 he7
  have hc0 : c₀ = 0 := by linear_combination -50*(he7-4*c₀*he8)
  have hz0 : z = 0 := by rw [← hz, hc0]
  have hS0 : S = 0 := by simp [hS, hc0]
  have hq : q = 4*D/5+1/250 := by rw [hc0] at he8; norm_num at he8; linarith
  apply no_exceptional_identity D a b c d
  intro t
  have hh := hid t
  rw [hS0, hH, hc0, hz0, hq] at hh
  convert hh using 1
  ring

/-- The four high coefficient equations, before either determinant chart
is selected. -/
theorem identity_high_constraints (S H c₀ D z q a b c d : ℚ)
    (hid : ∀ t : ℚ,
      t*((((S+H*t)/2)+(t^2+c₀*t+D))^5+
        (((S+H*t)/2)-(t^2+c₀*t+D))^5+(a+b*t)^5+(c+d*t)^5)+
      (t^2+z*t+q)^5 = q^5) :
    5*H+1 = 0 ∧ 20*H*c₀+5*S+5*z = 0 ∧
    5/2*H^3+30*H*c₀^2+20*S*c₀+20*H*D+10*z^2+5*q = 0 ∧
    5*H^3*c₀+20*H*c₀^3+15/2*S*H^2+30*S*c₀^2+
      60*H*c₀*D+10*z^3+20*S*D+20*z*q = 0 := by
  have hp : baseFamily S H c₀ D z q+X*(affineFifth a b+affineFifth c d) = 0 := by
    apply Polynomial.funext
    intro t
    simp only [baseFamily, affineFifth, eval_add, eval_sub, eval_mul, eval_pow,
      eval_C, eval_X, eval_zero]
    have hh := hid t
    linear_combination hh
  have hc (j : ℕ) : (baseFamily S H c₀ D z q).coeff (j+1)+
      (affineFifth a b).coeff j+(affineFifth c d).coeff j = 0 := by
    have he := congrArg (fun P : ℚ[X] => P.coeff (j+1)) hp
    simpa only [coeff_add, coeff_X_mul, coeff_zero, add_assoc] using he
  obtain ⟨h10, h9, h8, h7⟩ := high_coefficients S H c₀ D z q
  have he10 := hc 9
  have he9 := hc 8
  have he8 := hc 7
  have he7 := hc 6
  norm_num only [show 9+1=10 by rfl, show 8+1=9 by rfl,
    show 7+1=8 by rfl, show 6+1=7 by rfl] at he10 he9 he8 he7
  rw [h10] at he10
  rw [h9] at he9
  rw [h8] at he8
  rw [h7] at he7
  norm_num [affineFifth_coeff, Nat.choose] at he10 he9 he8 he7
  exact ⟨he10, he9, he8, he7⟩

end
end Erdos322Research.QuinticWeightedAffineExceptional
