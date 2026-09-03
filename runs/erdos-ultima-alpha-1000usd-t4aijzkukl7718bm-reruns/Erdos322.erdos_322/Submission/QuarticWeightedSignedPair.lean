import FormalConjecturesUtil

/-! Rational obstruction to a weighted signed quartic polynomial family.
This is a construction classification, not an unrestricted count theorem. -/
namespace Erdos322Research.QuarticWeightedSignedPair

open Polynomial
noncomputable section
set_option Elab.async false

private lemma mod_three_square (z : ZMod 3) (h : 8*z^2=0) : z=0 := by
  have H : ∀ z : ZMod 3, 8*z^2=0 → z=0 := by decide
  exact H z h

private lemma mod_three_two_squares (x y : ZMod 3) (h : x^2+y^2=0) : x=0 ∧ y=0 := by
  have H : ∀ x y : ZMod 3, x^2+y^2=0 → x=0 ∧ y=0 := by decide
  exact H x y h

/-- The ternary quadratic form is anisotropic, by descent at three. -/
theorem integer_quadratic_obstruction (x y z : ℤ) (h : 3*(x^2+y^2)=8*z^2) : z=0 := by
  suffices H : ∀ N : ℕ, ∀ x y z : ℤ, z.natAbs=N → 3*(x^2+y^2)=8*z^2 → z=0 by
    exact H z.natAbs x y z rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro x y z hN he
    by_cases hz : z=0
    · exact hz
    have he3 : (3 : ZMod 3)*((x : ZMod 3)^2+(y : ZMod 3)^2)=8*(z : ZMod 3)^2 := by
      have hc := congrArg (fun a : ℤ => (a : ZMod 3)) he
      push_cast at hc
      exact hc
    have hzr : (z : ZMod 3)=0 := mod_three_square _ (by
      rw [show (3 : ZMod 3)=0 by decide, zero_mul] at he3
      exact he3.symm)
    obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp hzr
    norm_num at hw
    have he' : x^2+y^2=24*w^2 := by rw [hw] at he; nlinarith only [he]
    have her : (x : ZMod 3)^2+(y : ZMod 3)^2=0 := by
      have hc : (x : ZMod 3)^2+(y : ZMod 3)^2=24*(w : ZMod 3)^2 := by
        have hc := congrArg (fun a : ℤ => (a : ZMod 3)) he'
        push_cast at hc
        exact hc
      rw [show (24 : ZMod 3)=0 by decide, zero_mul] at hc
      exact hc
    obtain ⟨hxr, hyr⟩ := mod_three_two_squares _ _ her
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hxr
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hyr
    norm_num at ha hb
    have hnew : 3*(a^2+b^2)=8*w^2 := by
      rw [ha,hb,hw] at he
      nlinarith only [he]
    have hscale : 3*w.natAbs=N := by
      rw [← hN, hw, Int.natAbs_mul]
      norm_num
    have hwN : w.natAbs<N := by
      have hNz : N ≠ 0 := by intro h0; apply hz; exact Int.natAbs_eq_zero.mp (hN.trans h0)
      omega
    have hw0 := ih w.natAbs hwN a b w rfl hnew
    rw [hw, hw0, mul_zero]

/-- The same anisotropy over the rationals, with denominators cleared. -/
theorem rational_quadratic_obstruction (x y z : ℚ) (h : 3*(x^2+y^2)=8*z^2) : z=0 := by
  let v : Fin 3 → ℚ := ![x,y,z]
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
  choose a ha using hd
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero d.property
  have hv (i : Fin 3) : (a i : ℚ)=(d : ℚ)*v i := by
    simpa only [Algebra.smul_def] using ha i
  have he : (3 : ℚ)*((a 0 : ℚ)^2+(a 1 : ℚ)^2)=8*(a 2 : ℚ)^2 := by
    rw [hv, hv, hv]
    dsimp [v]
    linear_combination (d : ℚ)^2*h
  have hz : a 2=0 := integer_quadratic_obstruction _ _ _ (by exact_mod_cast he)
  have hv2 := hv 2
  rw [hz] at hv2
  change 0=(d : ℚ)*z at hv2
  exact (mul_eq_zero.mp hv2.symm).resolve_left hd0

/-- After setting `u=t^4`, the two high-degree coordinates are
`t*(A*u+B)` and `t*(A*u+C₀)`, with opposite signs in the quartic sum. -/
def model (A B C₀ d e f g : ℚ) : ℚ[X] :=
  (C d*X+C e)^4+(C f*X+C g)^4-
    X*((C A*X+C B)^4-(C A*X+C C₀)^4)

private lemma model_coeff4 (A B C₀ d e f g : ℚ) :
    (model A B C₀ d e f g).coeff 4 = d^4+f^4-4*A^3*(B-C₀) := by
  dsimp [model]
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num

private lemma model_coeff3 (A B C₀ d e f g : ℚ) :
    (model A B C₀ d e f g).coeff 3 = 4*(d^3*e+f^3*g)-6*A^2*(B^2-C₀^2) := by
  dsimp [model]
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num

private lemma model_coeff2 (A B C₀ d e f g : ℚ) :
    (model A B C₀ d e f g).coeff 2 = 6*(d^2*e^2+f^2*g^2)-4*A*(B^3-C₀^3) := by
  dsimp [model]
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num

/-- The three top coefficients force the anisotropic quadratic equation. -/
theorem top_coefficients_force_quadratic (A B C₀ d e f g : ℚ)
    (h4 : d^4+f^4=4*A^3*(B-C₀))
    (h3 : 4*(d^3*e+f^3*g)=6*A^2*(B^2-C₀^2))
    (h2 : 6*(d^2*e^2+f^2*g^2)=4*A*(B^3-C₀^3)) :
    3*((A^2*(B^2-C₀^2))^2+(2*d*f*(d*g-e*f))^2)=8*(A^2*(B-C₀)^2)^2 := by
  have hdet : (d^4+f^4)*(d^2*e^2+f^2*g^2)-(d^3*e+f^3*g)^2 =
      d^2*f^2*(d*g-e*f)^2 := by ring
  have h3' : d^3*e+f^3*g=(3/2)*A^2*(B^2-C₀^2) := by linarith
  have h2' : d^2*e^2+f^2*g^2=(2/3)*A*(B^3-C₀^3) := by linarith
  rw [h4, h3', h2'] at hdet
  nlinarith only [hdet]

/-- A nonzero common leading coefficient and distinct high-degree factors
are impossible in a constant identity over the rationals. -/
theorem leading_degeneracy (A B C₀ d e f g N : ℚ)
    (h : model A B C₀ d e f g = C N) : A=0 ∨ B=C₀ := by
  have h4 := congrArg (fun p : ℚ[X] => p.coeff 4) h
  have h3 := congrArg (fun p : ℚ[X] => p.coeff 3) h
  have h2 := congrArg (fun p : ℚ[X] => p.coeff 2) h
  simp only [model_coeff4, coeff_C, show (4 : ℕ) ≠ 0 by decide, if_false] at h4
  simp only [model_coeff3, coeff_C, show (3 : ℕ) ≠ 0 by decide, if_false] at h3
  simp only [model_coeff2, coeff_C, show (2 : ℕ) ≠ 0 by decide, if_false] at h2
  have hquad := top_coefficients_force_quadratic A B C₀ d e f g
    (by linarith) (by linarith) (by linarith)
  have hz := rational_quadratic_obstruction _ _ _ hquad
  rcases mul_eq_zero.mp hz with hz | hz
  · exact Or.inl (eq_zero_of_pow_eq_zero hz)
  · exact Or.inr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz))

/-- Every constant identity in this weighted signed quartic family consists
only of exact cancellation and two constant coordinates. -/
theorem constant_identity_classification (A B C₀ d e f g N : ℚ)
    (h : model A B C₀ d e f g = C N) :
    (A=0 ∨ B=C₀) ∧ d=0 ∧ f=0 ∧ B^4=C₀^4 ∧ N=e^4+g^4 := by
  have hdeg := leading_degeneracy A B C₀ d e f g N h
  have h4 := congrArg (fun p : ℚ[X] => p.coeff 4) h
  simp only [model_coeff4, coeff_C, show (4 : ℕ) ≠ 0 by decide, if_false] at h4
  have hs : d^4+f^4=0 := by
    rcases hdeg with hA | hBC
    · rw [hA] at h4; norm_num at h4; exact h4
    · rw [hBC] at h4; simpa using h4
  have hd4 : d^4=0 := by nlinarith only [hs, show 0 ≤ d^4 by positivity, show 0 ≤ f^4 by positivity]
  have hf4 : f^4=0 := by linarith
  have hd : d=0 := eq_zero_of_pow_eq_zero hd4
  have hf : f=0 := eq_zero_of_pow_eq_zero hf4
  subst d
  subst f
  have h0 := congrArg (fun p : ℚ[X] => p.eval 0) h
  simp only [model, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    mul_zero, zero_add, zero_mul, sub_zero] at h0
  have h1 := congrArg (fun p : ℚ[X] => p.eval 1) h
  simp only [model, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    mul_one, zero_add, one_mul] at h1
  have hBC : B^4=C₀^4 := by
    rcases hdeg with hA | hBC
    · rw [hA] at h1
      simp only [zero_add] at h1
      linarith
    · rw [hBC]
  exact ⟨hdeg,rfl,rfl,hBC,h0.symm⟩

/-- The classification applies to identities in the original parameter,
not just to the weighted-variable polynomial formulation. -/
theorem original_constant_classification (A B C₀ d e f g N : ℚ)
    (h : ∀ t : ℚ, (t*(A*t^4+C₀))^4+(d*t^4+e)^4+(f*t^4+g)^4-
      (t*(A*t^4+B))^4=N) :
    (A=0 ∨ B=C₀) ∧ d=0 ∧ f=0 ∧ B^4=C₀^4 ∧ N=e^4+g^4 := by
  apply constant_identity_classification A B C₀ d e f g N
  have hi : Function.Injective (fun m : ℕ => (m : ℚ)^4) := by
    intro a b hab
    change (a : ℚ)^4=(b : ℚ)^4 at hab
    have hn : a^4=b^4 := by exact_mod_cast hab
    exact Nat.pow_left_injective (by decide : 4 ≠ 0) hn
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hi).mono
  rintro v ⟨m,rfl⟩
  simp only [Set.mem_setOf_eq, model, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, eval_X]
  have hm := h (m : ℚ)
  simp only [mul_pow] at hm
  linear_combination hm

end
end Erdos322Research.QuarticWeightedSignedPair
