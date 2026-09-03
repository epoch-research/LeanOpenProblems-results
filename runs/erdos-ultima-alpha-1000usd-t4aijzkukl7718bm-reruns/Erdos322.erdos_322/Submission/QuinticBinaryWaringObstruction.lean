import FormalConjecturesUtil

/-! A rational Waring obstruction for a binary quintic arising in a direct
quadratic construction of quintic peaks. This does not bound the unrestricted
representation count. -/
namespace Erdos322Research.QuinticBinaryWaringObstruction

noncomputable section
open Finset
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Twice the constant coefficient plus the middle coefficient plus twice
the leading coefficient of the product of four dual linear forms. -/
def invariant₀ {R : Type*} [CommRing R] (a b : Fin 4 → R) : R :=
  2*(b 0*b 1*b 2*b 3) +
  (b 0*b 1*a 2*a 3+b 0*a 1*b 2*a 3+b 0*a 1*a 2*b 3+
   a 0*b 1*b 2*a 3+a 0*b 1*a 2*b 3+a 0*a 1*b 2*b 3) +
  2*(a 0*a 1*a 2*a 3)

def invariant₁ {R : Type*} [CommRing R] (a b : Fin 4 → R) : R :=
  (b 0*b 1*b 2*a 3+b 0*b 1*a 2*b 3+b 0*a 1*b 2*b 3+a 0*b 1*b 2*b 3) +
  2*(b 0*a 1*a 2*a 3+a 0*b 1*a 2*a 3+a 0*a 1*b 2*a 3+a 0*a 1*a 2*b 3)

private lemma invariant₀_scale {R : Type*} [CommRing R] (t a b : Fin 4 → R) :
    invariant₀ (fun i ↦ t i * a i) (fun i ↦ t i * b i) =
      (∏ i, t i) * invariant₀ a b := by
  simp only [invariant₀,Fin.prod_univ_four]
  ring

private lemma invariant₁_scale {R : Type*} [CommRing R] (t a b : Fin 4 → R) :
    invariant₁ (fun i ↦ t i * a i) (fun i ↦ t i * b i) =
      (∏ i, t i) * invariant₁ a b := by
  simp only [invariant₁,Fin.prod_univ_four]
  ring

/-- No nonzero split binary quartic over F₃ satisfies these two apolar
relations. This finite check is evaluated by Lean's kernel. -/
theorem mod_three_split_obstruction :
    ∀ a b : Fin 4 → ZMod 3, invariant₀ a b = 0 → invariant₁ a b = 0 →
      ∃ i, a i = 0 ∧ b i = 0 := by
  decide +kernel

private lemma primitive_integer_pair (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ A B : ℤ, ∃ t : ℚ, (A : ℚ) = t*a ∧ (B : ℚ) = t*b ∧
      ¬ ((A : ZMod 3) = 0 ∧ (B : ZMod 3) = 0) := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    refine ⟨0,1,1/b,?_,?_,?_⟩
    · simp [ha]
    · simp [hb]
    · norm_num
  · let r := b/a
    have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    refine ⟨r.den,r.num,(r.den : ℚ)/a,?_,?_,?_⟩
    · push_cast
      field_simp
    · have hr := Rat.mul_den_eq_num r
      change (b/a)*(r.den : ℚ) = (r.num : ℚ) at hr
      rw [←hr]
      ring
    · rintro ⟨hden,hnum⟩
      obtain ⟨u,v,hbez⟩ := r.isCoprime_num_den
      have hh := congrArg (Int.castRingHom (ZMod 3)) hbez
      simp only [Int.cast_natCast] at hden
      norm_num [hden,hnum] at hh

/-- The modular obstruction remains valid for rational forms with arbitrary
denominators: each factor is made primitive separately before reduction. -/
theorem rational_split_obstruction (a b : Fin 4 → ℚ)
    (hp : ∀ i, a i ≠ 0 ∨ b i ≠ 0) :
    ¬ (invariant₀ a b = 0 ∧ invariant₁ a b = 0) := by
  rintro ⟨h₀,h₁⟩
  choose A B t ha hb hab using fun i ↦ primitive_integer_pair (a i) (b i) (hp i)
  have hi₀ : invariant₀ A B = 0 := by
    have hr : invariant₀ (fun i ↦ (A i : ℚ)) (fun i ↦ (B i : ℚ)) = 0 := by
      simp only [ha,hb,invariant₀_scale,h₀,mul_zero]
    unfold invariant₀ at hr ⊢
    dsimp only at hr
    exact_mod_cast hr
  have hi₁ : invariant₁ A B = 0 := by
    have hr : invariant₁ (fun i ↦ (A i : ℚ)) (fun i ↦ (B i : ℚ)) = 0 := by
      simp only [ha,hb,invariant₁_scale,h₁,mul_zero]
    unfold invariant₁ at hr ⊢
    dsimp only at hr
    exact_mod_cast hr
  have hm₀ : invariant₀ (fun i ↦ (A i : ZMod 3)) (fun i ↦ (B i : ZMod 3)) = 0 := by
    have hh := congrArg (Int.castRingHom (ZMod 3)) hi₀
    simpa [invariant₀] using hh
  have hm₁ : invariant₁ (fun i ↦ (A i : ZMod 3)) (fun i ↦ (B i : ZMod 3)) = 0 := by
    have hh := congrArg (Int.castRingHom (ZMod 3)) hi₁
    simpa [invariant₁] using hh
  obtain ⟨i,hi⟩ := mod_three_split_obstruction _ _ hm₀ hm₁
  exact hab i hi

private def mixed₁ {R : Type*} [CommRing R] (a b : Fin 4 → R) : R :=
  b 0*a 1*a 2*a 3+a 0*b 1*a 2*a 3+a 0*a 1*b 2*a 3+a 0*a 1*a 2*b 3
private def mixed₂ {R : Type*} [CommRing R] (a b : Fin 4 → R) : R :=
  b 0*b 1*a 2*a 3+b 0*a 1*b 2*a 3+b 0*a 1*a 2*b 3+
  a 0*b 1*b 2*a 3+a 0*b 1*a 2*b 3+a 0*a 1*b 2*b 3
private def mixed₃ {R : Type*} [CommRing R] (a b : Fin 4 → R) : R :=
  b 0*b 1*b 2*a 3+b 0*b 1*a 2*b 3+b 0*a 1*b 2*b 3+a 0*b 1*b 2*b 3

private lemma dual_expansion (a b : Fin 4 → ℚ) (x y : ℚ) :
    (∏ j, (b j*x-a j*y)) =
      (∏ j, b j)*x^4-mixed₃ a b*x^3*y+mixed₂ a b*x^2*y^2-
        mixed₁ a b*x*y^3+(∏ j, a j)*y^4 := by
  simp only [Fin.prod_univ_four,mixed₁,mixed₂,mixed₃]
  ring

def moment (w a b : Fin 4 → ℚ) (j : ℕ) : ℚ := ∑ i, w i*a i^(5-j)*b i^j

private lemma moment_apolar_relations (w a b : Fin 4 → ℚ) (N : ℚ) (hN : N ≠ 0)
    (h₀ : moment w a b 0 = N) (h₁ : moment w a b 1 = 0)
    (h₂ : moment w a b 2 = N/2) (h₃ : moment w a b 3 = 0)
    (h₄ : moment w a b 4 = N) (h₅ : moment w a b 5 = 0) :
    invariant₀ a b = 0 ∧ invariant₁ a b = 0 := by
  have hroot (i : Fin 4) : (∏ j, (b j*a i-a j*b i)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring
  have hr₀ : (∑ i, w i*a i*(∏ j, (b j*a i-a j*b i))) = 0 := by simp [hroot]
  have hr₁ : (∑ i, w i*b i*(∏ j, (b j*a i-a j*b i))) = 0 := by simp [hroot]
  have he₀ (i : Fin 4) : w i*a i*(∏ j, (b j*a i-a j*b i)) =
      (∏ j, b j)*(w i*a i^5)-mixed₃ a b*(w i*a i^4*b i)+
      mixed₂ a b*(w i*a i^3*b i^2)-mixed₁ a b*(w i*a i^2*b i^3)+
      (∏ j, a j)*(w i*a i*b i^4) := by rw [dual_expansion]; ring
  have he₁ (i : Fin 4) : w i*b i*(∏ j, (b j*a i-a j*b i)) =
      (∏ j, b j)*(w i*a i^4*b i)-mixed₃ a b*(w i*a i^3*b i^2)+
      mixed₂ a b*(w i*a i^2*b i^3)-mixed₁ a b*(w i*a i*b i^4)+
      (∏ j, a j)*(w i*b i^5) := by rw [dual_expansion]; ring
  simp only [he₀,sum_add_distrib,sum_sub_distrib,←Finset.mul_sum] at hr₀
  simp only [he₁,sum_add_distrib,sum_sub_distrib,←Finset.mul_sum] at hr₁
  norm_num only [moment,show 5-0=5 by rfl,show 5-1=4 by rfl,show 5-2=3 by rfl,
    show 5-3=2 by rfl,show 5-4=1 by rfl,show 5-5=0 by rfl,
    pow_zero,pow_one,mul_one] at h₀ h₁ h₂ h₃ h₄ h₅
  rw [h₀,h₁,h₂,h₃,h₄] at hr₀
  rw [h₁,h₂,h₃,h₄,h₅] at hr₁
  have hi₀ : N * invariant₀ a b = 0 := by
    simp only [invariant₀,mixed₂,Fin.prod_univ_four] at *
    linear_combination 2*hr₀
  have hi₁ : N * invariant₁ a b = 0 := by
    simp only [invariant₁,mixed₁,mixed₃,Fin.prod_univ_four] at *
    linear_combination -2*hr₁
  exact ⟨(mul_eq_zero.mp hi₀).resolve_left hN,(mul_eq_zero.mp hi₁).resolve_left hN⟩

/-- Four rational nodes/forms cannot have the normalized moments required
by the binary quintic, even with arbitrary rational weights. -/
theorem no_four_rational_moments (w a b : Fin 4 → ℚ) (N : ℚ) (hN : N ≠ 0)
    (h₀ : moment w a b 0 = N) (h₁ : moment w a b 1 = 0)
    (h₂ : moment w a b 2 = N/2) (h₃ : moment w a b 3 = 0)
    (h₄ : moment w a b 4 = N) (h₅ : moment w a b 5 = 0) : False := by
  classical
  let a' (i : Fin 4) := if a i = 0 ∧ b i = 0 then 1 else a i
  let b' (i : Fin 4) := if a i = 0 ∧ b i = 0 then 0 else b i
  let w' (i : Fin 4) := if a i = 0 ∧ b i = 0 then 0 else w i
  have hp (i : Fin 4) : a' i ≠ 0 ∨ b' i ≠ 0 := by
    by_cases hi : a i = 0 ∧ b i = 0
    · simp [a',b',hi]
    · simpa [a',b',hi] using not_and_or.mp hi
  have hm (j : ℕ) (hj : j ≤ 5) : moment w' a' b' j = moment w a b j := by
    apply sum_congr rfl
    intro i _
    by_cases hi : a i = 0 ∧ b i = 0
    · by_cases hj0 : j = 0
      · subst j
        simp [a',b',w',hi]
      · simp [a',b',w',hi,zero_pow hj0]
    · simp [a',b',w',hi]
  apply rational_split_obstruction a' b' hp
  apply moment_apolar_relations w' a' b' N hN
  · rw [hm 0 (by decide),h₀]
  · rw [hm 1 (by decide),h₁]
  · rw [hm 2 (by decide),h₂]
  · rw [hm 3 (by decide),h₃]
  · rw [hm 4 (by decide),h₄]
  · rw [hm 5 (by decide),h₅]

open Polynomial

def binaryQuintic (u v : ℚ) : ℚ := u^5+5*u^3*v^2+5*u*v^4

private def targetPolynomial : Polynomial ℚ := 1+5*X^2+5*X^4

private lemma affine_fifth_coeff (a b : ℚ) (j : ℕ) :
    ((C b*X+C a)^5).coeff j = (Nat.choose 5 j : ℚ)*(a^(5-j)*b^j) := by
  have he : (C b*X+C a)^5 = ((X+C a)^5).comp (C b*X) := by simp
  rw [he,comp_C_mul_X_coeff,coeff_X_add_C_pow]
  ring

private lemma weighted_fifth_coeff (w a b : Fin 4 → ℚ) (j : ℕ) :
    (∑ i, C (w i)*(C (b i)*X+C (a i))^5).coeff j =
      (Nat.choose 5 j : ℚ)*moment w a b j := by
  simp only [finset_sum_coeff,coeff_C_mul,affine_fifth_coeff,moment,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- The binary quintic has no decomposition into four rational fifth powers
of linear forms, even if arbitrary rational weights are allowed. -/
theorem no_four_weighted_linear_fifths (w a b : Fin 4 → ℚ) (N : ℚ) (hN : N ≠ 0) :
    ¬ (∀ u v : ℚ, ∑ i, w i*(a i*u+b i*v)^5 = N*binaryQuintic u v) := by
  intro h
  have hp : (∑ i, C (w i)*(C (b i)*X+C (a i))^5) = C N*targetPolynomial := by
    apply Polynomial.funext
    intro t
    simpa [eval_finset_sum,targetPolynomial,binaryQuintic,add_comm] using h 1 t
  have hc (j : ℕ) : (Nat.choose 5 j : ℚ)*moment w a b j =
      N*targetPolynomial.coeff j := by
    have hh := congrArg (fun P : Polynomial ℚ ↦ P.coeff j) hp
    simpa only [weighted_fifth_coeff,coeff_C_mul] using hh
  have h₀ := hc 0
  have h₁ := hc 1
  have h₂ := hc 2
  have h₃ := hc 3
  have h₄ := hc 4
  have h₅ := hc 5
  norm_num [targetPolynomial,coeff_one,Nat.choose] at h₀ h₁ h₂ h₃ h₄ h₅
  exact no_four_rational_moments w a b N hN h₀ (by linarith) (by linarith)
    (by linarith) (by linarith) h₅

/-- Five weighted rational linear forms suffice, so the preceding four-term
obstruction is sharp for weighted rational Waring decompositions. -/
theorem five_weighted_linear_fifths (u v : ℚ) :
    binaryQuintic u v =
      (5/8 : ℚ)*u^5 + (1/6 : ℚ)*((u+v)^5+(u-v)^5) +
      (1/48 : ℚ)*((u+2*v)^5+(u-2*v)^5) := by
  unfold binaryQuintic
  ring

theorem chebyshev_substitution (t : ℚ) : binaryQuintic (1-t^2) t = 1-t^10 := by
  unfold binaryQuintic
  ring

private def quadraticModel (a b : ℚ) : Polynomial ℚ := C a*(1-X^2)+C b*X

private lemma quadratic_low_coefficients (a b : ℚ) :
    (quadraticModel a b^5).coeff 0 = a^5 ∧
    (quadraticModel a b^5).coeff 1 = 5*a^4*b ∧
    (quadraticModel a b^5).coeff 2 = -5*a^5+10*a^3*b^2 ∧
    (quadraticModel a b^5).coeff 3 = -20*a^4*b+10*a^2*b^3 ∧
    (quadraticModel a b^5).coeff 4 = 10*a^5-30*a^3*b^2+5*a*b^4 ∧
    (quadraticModel a b^5).coeff 5 = 30*a^4*b-20*a^2*b^3+b^5 := by
  have he : quadraticModel a b^5 =
      C (a^5)+C (5*a^4*b)*X+C (-5*a^5+10*a^3*b^2)*X^2+
      C (-20*a^4*b+10*a^2*b^3)*X^3+C (10*a^5-30*a^3*b^2+5*a*b^4)*X^4+
      C (30*a^4*b-20*a^2*b^3+b^5)*X^5+
      C (-10*a^5+30*a^3*b^2-5*a*b^4)*X^6+
      C (-20*a^4*b+10*a^2*b^3)*X^7+C (5*a^5-10*a^3*b^2)*X^8+
      C (5*a^4*b)*X^9+C (-a^5)*X^10 := by
    simp only [quadraticModel,map_add,map_sub,map_mul,map_pow,map_ofNat,map_neg]
    ring
  rw [he]
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  norm_num

/-- This direct quadratic family cannot have a nonzero constant fifth-power
sum. The weights may even be arbitrary rationals; no positivity or restriction
on denominators is assumed. -/
theorem no_quadratic_chebyshev_identity (w a b : Fin 4 → ℚ) (A N : ℚ) (hN : N ≠ 0) :
    ¬ (∀ t : ℚ, (∑ i, w i*(a i*(1-t^2)+b i*t)^5)+(A*t^2)^5 = N) := by
  intro h
  have hp : (∑ i, C (w i)*quadraticModel (a i) (b i)^5)+C (A^5)*X^10 = C N := by
    apply Polynomial.funext
    intro t
    have ht : (A*t^2)^5 = A^5*t^10 := by ring
    simpa [quadraticModel,eval_finset_sum,ht] using h t
  have h₀ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 0) hp
  have h₁ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 1) hp
  have h₂ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 2) hp
  have h₃ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 3) hp
  have h₄ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 4) hp
  have h₅ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 5) hp
  simp only [coeff_add,finset_sum_coeff,coeff_C_mul,
    (quadratic_low_coefficients _ _).1,(quadratic_low_coefficients _ _).2.1,
    (quadratic_low_coefficients _ _).2.2.1,(quadratic_low_coefficients _ _).2.2.2.1,
    (quadratic_low_coefficients _ _).2.2.2.2.1,(quadratic_low_coefficients _ _).2.2.2.2.2,
    coeff_X_pow,coeff_C] at h₀ h₁ h₂ h₃ h₄ h₅
  norm_num at h₀ h₁ h₂ h₃ h₄ h₅
  apply no_four_rational_moments w a b N hN
  all_goals norm_num [moment,Fin.sum_univ_four] at h₀ h₁ h₂ h₃ h₄ h₅ ⊢
  · exact h₀
  · linear_combination h₁ / 5
  · linear_combination h₂ / 10 + h₀ / 2
  · linear_combination h₃ / 10 + h₁ * (2/5 : ℚ)
  · linear_combination h₄ / 5 + h₂ * (3/5 : ℚ) + h₀
  · linear_combination h₅ + 2*h₃ + 2*h₁

/-- The unweighted five-coordinate version relevant to representation counts. -/
theorem no_five_quadratic_chebyshev_identity (a b : Fin 4 → ℚ) (A N : ℚ) (hN : N ≠ 0) :
    ¬ (∀ t : ℚ, (∑ i, (a i*(1-t^2)+b i*t)^5)+(A*t^2)^5 = N) := by
  simpa using no_quadratic_chebyshev_identity (fun _ ↦ 1) a b A N hN

/-- Scope witness: replacing the normalized core by `1-2*t²` admits a
weighted identity. The weights are not rational fifth powers, so this is
not an unweighted five-coordinate construction for the conjecture. -/
theorem nonsquare_curvature_weighted_identity (t : ℚ) :
    (3/4 : ℚ)*(1-2*t^2)^5 +
      (1/8 : ℚ)*((1-2*t^2+2*t)^5+(1-2*t^2-2*t)^5)+(2*t^2)^5 = 1 := by
  ring

end
end Erdos322Research.QuinticBinaryWaringObstruction
