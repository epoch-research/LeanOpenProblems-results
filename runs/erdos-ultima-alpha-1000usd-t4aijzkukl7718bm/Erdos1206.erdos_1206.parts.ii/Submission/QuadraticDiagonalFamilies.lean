import FormalConjecturesUtil

/-!
An auxiliary obstruction to quadratic parametrizations through the diagonal.
This is NOT a proof or disproof of the positive-density conjecture.
-/

namespace Erdos1206.QuadraticDiagonalFamilies
open Polynomial

private lemma same_quadratic_zeros {p u w : ℝ} (hp : p ≠ 0)
    (h : ∀ t : ℝ, t * (p + u*t) = 0 ↔ t * (p + w*t) = 0) : u = w := by
  have step (u w : ℝ) (hu : u ≠ 0)
      (h : ∀ t : ℝ, t * (p + u*t) = 0 → t * (p + w*t) = 0) : u = w := by
    have ht : -p/u ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp) hu
    have hz : (-p/u) * (p + u*(-p/u)) = 0 := by field_simp; ring
    have he := (mul_eq_zero.mp (h _ hz)).resolve_left ht
    field_simp at he
    apply mul_left_cancel₀ hp
    nlinarith only [he]
  by_cases hu : u = 0
  · by_cases hw : w = 0
    · exact hu.trans hw.symm
    · exact (step w u hw (fun t ht => (h t).mpr ht)).symm
  · exact step u w hu (fun t ht => (h t).mp ht)

/-- A quadratic polynomial with fixed constant coefficient one. -/
noncomputable def Q (a b : ℝ) : ℝ[X] := 1 + C a * X + C b * X^2

@[simp] lemma eval_Q (a b t : ℝ) : (Q a b).eval t = 1 + a*t + b*t^2 := by
  simp [Q]

@[simp] lemma coeff_Q_zero (a b : ℝ) : (Q a b).coeff 0 = 1 := by
  simp [Q]

private lemma normalized_product_zero (a b p u q v : ℝ)
    (h : Q a b ^ 3 + Q (a+p+q) (b+u+v-2*p*q) ^ 3 =
      Q (a+p) (b+u) ^ 3 + Q (a+q) (b+v) ^ 3) : p*q = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  have hz (t : ℝ) : t*(p+u*t) = 0 ↔ t*(p+(u-2*p*q)*t) = 0 := by
    have he := congrArg (fun f : ℝ[X] => f.eval t) h
    simp only [eval_add, eval_pow, eval_Q] at he
    constructor
    · intro ht
      have hab : 1+a*t+b*t^2 = 1+(a+p)*t+(b+u)*t^2 := by
        nlinarith only [ht]
      rw [hab] at he
      have hd : (1+(a+p+q)*t+(b+u+v-2*p*q)*t^2)^3 =
          (1+(a+q)*t+(b+v)*t^2)^3 := by linarith only [he]
      have hd' := (Odd.pow_inj (by decide : Odd 3)).mp hd
      nlinarith only [hd']
    · intro ht
      have hdc : 1+(a+p+q)*t+(b+u+v-2*p*q)*t^2 =
          1+(a+q)*t+(b+v)*t^2 := by nlinarith only [ht]
      rw [hdc] at he
      have ha : (1+a*t+b*t^2)^3 = (1+(a+p)*t+(b+u)*t^2)^3 := by
        linarith only [he]
      have ha' := (Odd.pow_inj (by decide : Odd 3)).mp ha
      nlinarith only [ha']
  have hu := same_quadratic_zeros hp hz
  nlinarith only [hu]

private lemma pairs_of_sum_and_cubes {A B C D : ℝ[X]}
    (hs : A+D = B+C) (he : A^3+D^3 = B^3+C^3) (hne : A+D ≠ 0) :
    (A=B ∧ D=C) ∨ (A=C ∧ D=B) := by
  have hd : D = B+C-A := by linear_combination hs
  have hf : (3:ℝ[X]) * (A-B) * (A-C) * (A+D) = 0 := by
    rw [hd] at he ⊢
    linear_combination he
  have hh : (A-B)*(A-C) = 0 := by
    have hh := (mul_eq_zero.mp hf).resolve_right hne
    have : (3:ℝ[X]) * ((A-B)*(A-C)) = 0 := by simpa only [mul_assoc] using hh
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hh with hab | hac
  · left
    have hab' := sub_eq_zero.mp hab
    refine ⟨hab', ?_⟩
    rw [hab'] at hs
    exact add_left_cancel hs
  · right
    have hac' := sub_eq_zero.mp hac
    refine ⟨hac', ?_⟩
    rw [hac'] at hs
    linear_combination hs

/-- The coefficient-normalized quadratic family has only the trivial pairings. -/
theorem normalized_trivial (a b p u q v : ℝ)
    (h : Q a b ^ 3 + Q (a+p+q) (b+u+v-2*p*q) ^ 3 =
      Q (a+p) (b+u) ^ 3 + Q (a+q) (b+v) ^ 3) :
    (Q a b = Q (a+p) (b+u) ∧
      Q (a+p+q) (b+u+v-2*p*q) = Q (a+q) (b+v)) ∨
    (Q a b = Q (a+q) (b+v) ∧
      Q (a+p+q) (b+u+v-2*p*q) = Q (a+p) (b+u)) := by
  have hpq := normalized_product_zero a b p u q v h
  have hs : Q a b + Q (a+p+q) (b+u+v-2*p*q) =
      Q (a+p) (b+u) + Q (a+q) (b+v) := by
    have he : b+u+v-2*p*q = b+u+v := by nlinarith only [hpq]
    rw [he]
    simp only [Q, map_add]
    ring
  apply pairs_of_sum_and_cubes hs h
  intro hz
  have hc := congrArg (fun f : ℝ[X] => f.coeff 0) hz
  simp at hc

private lemma cube_Q_expansion (a b : ℝ) :
    Q a b ^ 3 = 1 + C (3*a)*X + C (3*b+3*a^2)*X^2 +
      C (a^3+6*a*b)*X^3 + C (3*a^2*b+3*b^2)*X^4 +
      C (3*a*b^2)*X^5 + C (b^3)*X^6 := by
  simp only [Q, map_add, map_mul, map_pow, map_ofNat]
  ring

private lemma cube_Q_coeff_one (a b : ℝ) : (Q a b ^ 3).coeff 1 = 3*a := by
  rw [cube_Q_expansion]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_one]
  simp only [ite_true, ite_false, zero_add, add_zero]

private lemma cube_Q_coeff_two (a b : ℝ) : (Q a b ^ 3).coeff 2 = 3*b+3*a^2 := by
  rw [cube_Q_expansion]
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_one]
  simp only [ite_true, ite_false, zero_add, add_zero]

@[simp] lemma Q_eq_iff (a b c d : ℝ) : Q a b = Q c d ↔ a=c ∧ b=d := by
  constructor
  · intro he
    constructor
    · have hh := congrArg (fun f : ℝ[X] => f.coeff 1) he
      simpa [Q] using hh
    · have hh := congrArg (fun f : ℝ[X] => f.coeff 2) he
      simpa [Q] using hh
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Four quadratic polynomials equal to one at zero can satisfy the cubic
identity only by one of the two trivial pairings. -/
theorem polynomial_trivial (a b c d e f g h : ℝ)
    (he : Q a b ^ 3 + Q g h ^ 3 = Q c d ^ 3 + Q e f ^ 3) :
    (Q a b = Q c d ∧ Q g h = Q e f) ∨
      (Q a b = Q e f ∧ Q g h = Q c d) := by
  have h₁ := congrArg (fun P : ℝ[X] => P.coeff 1) he
  have h₂ := congrArg (fun P : ℝ[X] => P.coeff 2) he
  simp only [coeff_add, cube_Q_coeff_one] at h₁
  simp only [coeff_add, cube_Q_coeff_two] at h₂
  have hg : g = a+(c-a)+(e-a) := by linarith only [h₁]
  have hh : h = b+(d-b)+(f-b)-2*(c-a)*(e-a) := by
    rw [hg] at h₂
    nlinarith only [h₂]
  have hac : a+(c-a)=c := by ring
  have hae : a+(e-a)=e := by ring
  have hbd : b+(d-b)=d := by ring
  have hbf : b+(f-b)=f := by ring
  have hn : Q a b ^ 3 +
      Q (a+(c-a)+(e-a)) (b+(d-b)+(f-b)-2*(c-a)*(e-a)) ^ 3 =
      Q (a+(c-a)) (b+(d-b)) ^ 3 + Q (a+(e-a)) (b+(f-b)) ^ 3 := by
    rw [← hg, ← hh, hac, hae, hbd, hbf]
    exact he
  have ht := normalized_trivial a b (c-a) (d-b) (e-a) (f-b) hn
  rw [← hg, ← hh, hac, hae, hbd, hbf] at ht
  exact ht

/-- Functional version: even over the reals, there is no nontrivial family
of degree at most two through the diagonal point (1,1,1,1). -/
theorem quadratic_family_trivial (a b c d e f g h : ℝ)
    (he : ∀ t : ℝ, (1+a*t+b*t^2)^3 + (1+g*t+h*t^2)^3 =
      (1+c*t+d*t^2)^3 + (1+e*t+f*t^2)^3) :
    ((a=c ∧ b=d) ∧ (g=e ∧ h=f)) ∨ ((a=e ∧ b=f) ∧ (g=c ∧ h=d)) := by
  have hp : Q a b ^ 3 + Q g h ^ 3 = Q c d ^ 3 + Q e f ^ 3 := by
    apply Polynomial.funext
    intro t
    simpa only [eval_add, eval_pow, eval_Q] using he t
  simpa only [Q_eq_iff] using polynomial_trivial a b c d e f g h hp

#print axioms normalized_trivial
#print axioms polynomial_trivial
#print axioms quadratic_family_trivial
end Erdos1206.QuadraticDiagonalFamilies
