import Submission.CircleLineRigidity

/-! An obstruction to a low-degree deformation strategy, not a proof of Erdős 213.
The parameter identities below must hold as rational functions, not just at
individual rational parameter values. -/
namespace Erdos213.QuadraticMotion
open Polynomial CircleLineRigidity
noncomputable section

lemma squarefree_conjugate_fixed {f : ℂ[X]} (hf : f ≠ 0)
    (hsf : Squarefree f) (hc : f.coeff 0 ≠ 0)
    (hreal : (starRingEnd ℂ) (f.coeff 0) = f.coeff 0)
    (hsq : IsSquare (f * f.map (starRingEnd ℂ))) :
    f.map (starRingEnd ℂ) = f := by
  obtain ⟨q,hq⟩ := squarefree_dvd_partner hf hsf hsq
  have hg : f.map (starRingEnd ℂ) ≠ 0 := by simpa using hf
  have hq0 : q ≠ 0 := by intro h; apply hg; simp [hq,h]
  have hd := congrArg (fun p : ℂ[X] => p.natDegree) hq
  change (f.map (starRingEnd ℂ)).natDegree = (f*q).natDegree at hd
  rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective, natDegree_mul hf hq0] at hd
  have hn : q.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hn] at hq
  have hz := congrArg (fun p : ℂ[X] => p.coeff 0) hq
  simp only [coeff_map, coeff_mul_C, hreal] at hz
  have hq1 : q.coeff 0 = 1 := by
    apply mul_left_cancel₀ hc
    simpa using hz.symm
  simpa [hq1] using hq

/-- A non-real quadratic with real nonzero constant coefficient and square norm
must have zero complex discriminant. The leading coefficient may vanish. -/
lemma quadratic_type (a : ℝ) (b c : ℂ) (ha : a ≠ 0)
    (hsq : IsSquare (quad c b (a : ℂ) *
      (quad c b (a : ℂ)).map (starRingEnd ℂ))) :
    b^2-4*c*(a : ℂ)=0 ∨ (b.im=0 ∧ c.im=0) := by
  by_cases hd : b^2-4*c*(a : ℂ)=0
  · exact Or.inl hd
  right
  have hconst : (quad c b (a : ℂ)).coeff 0 ≠ 0 := by simpa only [quad_coeff_zero, ne_eq, Complex.ofReal_eq_zero] using ha
  have hf : quad c b (a : ℂ) ≠ 0 := by
    intro h
    exact hconst (by rw [h]; simp)
  have hh := squarefree_conjugate_fixed hf (quad_separable c b (a : ℂ) hd).squarefree
    hconst (by simp [quad_coeff_zero]) hsq
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hh
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hh
  simp only [coeff_map, quad_coeff_one, quad_coeff_two] at h1 h2
  exact ⟨Complex.conj_eq_iff_im.mp h1, Complex.conj_eq_iff_im.mp h2⟩

def normPolynomial (a : ℝ) (b c : ℂ) : ℝ[X] :=
  (quad c.re b.re a)^2+(quad c.im b.im 0)^2

lemma quadratic_type_ratFunc (a : ℝ) (b c : ℂ) (ha : a ≠ 0)
    (hsq : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (normPolynomial a b c))) :
    b^2-4*c*(a : ℂ)=0 ∨ (b.im=0 ∧ c.im=0) := by
  apply quadratic_type a b c ha
  rw [quad_map, quad_conjugate_product]
  obtain ⟨p,hp⟩ := polynomial_square_of_ratFunc_square _ hsq
  refine ⟨p.map (algebraMap ℝ ℂ), ?_⟩
  simpa [normPolynomial, map_mul] using congrArg (Polynomial.map (algebraMap ℝ ℂ)) hp

lemma quadratic_imag_zero (a : ℝ) (b c : ℂ) (ha : a ≠ 0)
    (h : b^2-4*c*(a : ℂ)=0 ∨ (b.im=0 ∧ c.im=0)) (hb : b.im=0) : c.im=0 := by
  rcases h with h | h
  · have hh := congrArg Complex.im h
    simp [pow_two, Complex.mul_im, hb] at hh
    rcases hh with h | h
    · exact h
    · exact False.elim (ha h)
  · exact h.2

lemma null_triangle (a d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0)
    (b c e f : ℂ)
    (h1 : b^2-4*c*(a : ℂ)=0) (h2 : e^2-4*f*(d : ℂ)=0)
    (h3 : (e-b)^2-4*(f-c)*((d-a : ℝ) : ℂ)=0) :
    e=((d/a : ℝ) : ℂ)*b ∧ f=((d/a : ℝ) : ℂ)*c := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hn : ((a : ℂ)*e-(d : ℂ)*b)^2=0 := by
    push_cast at h3
    linear_combination (a : ℂ)*d*h3-(a : ℂ)*(d-a)*h2+(d : ℂ)*(d-a)*h1
  have he : (a : ℂ)*e=(d : ℂ)*b := sub_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hf : (a : ℂ)*f=(d : ℂ)*c := by
    have hh : (4*(a : ℂ)*d)*((a : ℂ)*f-(d : ℂ)*c)=0 := by
      linear_combination (d : ℂ)^2*h1-(a : ℂ)^2*h2+
        ((a : ℂ)*e+(d : ℂ)*b)*he
    have hh' := (mul_eq_zero.mp hh).resolve_left (by exact mul_ne_zero (mul_ne_zero (by norm_num) ha') hd')
    exact sub_eq_zero.mp hh'
  constructor
  · push_cast
    field_simp
    linear_combination he
  · push_cast
    field_simp
    linear_combination hf

def motion (a : ℝ) (b c : ℂ) (t : ℝ) : ℂ := (a : ℂ)+b*t+c*t^2

def cross (z w : ℂ) : ℝ := z.re*w.im-z.im*w.re

lemma cross_real_mul (z : ℂ) (r : ℝ) : cross z ((r : ℂ)*z)=0 := by
  simp [cross, Complex.mul_re, Complex.mul_im]
  ring

/-- Three different vertical velocities force the whole triple to stay on a line. -/
lemma three_distinct_velocities (a : Fin 3 → ℝ) (b c : Fin 3 → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective (fun i => (b i).im))
    (hsq : ∀ i j, i ≠ j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a j-a i) (b j-b i) (c j-c i)))) (t : ℝ) :
    cross (motion (a 1) (b 1) (c 1) t-motion (a 0) (b 0) (c 0) t)
      (motion (a 2) (b 2) (c 2) t-motion (a 0) (b 0) (c 0) t)=0 := by
  have hd (i j : Fin 3) (hij : i ≠ j) :
      (b j-b i)^2-4*(c j-c i)*((a j-a i : ℝ) : ℂ)=0 := by
    have h := quadratic_type_ratFunc (a j-a i) (b j-b i) (c j-c i)
      (sub_ne_zero.mpr (ha.ne hij.symm)) (hsq i j hij)
    rcases h with h | h
    · exact h
    · have he : (b j).im=(b i).im := sub_eq_zero.mp (by simpa using h.1)
      exact False.elim (hij (hb he).symm)
  have hh := null_triangle (a 1-a 0) (a 2-a 0)
    (sub_ne_zero.mpr (ha.ne (by decide))) (sub_ne_zero.mpr (ha.ne (by decide)))
    (b 1-b 0) (c 1-c 0) (b 2-b 0) (c 2-c 0)
    (hd 0 1 (by decide)) (hd 0 2 (by decide)) (by
      simpa only [sub_sub_sub_cancel_right] using hd 1 2 (by decide))
  have he : motion (a 2) (b 2) (c 2) t-motion (a 0) (b 0) (c 0) t =
      (((a 2-a 0)/(a 1-a 0) : ℝ) : ℂ)*
        (motion (a 1) (b 1) (c 1) t-motion (a 0) (b 0) (c 0) t) := by
    have hcst : ((a 2-a 0 : ℝ) : ℂ) =
        (((a 2-a 0)/(a 1-a 0) : ℝ) : ℂ)*((a 1-a 0 : ℝ) : ℂ) := by
      exact_mod_cast (div_mul_cancel₀ (a 2-a 0) (sub_ne_zero.mpr (ha.ne (by decide : (1 : Fin 3) ≠ 0)))).symm
    simp only [Complex.ofReal_sub] at hcst
    dsimp [motion]
    linear_combination hcst+(t : ℂ)*hh.1+(t : ℂ)^2*hh.2
  rw [he]
  exact cross_real_mul _ _

/-- Among five colors there is a constant triple or a pairwise different triple. -/
lemma five_colors {α : Type*} (f : Fin 5 → α) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ((f i=f j ∧ f j=f k) ∨ (f i ≠ f j ∧ f i ≠ f k ∧ f j ≠ f k)) := by
  by_contra h
  have hn (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ¬ ((f i=f j ∧ f j=f k) ∨ (f i ≠ f j ∧ f i ≠ f k ∧ f j ≠ f k)) := by
    intro hh
    exact h ⟨i,j,k,hij,hik,hjk,hh⟩
  have h012 := hn 0 1 2 (by decide) (by decide) (by decide)
  have h013 := hn 0 1 3 (by decide) (by decide) (by decide)
  have h014 := hn 0 1 4 (by decide) (by decide) (by decide)
  have h023 := hn 0 2 3 (by decide) (by decide) (by decide)
  have h024 := hn 0 2 4 (by decide) (by decide) (by decide)
  have h034 := hn 0 3 4 (by decide) (by decide) (by decide)
  have h123 := hn 1 2 3 (by decide) (by decide) (by decide)
  have h124 := hn 1 2 4 (by decide) (by decide) (by decide)
  have h134 := hn 1 3 4 (by decide) (by decide) (by decide)
  have h234 := hn 2 3 4 (by decide) (by decide) (by decide)
  clear hn h
  grind

/-- Five quadratic polynomial motions initially at distinct positions on the
real axis, with all squared distances square in the rational-function field,
have a fixed triple that is collinear throughout the motion. -/
lemma five_motion_collinear_triple (a : Fin 5 → ℝ) (b c : Fin 5 → ℂ)
    (ha : Function.Injective a)
    (hsq : ∀ i j, i ≠ j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a j-a i) (b j-b i) (c j-c i)))) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ∀ t : ℝ,
      cross (motion (a j) (b j) (c j) t-motion (a i) (b i) (c i) t)
        (motion (a k) (b k) (c k) t-motion (a i) (b i) (c i) t)=0 := by
  obtain ⟨i,j,k,hij,hik,hjk,hm | hr⟩ := five_colors (fun i => (b i).im)
  · refine ⟨i,j,k,hij,hik,hjk,?_⟩
    have hcij : (c j).im=(c i).im := by
      apply sub_eq_zero.mp
      exact quadratic_imag_zero (a j-a i) (b j-b i) (c j-c i)
        (sub_ne_zero.mpr (ha.ne hij.symm))
        (quadratic_type_ratFunc _ _ _ (sub_ne_zero.mpr (ha.ne hij.symm)) (hsq i j hij))
        (by simp [hm.1])
    have hcik : (c k).im=(c i).im := by
      apply sub_eq_zero.mp
      exact quadratic_imag_zero (a k-a i) (b k-b i) (c k-c i)
        (sub_ne_zero.mpr (ha.ne hik.symm))
        (quadratic_type_ratFunc _ _ _ (sub_ne_zero.mpr (ha.ne hik.symm)) (hsq i k hik))
        (by simp [hm.1,hm.2])
    intro t
    have hj : (motion (a j) (b j) (c j) t-motion (a i) (b i) (c i) t).im=0 := by
      simp [motion, pow_two, Complex.mul_im, hcij, hm.1]
    have hk : (motion (a k) (b k) (c k) t-motion (a i) (b i) (c i) t).im=0 := by
      simp [motion, pow_two, Complex.mul_im, hcik, hm.1, hm.2]
    simp [cross,hj,hk]
  · let e : Fin 3 → Fin 5 := ![i,j,k]
    have he : Function.Injective e := by
      intro x y
      fin_cases x <;> fin_cases y <;>
        simp [e, Matrix.cons_val, hij, hik, hjk, hij.symm, hik.symm, hjk.symm]
    have hb : Function.Injective (fun x => (b (e x)).im) := by
      intro x y
      fin_cases x <;> fin_cases y <;>
        simp [e, Matrix.cons_val, hr.1, hr.2.1, hr.2.2,
          hr.1.symm, hr.2.1.symm, hr.2.2.symm]
    refine ⟨i,j,k,hij,hik,hjk,?_⟩
    intro t
    exact three_distinct_velocities (a ∘ e) (b ∘ e) (c ∘ e) (ha.comp he) hb
      (fun x y hxy => hsq _ _ (he.ne hxy)) t

lemma normPolynomial_eval (a : ℝ) (b c : ℂ) (t : ℝ) :
    (normPolynomial a b c).eval t = (motion a b c t).re^2+(motion a b c t).im^2 := by
  simp [normPolynomial, quad, motion, pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- A four-point control: there are noncollinear quadratic deformations, but
this control is an isosceles trapezoid and hence has four points on a circle. -/
def controlA : Fin 4 → ℝ := ![0,-1,1,-2]
def controlB : Fin 4 → ℂ := ![0,0,2*Complex.I,2*Complex.I]
def controlC : Fin 4 → ℂ := ![0,-1/2,-1,1/2]
def controlD0 : Fin 4 → Fin 4 → ℝ :=
  !![0,1,1,2; 1,0,2,1; 1,2,0,3; 2,1,3,0]
def controlD2 : Fin 4 → Fin 4 → ℝ :=
  !![0,1/2,1,1/2; 1/2,0,1/2,1; 1,1/2,0,-3/2; 1/2,1,-3/2,0]

lemma control_squares (i j : Fin 4) :
    normPolynomial (controlA j-controlA i) (controlB j-controlB i)
      (controlC j-controlC i) =
        (C (controlD0 i j)+C (controlD2 i j)*X^2)^2 := by
  apply Polynomial.funext
  intro t
  fin_cases i <;> fin_cases j <;>
    norm_num [normPolynomial, quad, controlA, controlB, controlC,
      controlD0, controlD2, Matrix.cons_val, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- A collision control: reflecting the third point produces a GP kite at
suitable parameters. The last two initial positions coincide, so the distinct
initial-position hypothesis of the obstruction is genuinely important. -/
def kiteA : Fin 4 → ℝ := ![0,-1,1,1]
def kiteB : Fin 4 → ℂ := ![0,0,2*Complex.I,-2*Complex.I]
def kiteC : Fin 4 → ℂ := ![0,-1/2,-1,-1]
def kiteD0 : Fin 4 → Fin 4 → ℝ :=
  !![0,1,1,1; 1,0,2,2; 1,2,0,0; 1,2,0,0]
def kiteD1 : Fin 4 → Fin 4 → ℝ :=
  !![0,0,0,0; 0,0,0,0; 0,0,0,4; 0,0,4,0]
def kiteD2 : Fin 4 → Fin 4 → ℝ :=
  !![0,1/2,1,1; 1/2,0,1/2,1/2; 1,1/2,0,0; 1,1/2,0,0]

lemma kite_squares (i j : Fin 4) :
    normPolynomial (kiteA j-kiteA i) (kiteB j-kiteB i) (kiteC j-kiteC i) =
      (C (kiteD0 i j)+C (kiteD1 i j)*X+C (kiteD2 i j)*X^2)^2 := by
  apply Polynomial.funext
  intro t
  fin_cases i <;> fin_cases j <;>
    norm_num [normPolynomial, quad, kiteA, kiteB, kiteC,
      kiteD0, kiteD1, kiteD2, Matrix.cons_val, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring

#print axioms quadratic_type_ratFunc
#print axioms null_triangle
#print axioms three_distinct_velocities
#print axioms five_motion_collinear_triple
#print axioms normPolynomial_eval
#print axioms control_squares
#print axioms kite_squares
end
end Erdos213.QuadraticMotion
