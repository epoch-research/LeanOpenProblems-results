import Submission.QuadraticMotion
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! Rigidity of quadratic motions at an initial collision. These are
rational-function identities, not obstructions to individual rational-distance
configurations or a settlement of Erdős 213. -/
namespace Erdos213.QuadraticMotion
open Polynomial CircleLineRigidity
noncomputable section

lemma collision_type (b c : ℂ)
    (hsq : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (normPolynomial 0 b c))) :
    cross b c = 0 := by
  by_cases hb : b = 0
  · simp [hb, cross]
  have hsq' : IsSquare (quad c b (0 : ℂ) *
      (quad c b (0 : ℂ)).map (starRingEnd ℂ)) := by
    rw [quad_map, quad_conjugate_product]
    obtain ⟨p,hp⟩ := polynomial_square_of_ratFunc_square _ hsq
    refine ⟨p.map (algebraMap ℝ ℂ), ?_⟩
    simpa [normPolynomial, map_mul] using
      congrArg (Polynomial.map (algebraMap ℝ ℂ)) hp
  have hf : quad c b (0 : ℂ) ≠ 0 := by
    intro h
    apply hb
    simpa only [quad_coeff_one, coeff_zero] using congrArg (fun p : ℂ[X] => p.coeff 1) h
  have hd : b^2-4*c*(0 : ℂ) ≠ 0 := by simpa using pow_ne_zero 2 hb
  obtain ⟨q,hq⟩ := squarefree_dvd_partner hf
    (quad_separable c b (0 : ℂ) hd).squarefree hsq'
  have hg : (quad c b (0 : ℂ)).map (starRingEnd ℂ) ≠ 0 := by simpa using hf
  have hq0 : q ≠ 0 := by intro h; apply hg; simp [hq,h]
  have hh := congrArg (fun p : ℂ[X] => p.natDegree) hq
  change ((quad c b (0 : ℂ)).map (starRingEnd ℂ)).natDegree =
    (quad c b (0 : ℂ)*q).natDegree at hh
  rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective,
    natDegree_mul hf hq0] at hh
  have hn : q.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hn] at hq
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hq
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hq
  simp only [coeff_map, quad_coeff_one, quad_coeff_two, coeff_mul_C] at h1 h2
  have he : (starRingEnd ℂ) b * c = (starRingEnd ℂ) c * b := by
    rw [h1,h2]
    ring
  have hi := congrArg Complex.im he
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at hi
  dsimp [cross]
  linarith

lemma cross_add_left (u v w : ℂ) : cross (u+v) w = cross u w+cross v w := by
  simp [cross]; ring
lemma cross_sub_left (u v w : ℂ) : cross (u-v) w = cross u w-cross v w := by
  simp [cross]; ring
lemma cross_add_right (u v w : ℂ) : cross u (v+w) = cross u v+cross u w := by
  simp [cross]; ring
lemma cross_sub_right (u v w : ℂ) : cross u (v-w) = cross u v-cross u w := by
  simp [cross]; ring
lemma cross_smul_left (r : ℝ) (u v : ℂ) : cross ((r : ℂ)*u) v = r*cross u v := by
  simp [cross, Complex.mul_re, Complex.mul_im]; ring
lemma cross_smul_right (r : ℝ) (u v : ℂ) : cross u ((r : ℂ)*v) = r*cross u v := by
  simp [cross, Complex.mul_re, Complex.mul_im]; ring
lemma cross_self (u : ℂ) : cross u u = 0 := by dsimp [cross]; ring
lemma cross_swap (u v : ℂ) : cross u v = -cross v u := by dsimp [cross]; ring

lemma cross_sub_scaled (u v w : ℂ) (r : ℝ) :
    cross (v-u) (w-(r : ℂ)*u) = cross v w-cross u (w-(r : ℂ)*v) := by
  simp [cross, Complex.mul_re, Complex.mul_im]
  ring

lemma cross_zero_iff_real_mul {u v : ℂ} (hu : u ≠ 0) :
    cross u v = 0 ↔ ∃ r : ℝ, v = (r : ℂ)*u := by
  constructor
  · intro h
    by_cases hr : u.re = 0
    · have hi : u.im ≠ 0 := by
        intro hh
        exact hu (Complex.ext hr hh)
      refine ⟨v.im/u.im, ?_⟩
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, hr, mul_zero]
        have hh : u.im*v.re = 0 := by simpa [cross,hr] using h
        exact (mul_eq_zero.mp hh).resolve_left hi
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero]
        exact (div_mul_cancel₀ _ hi).symm
    · refine ⟨v.re/u.re, ?_⟩
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero]
        exact (div_mul_cancel₀ _ hr).symm
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero]
        dsimp [cross] at h
        field_simp
        nlinarith
  · rintro ⟨r,rfl⟩
    exact cross_real_mul _ _

lemma two_cross_zero {u v w : ℂ} (huv : cross u v ≠ 0)
    (hu : cross u w = 0) (hv : cross v w = 0) : w = 0 := by
  have hre : cross u v*w.re = 0 := by
    dsimp [cross] at *
    linear_combination v.re*hu-u.re*hv
  have him : cross u v*w.im = 0 := by
    dsimp [cross] at *
    linear_combination v.im*hu-u.im*hv
  apply Complex.ext
  · exact (mul_eq_zero.mp hre).resolve_left huv
  · exact (mul_eq_zero.mp him).resolve_left huv

/-- A parallel redrawing of a complete noncollinear configuration is a
homothety. No arithmetic hypotheses are needed in this linear-algebra lemma. -/
lemma parallel_redrawing {ι : Type*} (b c : ι → ℂ) (i j k : ι)
    (hn : cross (b j-b i) (b k-b i) ≠ 0)
    (h : ∀ u v, cross (b v-b u) (c v-c u) = 0) :
    ∃ r : ℝ, ∃ z : ℂ, ∀ u, c u = (r : ℂ)*b u+z := by
  have hji : b j-b i ≠ 0 := by intro hz; simp [hz,cross] at hn
  obtain ⟨r,hr⟩ := (cross_zero_iff_real_mul hji).mp (h i j)
  have he (u : ι) : cross (b j-b i) (c u-c i-(r : ℂ)*(b u-b i)) = 0 := by
    have hh := h j u
    have hi := h i u
    have hj := h i j
    have hsub : c u-c j = (c u-c i)-(c j-c i) := by ring
    have hbsub : b u-b j = (b u-b i)-(b j-b i) := by ring
    rw [hsub, hbsub, hr, cross_sub_scaled] at hh
    linarith
  have hk : c k-c i = (r : ℂ)*(b k-b i) := by
    apply sub_eq_zero.mp
    apply two_cross_zero hn (he k)
    rw [cross_sub_right, cross_smul_right, cross_self, h i k]
    ring
  refine ⟨r,c i-(r : ℂ)*b i,?_⟩
  intro u
  have he' : cross (b k-b i) (c u-c i-(r : ℂ)*(b u-b i)) = 0 := by
    have hh := h k u
    have hi := h i u
    have hsub : c u-c k = (c u-c i)-(c k-c i) := by ring
    have hbsub : b u-b k = (b u-b i)-(b k-b i) := by ring
    rw [hsub, hbsub, hk, cross_sub_scaled] at hh
    linarith
  have hu := two_cross_zero hn (he u) he'
  linear_combination hu

/-- If every initial position collides and the first-order velocities already
contain a noncollinear triple, square distance identities force a fixed shape.
All noncollapsed realizations have the same shape up to translation and scaling. -/
lemma total_collision_homothety {ι : Type*} (a : ℝ) (b c : ι → ℂ) (i j k : ι)
    (hn : cross (b j-b i) (b k-b i) ≠ 0)
    (hsq : ∀ u v, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial 0 (b v-b u) (c v-c u)))) :
    ∃ r : ℝ, ∃ z : ℂ, ∀ u t,
      motion a (b u) (c u) t = (a : ℂ)+z*t^2+
        ((t+r*t^2 : ℝ) : ℂ)*b u := by
  obtain ⟨r,z,h⟩ := parallel_redrawing b c i j k hn
    (fun u v => collision_type _ _ (hsq u v))
  refine ⟨r,z,?_⟩
  intro u t
  rw [h u]
  simp only [motion, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- The same rigidity can be tested at any affine-velocity time, so no
noncollinearity of the first-order velocities at zero is required. -/
lemma total_collision_homothety_at {ι : Type*} (a τ : ℝ) (b c : ι → ℂ) (i j k : ι)
    (hn : cross ((b j+c j*τ)-(b i+c i*τ))
      ((b k+c k*τ)-(b i+c i*τ)) ≠ 0)
    (hsq : ∀ u v, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial 0 (b v-b u) (c v-c u)))) :
    ∃ r : ℝ, ∃ z : ℂ, ∀ u t,
      motion a (b u) (c u) t = (a : ℂ)+z*(t^2-τ*t)+
        ((t+r*(t^2-τ*t) : ℝ) : ℂ)*(b u+c u*τ) := by
  have hc (u v : ι) :
      cross ((b v+c v*τ)-(b u+c u*τ)) (c v-c u) = 0 := by
    have hh := collision_type _ _ (hsq u v)
    have he : (b v+c v*τ)-(b u+c u*τ) = (b v-b u)+(τ : ℂ)*(c v-c u) := by ring
    rw [he, cross_add_left, cross_smul_left, cross_self, hh]
    ring
  obtain ⟨r,z,h⟩ := parallel_redrawing (fun u => b u+c u*τ) c i j k hn hc
  refine ⟨r,z,?_⟩
  intro u t
  simp only [motion, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow]
  linear_combination ((t : ℂ)^2-τ*t)*(h u)

private lemma null_roots_unique (a r : ℝ) (v w z x y s : ℂ) (hxy : x ≠ y)
    (hxs : x ≠ s)
    (hx : (v-x)^2-4*(w-((r : ℂ)*x+z))*(a : ℂ)=0)
    (hy : (v-y)^2-4*(w-((r : ℂ)*y+z))*(a : ℂ)=0)
    (hs : (v-s)^2-4*(w-((r : ℂ)*s+z))*(a : ℂ)=0) : y = s := by
  have h1 : (x-y)*(x+y-2*v+4*(a : ℂ)*r)=0 := by linear_combination hx-hy
  have h2 : (x-s)*(x+s-2*v+4*(a : ℂ)*r)=0 := by linear_combination hx-hs
  have h1' := (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hxy)
  have h2' := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hxs)
  linear_combination h1'-h2'

private lemma four_two_horizontal (A B : Fin 4 → Prop)
    (h : ∀ i, A i ∨ B i)
    (ha : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬(A i ∧ A j ∧ A k)) :
    ∃ i j, i ≠ j ∧ B i ∧ B j := by
  by_contra hn
  have hb (i j : Fin 4) (hij : i ≠ j) : ¬(B i ∧ B j) := by
    rintro ⟨hi,hj⟩
    exact hn ⟨i,j,hij,hi,hj⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have ha012 := ha 0 1 2 (by decide) (by decide) (by decide)
  have ha013 := ha 0 1 3 (by decide) (by decide) (by decide)
  have ha023 := ha 0 2 3 (by decide) (by decide) (by decide)
  have ha123 := ha 1 2 3 (by decide) (by decide) (by decide)
  have hb01 := hb 0 1 (by decide)
  have hb02 := hb 0 2 (by decide)
  have hb03 := hb 0 3 (by decide)
  have hb12 := hb 1 2 (by decide)
  have hb13 := hb 1 3 (by decide)
  have hb23 := hb 2 3 (by decide)
  clear h ha hb hn
  grind

/-- Four homothetically separating points cannot all have polynomial-square
distances to an anchor at a different initial position without a fixed
collinear triple. This allows arbitrary anchor velocity and acceleration. -/
lemma four_point_split_obstruction (a r : ℝ) (z v w : ℂ) (b : Fin 4 → ℂ)
    (ha : a ≠ 0) (hb : Function.Injective b)
    (hsq : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial a (v-b i) (w-((r : ℂ)*b i+z))))) :
    ∃ i j, i ≠ j ∧ ∀ t : ℝ,
      cross (motion a v w t-motion 0 (b i) ((r : ℂ)*b i+z) t)
        (motion a v w t-motion 0 (b j) ((r : ℂ)*b j+z) t)=0 := by
  let A : Fin 4 → Prop := fun i =>
    (v-b i)^2-4*(w-((r : ℂ)*b i+z))*(a : ℂ)=0
  let B : Fin 4 → Prop := fun i =>
    (v-b i).im=0 ∧ (w-((r : ℂ)*b i+z)).im=0
  have h : ∀ i, A i ∨ B i := fun i => quadratic_type_ratFunc _ _ _ ha (hsq i)
  have hn : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬(A i ∧ A j ∧ A k) := by
    rintro i j k hij hik hjk ⟨hi,hj,hk⟩
    exact hjk (hb (null_roots_unique a r v w z (b i) (b j) (b k)
      (hb.ne hij) (hb.ne hik) hi hj hk))
  obtain ⟨i,j,hij,hi,hj⟩ := four_two_horizontal A B h hn
  refine ⟨i,j,hij,?_⟩
  intro t
  have him (u : Fin 4) (hu : B u) :
      (motion a v w t-motion 0 (b u) ((r : ℂ)*b u+z) t).im=0 := by
    have he : motion a v w t-motion 0 (b u) ((r : ℂ)*b u+z) t =
        motion a (v-b u) (w-((r : ℂ)*b u+z)) t := by
      simp only [motion, Complex.ofReal_zero]
      ring
    rw [he]
    simp [motion, pow_two, Complex.mul_im, hu.1, hu.2]
  simp [cross, him i hi, him j hj]

/-- A four-point collision cluster with a noncollinear velocity triangle
cannot grow a GP configuration while retaining an exterior initial anchor. -/
lemma collision_cluster_four (a : ℝ) (b c : Fin 4 → ℂ) (v w : ℂ)
    (ha : a ≠ 0) (hb : Function.Injective b)
    (hn : cross (b 1-b 0) (b 2-b 0) ≠ 0)
    (hin : ∀ i j, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial 0 (b j-b i) (c j-c i))))
    (hout : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial a (v-b i) (w-c i)))) :
    ∃ i j, i ≠ j ∧ ∀ t : ℝ,
      cross (motion a v w t-motion 0 (b i) (c i) t)
        (motion a v w t-motion 0 (b j) (c j) t)=0 := by
  obtain ⟨r,z,h⟩ := parallel_redrawing b c 0 1 2 hn
    (fun i j => collision_type _ _ (hin i j))
  have hs : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial a (v-b i) (w-((r : ℂ)*b i+z)))) := by
    intro i
    simpa only [← h i] using hout i
  obtain ⟨i,j,hij,hij'⟩ := four_point_split_obstruction a r z v w b ha hb hs
  refine ⟨i,j,hij,?_⟩
  intro t
  simpa only [← h i, ← h j] using hij' t

/-- A sharp size control: three points may split from zero while one starts
elsewhere. At time one the four points are the GP diamond `(3, ±4i, -3)`. -/
def splitA : Fin 4 → ℝ := ![0,0,0,1]
def splitB : Fin 4 → ℂ := ![3,4*Complex.I,-4*Complex.I,0]
def splitC : Fin 4 → ℂ := ![0,0,0,-4]
def splitD0 : Fin 4 → Fin 4 → ℝ :=
  !![0,0,0,1; 0,0,0,1; 0,0,0,1; 1,1,1,0]
def splitD1 : Fin 4 → Fin 4 → ℝ :=
  !![0,5,5,-3; 5,0,8,0; 5,8,0,0; -3,0,0,0]
def splitD2 : Fin 4 → Fin 4 → ℝ :=
  !![0,0,0,-4; 0,0,0,4; 0,0,0,4; -4,4,4,0]

lemma split_control_squares (i j : Fin 4) :
    normPolynomial (splitA j-splitA i) (splitB j-splitB i) (splitC j-splitC i) =
      (C (splitD0 i j)+C (splitD1 i j)*X+C (splitD2 i j)*X^2)^2 := by
  apply Polynomial.funext
  intro t
  fin_cases i <;> fin_cases j <;>
    norm_num [normPolynomial, quad, splitA, splitB, splitC,
      splitD0, splitD1, splitD2, Matrix.cons_val, pow_two,
      Complex.mul_re, Complex.mul_im] <;> ring

lemma split_control_triangle (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    cross (motion (splitA j) (splitB j) (splitC j) 1-
      motion (splitA i) (splitB i) (splitC i) 1)
      (motion (splitA k) (splitB k) (splitC k) 1-
        motion (splitA i) (splitB i) (splitC i) 1) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [splitA,splitB,splitC,motion,cross,Matrix.cons_val,
      Complex.mul_re,Complex.mul_im] at *

lemma split_control_not_cospherical :
    ¬ EuclideanGeometry.Cospherical
      (Set.range (fun i : Fin 4 => motion (splitA i) (splitB i) (splitC i) 1)) := by
  rintro ⟨o,r,h⟩
  have h0 := congrArg (fun x : ℝ => x^2) (h _ ⟨(0 : Fin 4),rfl⟩)
  have h1 := congrArg (fun x : ℝ => x^2) (h _ ⟨(1 : Fin 4),rfl⟩)
  have h2 := congrArg (fun x : ℝ => x^2) (h _ ⟨(2 : Fin 4),rfl⟩)
  have h3 := congrArg (fun x : ℝ => x^2) (h _ ⟨(3 : Fin 4),rfl⟩)
  norm_num [splitA,splitB,splitC,motion,Matrix.cons_val,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,dist_eq_norm,
    Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
      at h0 h1 h2 h3
  have hre : o.re=0 := by nlinarith [h0,h3]
  have him : o.im=0 := by nlinarith [h1,h2]
  simp only [hre,him] at h0 h1
  nlinarith

#print axioms split_control_not_cospherical
#print axioms collision_type
#print axioms parallel_redrawing
#print axioms total_collision_homothety
#print axioms total_collision_homothety_at
#print axioms four_point_split_obstruction
#print axioms collision_cluster_four
#print axioms split_control_squares
#print axioms split_control_triangle
end
end Erdos213.QuadraticMotion
