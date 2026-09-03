import Submission.QuadraticMotion
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! Independent double-pole motions. Universal square identities force
these motions onto a line or circle. This is not an obstruction at an
isolated parameter value, nor a settlement of Erdős 213. -/
namespace Erdos213.DoublePoleMotion
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000

def pairNorm (a b c d : ℝ) : ℝ[X] :=
  (C (a-c)+C (c*b^2-a*d^2)*X^2)^2+(C (-2*(a*d-c*b))*X)^2

def denominator (b : ℝ) : ℝ[X] := 1+C (b^2)*X^2

def squaredChord (a b c d : ℝ) : RatFunc ℝ :=
  algebraMap ℝ[X] (RatFunc ℝ) (pairNorm a b c d) /
    (algebraMap ℝ[X] (RatFunc ℝ) (denominator b*denominator d))^2

lemma denominator_ne (b : ℝ) : denominator b ≠ 0 := by
  intro h
  have hh := congrArg (Polynomial.eval 0) h
  norm_num [denominator] at hh

lemma chord_square_iff_numerator (a b c d : ℝ) :
    IsSquare (squaredChord a b c d) ↔
      IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (pairNorm a b c d)) := by
  have hden : algebraMap ℝ[X] (RatFunc ℝ) (denominator b*denominator d) ≠ 0 := by
    intro h
    apply mul_ne_zero (denominator_ne b) (denominator_ne d)
    apply IsFractionRing.injective ℝ[X] (RatFunc ℝ)
    simpa using h
  unfold squaredChord
  constructor
  · intro h
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 hden)] using h.mul (IsSquare.sq
      (algebraMap ℝ[X] (RatFunc ℝ) (denominator b*denominator d)))
  · intro h
    exact h.div (IsSquare.sq _)

lemma pairNorm_as_quadratic (a b c d : ℝ) :
    pairNorm a b c d = QuadraticMotion.normPolynomial (a-c)
      ⟨0,-2*(a*d-c*b)⟩ ⟨c*b^2-a*d^2,0⟩ := by
  simp only [pairNorm,QuadraticMotion.normPolynomial,CircleLineRigidity.quad]
  simp
  ring

/-- Complete classification for one pair with distinct, nonzero initial
positions. The two alternatives are equal poles or equal radial-to-pole
ratios, expressed without division. -/
theorem pair_square_iff (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (hac : a ≠ c) :
    IsSquare (squaredChord a b c d) ↔ b=d ∨ a*d=c*b := by
  rw [chord_square_iff_numerator]
  constructor
  · intro h
    rw [pairNorm_as_quadratic] at h
    obtain h | h := QuadraticMotion.quadratic_type_ratFunc (a-c)
      ⟨0,-2*(a*d-c*b)⟩ ⟨c*b^2-a*d^2,0⟩ (sub_ne_zero.mpr hac) h
    · left
      have he := congrArg Complex.re h
      simp [pow_two,Complex.mul_re,Complex.mul_im] at he
      have hz : (4*a*c)*(b-d)^2=0 := by
        nlinarith only [he]
      have hz' := (mul_eq_zero.mp hz).resolve_left
        (mul_ne_zero (mul_ne_zero (by norm_num) ha) hc)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz')
    · right
      have hh := h.1
      change -2*(a*d-c*b)=0 at hh
      linarith
  · rintro (rfl | h)
    · have hid : pairNorm a b c b =
          (C (a-c)*(1+C (b^2)*X^2))^2 := by
        apply Polynomial.funext
        intro t
        simp only [pairNorm,eval_add,eval_pow,eval_mul,eval_C,eval_X,eval_one]
        ring
      rw [hid,map_pow]
      exact IsSquare.sq _
    · have hid : pairNorm a b c d = (C (a-c)+C (c*b^2-a*d^2)*X^2)^2 := by
        simp [pairNorm,h]
      rw [hid,map_pow]
      exact IsSquare.sq _

/-- Pairwise compatibility of two equivalence relations forces one relation
to hold globally. No finite-cardinality hypothesis is used. -/
lemma global_compatibility {ι : Type*} [Nonempty ι] (a b : ι → ℝ)
    (ha : ∀ i, a i ≠ 0)
    (h : ∀ i j, b i=b j ∨ a i*b j=a j*b i) :
    (∃ B, ∀ i, b i=B) ∨ (∃ K, ∀ i, b i=K*a i) := by
  classical
  by_cases hb : ∀ i j, b i=b j
  · left
    let i := Classical.choice (inferInstance : Nonempty ι)
    exact ⟨b i,fun j => hb j i⟩
  · push_neg at hb
    obtain ⟨i,j,hij⟩ := hb
    have hrat := (h i j).resolve_left hij
    have hall (k) : a i*b k=a k*b i := by
      obtain hik | hik := h i k
      · obtain hjk | hjk := h j k
        · exact False.elim (hij (hik.trans hjk.symm))
        · have hz : a j*(a i*b k-a k*b i)=0 := by
            linear_combination a i*hjk+a k*hrat
          exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ha j))
      · exact hik
    right
    refine ⟨b i/a i,?_⟩
    intro k
    have hai := ha i
    field_simp
    linear_combination hall k

/-- Real coordinates of a/(1-i*b*t)^2. Its distance to zero is
|a|/(1+b^2*t^2). -/
def point (a b t : ℝ) : ℂ :=
  ⟨a*(1-b^2*t^2)/(1+b^2*t^2)^2,2*a*b*t/(1+b^2*t^2)^2⟩

lemma den_pos (b t : ℝ) : 0 < 1+b^2*t^2 := by positivity

lemma point_dist_sq (a b c d t : ℝ) :
    dist (point a b t) (point c d t)^2 =
      (pairNorm a b c d).eval t / ((1+b^2*t^2)*(1+d^2*t^2))^2 := by
  have hb := ne_of_gt (den_pos b t)
  have hd := ne_of_gt (den_pos d t)
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp only [point,Complex.sub_re,Complex.sub_im,pairNorm,eval_add,eval_pow,
    eval_mul,eval_C,eval_X]
  field_simp
  ring

lemma common_pole_collinear {ι : Type*} (a : ι → ℝ) (B t : ℝ) :
    Collinear ℝ (Set.range (fun i => point (a i) B t)) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(0 : ℂ),point 1 B t,?_⟩
  rintro _ ⟨i,rfl⟩
  refine ⟨a i,?_⟩
  apply Complex.ext <;> simp [point] <;> ring

lemma proportional_zero (a K t : ℝ) (h : K*t=0) : point a (K*a) t = (a : ℂ) := by
  rcases mul_eq_zero.mp h with rfl | rfl <;> apply Complex.ext <;> simp [point]

lemma proportional_circle_sq (a K t : ℝ) (h : K*t ≠ 0) :
    dist (point a (K*a) t) (⟨0,1/(4*K*t)⟩ : ℂ)^2 = (1/(4*K*t))^2 := by
  have hK : K ≠ 0 := left_ne_zero_of_mul h
  have ht : t ≠ 0 := right_ne_zero_of_mul h
  have hd := ne_of_gt (den_pos (K*a) t)
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp only [point,Complex.sub_re,Complex.sub_im,sub_zero]
  field_simp
  ring

lemma proportional_line_or_circle {ι : Type*} (a : ι → ℝ) (K t : ℝ) :
    Collinear ℝ (Set.range (fun i => point (a i) (K*a i) t)) ∨
      EuclideanGeometry.Cospherical (Set.range (fun i => point (a i) (K*a i) t)) := by
  by_cases h : K*t=0
  · left
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨(0 : ℂ),(1 : ℂ),?_⟩
    rintro _ ⟨i,rfl⟩
    refine ⟨a i,?_⟩
    simp [proportional_zero _ _ _ h]
  · right
    refine ⟨(⟨0,1/(4*K*t)⟩ : ℂ),|1/(4*K*t)|,?_⟩
    rintro _ ⟨i,rfl⟩
    apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
    rw [sq_abs,proportional_circle_sq _ _ _ h]

/-- A complete universal-identity obstruction for this independent-pole
ansatz. It says nothing about square values at a single parameter. -/
theorem motions_line_or_circle {ι : Type*} [Nonempty ι] (a b : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (hsq : ∀ i j, IsSquare (squaredChord (a i) (b i) (a j) (b j))) (t : ℝ) :
    Collinear ℝ (Set.range (fun i => point (a i) (b i) t)) ∨
      EuclideanGeometry.Cospherical (Set.range (fun i => point (a i) (b i) t)) := by
  have hpair (i j) : b i=b j ∨ a i*b j=a j*b i := by
    by_cases h : i=j
    · exact Or.inl (congrArg b h)
    · exact (pair_square_iff _ _ _ _ (ha i) (ha j) (hinj.ne h)).mp (hsq i j)
  obtain ⟨B,hB⟩ | ⟨K,hK⟩ := global_compatibility a b ha hpair
  · left
    simp_rw [hB]
    exact common_pole_collinear a B t
  · simp_rw [hK]
    exact proportional_line_or_circle a K t

#print axioms pair_square_iff
#print axioms global_compatibility
#print axioms point_dist_sq
#print axioms motions_line_or_circle
end
end Erdos213.DoublePoleMotion
