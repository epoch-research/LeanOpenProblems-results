import Submission.DoublePoleMotion

/-! The double-pole ansatz is flexible at one parameter value. This file
exhibits a GP four-point specialization with integer distances although
its nonanchor distance functions are not squares in R(t). -/
namespace Erdos213.DoublePoleMotion
noncomputable section
set_option maxHeartbeats 3000000

/-- Every point with a specified radius is represented at t=1, except
for the usual excluded endpoint of the rational circle parametrization. -/
lemma inverse_at_one (x y r : ℝ) (h : r^2=x^2+y^2) (hd : r+x ≠ 0) :
    point (2*r^2/(r+x)) (y/(r+x)) 1 = (⟨x,y⟩ : ℂ) := by
  have hr : r ≠ 0 := by
    intro hr
    rw [hr] at h
    have hx : x=0 := by nlinarith [sq_nonneg y]
    exact hd (by rw [hr,hx]; ring)
  have hp : 1+(y/(r+x))^2 = 2*r/(r+x) := by
    field_simp
    nlinarith only [h]
  have hm : 1-(y/(r+x))^2 = 2*x/(r+x) := by
    field_simp
    nlinarith only [h]
  apply Complex.ext
  · change (2*r^2/(r+x))*(1-(y/(r+x))^2*1^2)/(1+(y/(r+x))^2*1^2)^2=x
    simp only [one_pow,mul_one,hp,hm]
    field_simp
  · change 2*(2*r^2/(r+x))*(y/(r+x))*1/(1+(y/(r+x))^2*1^2)^2=y
    simp only [one_pow,mul_one,hp]
    field_simp


/-- Rational coordinates and a rational radius give rational parameters.
Thus the obstruction above concerns identities, not representability of
individual rational-distance configurations at a fixed time. -/
lemma rational_inverse_at_one (x y r : ℚ) (h : r^2=x^2+y^2) (hd : r+x ≠ 0) :
    ∃ a b : ℚ, point (a : ℝ) (b : ℝ) 1 = (⟨(x : ℝ),(y : ℝ)⟩ : ℂ) := by
  refine ⟨2*r^2/(r+x),y/(r+x),?_⟩
  have hR : (r : ℝ)^2=(x : ℝ)^2+(y : ℝ)^2 := by exact_mod_cast h
  have hdR : (r : ℝ)+(x : ℝ) ≠ 0 := by exact_mod_cast hd
  convert inverse_at_one (x : ℝ) (y : ℝ) (r : ℝ) hR hdR using 1
  push_cast
  rfl

namespace Control

def a : Fin 4 → ℝ := ![0,45,250/9,10]
def b : Fin 4 → ℝ := ![0,-2,4/3,0]
def p (i : Fin 4) : ℂ := point (a i) (b i) 1
def length : Fin 4 → Fin 4 → ℕ :=
  !![0,9,10,10; 9,0,17,17; 10,17,0,16; 10,17,16,0]

lemma distances (i j : Fin 4) : dist (p i) (p j)=(length i j : ℝ) := by
  have hh : dist (p i) (p j)^2=(length i j : ℝ)^2 := by
    unfold p
    rw [point_dist_sq]
    fin_cases i <;> fin_cases j <;> norm_num [a,b,length,pairNorm]
  nlinarith only [hh,dist_nonneg (x := p i) (y := p j),
    Nat.cast_nonneg (α := ℝ) (length i j)]

private lemma complex_dist_sq (z w : ℂ) :
    dist z w^2=(z.re-w.re)^2+(z.im-w.im)^2 := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im]
  ring

private lemma collinear_cross_zero {z w u : ℂ} (h : Collinear ℝ {z,w,u}) :
    QuadraticMotion.cross (w-z) (u-z)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : z ∈ ({z,w,u} : Set ℂ))).mp h
  obtain ⟨r,hr⟩ := hv w (by simp)
  obtain ⟨s,hs⟩ := hv u (by simp)
  subst w u
  simp [QuadraticMotion.cross]
  ring

lemma no_collinear_triples (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Collinear ℝ {p i,p j,p k} := by
  intro h
  have hh := collinear_cross_zero h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals norm_num [p,a,b,point,QuadraticMotion.cross] at hh

lemma not_cospherical : ¬ EuclideanGeometry.Cospherical (Set.range p) := by
  rintro ⟨o,r,h⟩
  have h0 := congrArg (fun x : ℝ => x^2) (h (p 0) ⟨0,rfl⟩)
  have h1 := congrArg (fun x : ℝ => x^2) (h (p 1) ⟨1,rfl⟩)
  have h2 := congrArg (fun x : ℝ => x^2) (h (p 2) ⟨2,rfl⟩)
  have h3 := congrArg (fun x : ℝ => x^2) (h (p 3) ⟨3,rfl⟩)
  simp only [complex_dist_sq] at h0 h1 h2 h3
  norm_num [p,a,b,point,Matrix.cons_val_two,Matrix.cons_val_three] at h0 h1 h2 h3
  nlinarith

/-- All six distances at t=1 are integers, but even the 1--2 edge
fails to be a square rational function. -/
lemma not_universal_square : ¬ IsSquare (squaredChord (a 1) (b 1) (a 2) (b 2)) := by
  rw [pair_square_iff _ _ _ _ (by norm_num [a,Matrix.cons_val_two,Matrix.cons_val_three]) (by norm_num [a,Matrix.cons_val_two,Matrix.cons_val_three]) (by norm_num [a,Matrix.cons_val_two,Matrix.cons_val_three])]
  norm_num [a,b,Matrix.cons_val_two,Matrix.cons_val_three]

#print axioms distances
#print axioms no_collinear_triples
#print axioms not_cospherical
#print axioms not_universal_square
end Control
#print axioms inverse_at_one
#print axioms rational_inverse_at_one
end
end Erdos213.DoublePoleMotion
