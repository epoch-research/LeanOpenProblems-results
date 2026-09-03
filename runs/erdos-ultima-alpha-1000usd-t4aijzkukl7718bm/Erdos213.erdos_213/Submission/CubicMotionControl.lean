import FormalConjecturesUtil

/-! A noncollinear cubic-motion triangle starting at three distinct real
positions with distinct vertical velocities. It shows that the earlier
quadratic three-velocity rigidity does not extend to cubics. It is not a
cardinality-growth construction or a settlement of Erdős 213. -/
namespace Erdos213.CubicMotionControl
noncomputable section

def px {R : Type*} [CommRing R] (t : R) : Fin 3 → R :=
  ![0,-875+2575*t-1505*t^2+165*t^3,125-25*t-745*t^2+429*t^3]

def py {R : Type*} [CommRing R] (t : R) : Fin 3 → R :=
  ![0,1400*t-2160*t^2+280*t^3,600*t-240*t^2-72*t^3]

def length {R : Type*} [CommRing R] (t : R) : Fin 3 → Fin 3 → R :=
  !![0,25*(t-7)*(5-14*t+13*t^2),5*(5-3*t)*(5+2*t+29*t^2);
     25*(t-7)*(5-14*t+13*t^2),0,40*(11*t-5)*(5-2*t+t^2);
     5*(5-3*t)*(5+2*t+29*t^2),40*(11*t-5)*(5-2*t+t^2),0]

/-- All three edge-square identities hold over every commutative ring. -/
theorem squared_lengths {R : Type*} [CommRing R] (t : R) (i j : Fin 3) :
    (px t i-px t j)^2+(py t i-py t j)^2=length t i j^2 := by
  fin_cases i <;> fin_cases j <;> simp [px,py,length] <;> ring

/-- The signed area determinant is not the zero polynomial. -/
theorem area_factorization {R : Type*} [CommRing R] (t : R) :
    px t 1*py t 2-py t 1*px t 2 =
      -4000*t*(t-7)*(t-1)*(t+1)*(3*t-5)*(11*t-5) := by
  simp [px,py]
  ring

def point (t : ℝ) (i : Fin 3) : ℂ := ⟨px t i,py t i⟩

theorem distance_eq (t : ℝ) (i j : Fin 3) :
    dist (point t i) (point t j)=|length t i j| := by
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  rw [sq_abs,dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simpa [point, Complex.sub_re, Complex.sub_im, pow_two] using squared_lengths t i j

theorem rational_distances (t : ℚ) (i j : Fin 3) :
    dist (point t i) (point t j)∈Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨|length t i j|,?_⟩
  rw [distance_eq,Rat.cast_abs]
  congr 1
  fin_cases i <;> fin_cases j <;> norm_num [length]

lemma initial_positions_distinct : Function.Injective (px (0 : ℝ)) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [px, Matrix.cons_val_succ] at he

lemma initial_vertical_zero (i : Fin 3) : py (0 : ℝ) i=0 := by
  fin_cases i <;> norm_num [py]

def verticalVelocity : Fin 3 → ℤ := ![0,1400,600]

lemma vertical_velocity_distinct : Function.Injective verticalVelocity := by decide

lemma vertical_velocity_coefficient (i : Fin 3) :
    (py (Polynomial.X : Polynomial ℤ) i).coeff 1=verticalVelocity i := by
  fin_cases i <;> norm_num [py,verticalVelocity, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_mul, Polynomial.coeff_X_pow, Matrix.cons_val_succ]

private lemma collinear_det_zero {a b c : ℂ} (h : Collinear ℝ {a,b,c}) :
    (b.re-a.re)*(c.im-a.im)-(b.im-a.im)*(c.re-a.re)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a∈({a,b,c} : Set ℂ))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp [Complex.real_smul,Complex.mul_re,Complex.mul_im]
  ring

theorem noncollinear_at_two : ¬Collinear ℝ {point 2 0,point 2 1,point 2 2} := by
  intro h
  have he := collinear_det_zero h
  change ((-875+2575*2-1505*2^2+165*2^3 : ℝ)-0) *
      ((600*2-240*2^2-72*2^3)-0) -
      ((1400*2-2160*2^2+280*2^3)-0) *
      ((125-25*2-745*2^2+429*2^3)-0) = 0 at he
  norm_num at he

#print axioms squared_lengths
#print axioms rational_distances
#print axioms initial_positions_distinct
#print axioms vertical_velocity_coefficient
#print axioms noncollinear_at_two
end
end Erdos213.CubicMotionControl
