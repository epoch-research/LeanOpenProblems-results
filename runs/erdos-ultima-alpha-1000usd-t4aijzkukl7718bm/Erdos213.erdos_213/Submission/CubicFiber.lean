import FormalConjecturesUtil

/-! A rational-distance construction from a cubic fiber.
This file does not assert that a sufficiently large general-position fiber exists. -/

open EuclideanGeometry

set_option maxHeartbeats 2000000
namespace Erdos213.CubicFiber

variable {R : Type*} [CommRing R]

-- Twice the two coordinates of the quadratic image; no division is needed.
def imageX (a c x y : R) : R := y^2-x^2-4*a*y+4*c*x
def imageY (b d x y : R) : R := -2*x*y-2*b*y+2*d*x

def fiberX (a b k x y : R) : R :=
  x*(x^2+y^2)-2*a*(x^2-y^2)-2*b*x*y-2*k*x-(b^2+4*a^2)*y

def fiberY (a b c d k x y : R) : R :=
  y*(x^2+y^2)-2*c*(x^2-y^2)-2*d*x*y+(d^2+4*c^2)*x-
    2*(k+4*a*c+b*d)*y

-- Twice the signed distance of the unscaled quadratic image.
def signedChord (x y u v : R) : R :=
  u^2+v^2-x^2-y^2+2*x*v-2*y*u

lemma distance_identity (a b c d k x y u v : R) :
    (imageX a c x y-imageX a c u v)^2+
      (imageY b d x y-imageY b d u v)^2 =
    signedChord x y u v ^ 2+
      4*(x-u)*(fiberY a b c d k x y-fiberY a b c d k u v)-
      4*(y-v)*(fiberX a b k x y-fiberX a b k u v) := by
  dsimp [imageX,imageY,fiberX,fiberY,signedChord]
  ring

lemma same_fiber_distance_sq (a b c d k x y u v : R)
    (hX : fiberX a b k x y = fiberX a b k u v)
    (hY : fiberY a b c d k x y = fiberY a b c d k u v) :
    (imageX a c x y-imageX a c u v)^2+
      (imageY b d x y-imageY b d u v)^2 = signedChord x y u v ^ 2 := by
  rw [distance_identity a b c d k, hX, hY]
  ring

noncomputable def point (a b c d x y : ℚ) : ℝ² :=
  !₂[((imageX a c x y : ℚ) : ℝ), ((imageY b d x y : ℚ) : ℝ)]

lemma point_dist (a b c d k x y u v : ℚ)
    (hX : fiberX a b k x y = fiberX a b k u v)
    (hY : fiberY a b c d k x y = fiberY a b c d k u v) :
    dist (point a b c d x y) (point a b c d u v) = |((signedChord x y u v : ℚ) : ℝ)| := by
  have hid := same_fiber_distance_sq a b c d k x y u v hX hY
  have hd : dist (point a b c d x y) (point a b c d u v)^2 =
      ((signedChord x y u v : ℚ) : ℝ)^2 := by
    simp only [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq,point,
      Matrix.cons_val_zero,Matrix.cons_val_one,sq_abs]
    exact_mod_cast hid
  exact (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp (by simpa only [sq_abs] using hd)

lemma point_rational_distance (a b c d k x y u v : ℚ)
    (hX : fiberX a b k x y = fiberX a b k u v)
    (hY : fiberY a b c d k x y = fiberY a b c d k u v) :
    dist (point a b c d x y) (point a b c d u v) ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨|signedChord x y u v|,?_⟩
  rw [Rat.cast_abs,point_dist a b c d k x y u v hX hY]

lemma fiber_pairwise_rational {ι : Type*} (a b c d k r s : ℚ)
    (x y : ι → ℚ)
    (hX : ∀ i, fiberX a b k (x i) (y i) = r)
    (hY : ∀ i, fiberY a b c d k (x i) (y i) = s) :
    (Set.range fun i => point a b c d (x i) (y i)).Pairwise
      (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
  exact point_rational_distance a b c d k (x i) (y i) (x j) (y j)
    ((hX i).trans (hX j).symm) ((hY i).trans (hY j).symm)

/-- A tempting symmetric subfamily has a reducible fiber. -/
lemma symmetric_factorization (u x y : ℚ) :
    let m : ℚ := (u^2+4)/2
    let k : ℚ := m*(m-2)/2
    fiberY 1 u 1 u k x y-fiberX 1 u k x y =
      (y-x)*(x^2+y^2-m^2) := by
  dsimp [fiberX,fiberY]
  ring

lemma symmetric_zero_fiber_split (u x y : ℚ)
    (hX : fiberX 1 u (((u^2+4)/2)*((u^2+4)/2-2)/2) x y = 0)
    (hY : fiberY 1 u 1 u (((u^2+4)/2)*((u^2+4)/2-2)/2) x y = 0) :
    y = x ∨ x^2+y^2 = ((u^2+4)/2)^2 := by
  have h := symmetric_factorization u x y
  dsimp only at h
  rw [hX,hY,sub_zero] at h
  rcases mul_eq_zero.mp h.symm with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- All images of the diagonal branch lie on one line, independently of
which fiber is being considered. They cannot supply three general-position points. -/
lemma diagonal_image_collinear (a b : ℚ) :
    Collinear ℝ (Set.range fun x : ℚ => point a b a b x x) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨0, !₂[(0 : ℝ),1], ?_⟩
  rintro _ ⟨x,rfl⟩
  refine ⟨(-2 : ℝ)*(x : ℝ)^2, ?_⟩
  ext i
  fin_cases i <;> simp [point,imageX,imageY] <;> ring

#print axioms distance_identity
#print axioms point_dist
#print axioms fiber_pairwise_rational
#print axioms symmetric_zero_fiber_split
#print axioms diagonal_image_collinear

end Erdos213.CubicFiber
