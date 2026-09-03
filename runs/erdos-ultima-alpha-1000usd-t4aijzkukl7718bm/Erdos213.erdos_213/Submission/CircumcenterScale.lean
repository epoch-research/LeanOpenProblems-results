import FormalConjecturesUtil

/-! The scaled shared-edge circumcenter identity. This gives no global
cardinality bound and no general-position growth theorem. -/
namespace Erdos213.CircumcenterScale
noncomputable section

lemma lagrange_identity {R : Type*} [CommRing R] (D u v s t : R) :
    (u^2+D*v^2)*(s^2+D*t^2) = (u*s+D*v*t)^2+D*(u*t-v*s)^2 := by ring

lemma orthogonal_scaled_isSquare (D u v s t r : ℚ) (hr : r ≠ 0)
    (hn : u^2+D*v^2 = r^2) (ho : u*s+D*v*t = 0) :
    IsSquare (D*(s^2+D*t^2)) := by
  refine ⟨D*(u*t-v*s)/r, ?_⟩
  have he := lagrange_identity D u v s t
  rw [hn,ho] at he
  field_simp
  linear_combination D*he

lemma shared_bisectors_isSquare (D ax ay bx by_ ox oy px py r : ℚ)
    (hr : r ≠ 0) (hedge : (bx-ax)^2+D*(by_-ay)^2 = r^2)
    (ho : (ox-ax)^2+D*(oy-ay)^2 = (ox-bx)^2+D*(oy-by_)^2)
    (hp : (px-ax)^2+D*(py-ay)^2 = (px-bx)^2+D*(py-by_)^2) :
    IsSquare (D*((ox-px)^2+D*(oy-py)^2)) := by
  apply orthogonal_scaled_isSquare D (bx-ax) (by_-ay) (ox-px) (oy-py) r hr hedge
  linear_combination ho/2-hp/2

def point (D : ℕ) (x y : ℚ) : ℂ :=
  (x : ℂ)+(y : ℂ)*(Real.sqrt D : ℂ)*Complex.I

def scaledPoint (D : ℕ) (x y : ℚ) : ℂ := point D (-(D : ℚ)*y) x

lemma point_sub (D : ℕ) (x y x' y' : ℚ) :
    point D x y-point D x' y' = point D (x-x') (y-y') := by
  simp [point]
  ring

lemma normSq_point (D : ℕ) (x y : ℚ) :
    Complex.normSq (point D x y) = ((x^2+(D : ℚ)*y^2 : ℚ) : ℝ) := by
  simp only [point,Complex.normSq_apply]
  simp
  nlinarith [Real.sq_sqrt (show 0 ≤ (D : ℝ) by positivity)]

lemma scaled_normSq_sub (D : ℕ) (x y x' y' : ℚ) :
    Complex.normSq (scaledPoint D x y-scaledPoint D x' y') =
      (((D : ℚ)*((x-x')^2+(D : ℚ)*(y-y')^2) : ℚ) : ℝ) := by
  rw [scaledPoint,scaledPoint,point_sub,normSq_point]
  push_cast
  ring

lemma rational_norm_of_square {z : ℂ} {q : ℚ}
    (hz : Complex.normSq z = (q : ℝ)) (hq : IsSquare q) :
    ‖z‖ ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := hq
  refine ⟨|r|, ?_⟩
  rw [Complex.normSq_eq_norm_sq,hr] at hz
  push_cast at hz ⊢
  nlinarith [norm_nonneg z,abs_nonneg (r : ℝ),sq_abs (r : ℝ)]

/-- Two rational-coordinate centers on the same perpendicular bisector have
rational mutual distance after a common rotation/dilation by sqrt(-D), provided
the shared chord has nonzero rational length. -/
lemma shared_bisectors_rational_distance (D : ℕ) (ax ay bx by_ ox oy px py r : ℚ)
    (hr : r ≠ 0) (hedge : (bx-ax)^2+(D : ℚ)*(by_-ay)^2 = r^2)
    (ho : (ox-ax)^2+(D : ℚ)*(oy-ay)^2 = (ox-bx)^2+(D : ℚ)*(oy-by_)^2)
    (hp : (px-ax)^2+(D : ℚ)*(py-ay)^2 = (px-bx)^2+(D : ℚ)*(py-by_)^2) :
    dist (scaledPoint D ox oy) (scaledPoint D px py) ∈
      Set.range ((↑) : ℚ → ℝ) := by
  rw [dist_eq_norm]
  exact rational_norm_of_square (scaled_normSq_sub D ox oy px py)
    (shared_bisectors_isSquare D ax ay bx by_ ox oy px py r hr hedge ho hp)

#print axioms orthogonal_scaled_isSquare
#print axioms shared_bisectors_rational_distance
end
end Erdos213.CircumcenterScale
