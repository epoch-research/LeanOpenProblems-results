import Submission.SquarefreeRothAlgebra

/-! Exact algebra and real cofactor bounds for four large-square witnesses.
The identities are the real/integer versions of HigherWitnessDetAlgebra.lean. -/
namespace SquarefreeFourthSign

set_option autoImplicit false

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {R : Type*} [CommRing R]

def v3 (x y z : R) : R := (y-x)*(z-x)*(z-y)
def e2 (x y z : R) : R := x*y+x*z+y*z
def e3 (x y z w : R) : R := x*y*z+x*y*w+x*z*w+y*z*w

def det4 (x y z w q₀ q₁ q₂ q₃ : R) : R :=
  -v3 y z w*q₀+v3 x z w*q₁-v3 x y w*q₂+v3 x y z*q₃

def mixedDet4 (x y z w n₀ n₁ n₂ n₃ : R) : R :=
  -v3 y z w*e2 y z w*n₀+v3 x z w*e2 x z w*n₁-
    v3 x y w*e2 x y w*n₂+v3 x y z*e2 x y z*n₃

def witnessMatrix (x y z w q₀ q₁ q₂ q₃ : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1,1,1,1; x,y,z,w; x^2,y^2,z^2,w^2; q₀,q₁,q₂,q₃]

lemma det_witnessMatrix (x y z w q₀ q₁ q₂ q₃ : R) :
    Matrix.det (witnessMatrix x y z w q₀ q₁ q₂ q₃) = det4 x y z w q₀ q₁ q₂ q₃ := by
  rw [Matrix.det_succ_row_zero]
  simp [witnessMatrix, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix, Fin.succAbove, det4, v3]
  ring

lemma det4_previous_minors (x y z w q₀ q₁ q₂ q₃ : R) :
    det4 x y z w q₀ q₁ q₂ q₃ =
    (y-x)*(z-x)*((w-z)*q₁-(w-y)*q₂+(z-y)*q₃)-
      (w-z)*(w-y)*((z-y)*q₀-(z-x)*q₁+(y-x)*q₂) := by
  dsimp [det4,v3]
  ring

lemma mixed_identity_left (x y z w q₀ q₁ q₂ q₃ : R) :
    mixedDet4 x y z w (x^2*q₀) (y^2*q₁) (z^2*q₂) (w^2*q₃) =
    ((z-y)*q₀-(z-x)*q₁+(y-x)*q₂)*(w-x)*(w-y)*(w-z)*e3 x y z w+
      det4 x y z w q₀ q₁ q₂ q₃*w^2*e2 x y z := by
  dsimp [mixedDet4,det4,v3,e2,e3]
  ring

lemma mixed_identity_right (x y z w q₀ q₁ q₂ q₃ : R) :
    mixedDet4 x y z w (x^2*q₀) (y^2*q₁) (z^2*q₂) (w^2*q₃) =
    ((w-z)*q₁-(w-y)*q₂+(z-y)*q₃)*(y-x)*(z-x)*(w-x)*e3 x y z w+
      det4 x y z w q₀ q₁ q₂ q₃*x^2*e2 y z w := by
  dsimp [mixedDet4,det4,v3,e2,e3]
  ring

lemma triple_identity (x y z q₀ q₁ q₂ : R) :
    (z-y)*(y+z)*(y^2*q₁-x^2*q₀)-
      (y-x)*(x+y)*(z^2*q₂-y^2*q₁) =
    (y-x)*(q₁-q₂)*(z-x)*e2 x y z-
      ((z-y)*q₀-(z-x)*q₁+(y-x)*q₂)*(y+z)*x^2 := by
  dsimp [e2]
  ring

lemma mixed_shift (x y z w n₀ n₁ n₂ n₃ N : R) :
    mixedDet4 x y z w n₀ n₁ n₂ n₃ =
    mixedDet4 x y z w (n₀-N) (n₁-N) (n₂-N) (n₃-N) := by
  dsimp [mixedDet4,v3,e2]
  ring

lemma cofactor_sum (x y z w : R) :
    v3 x z w + v3 x y z = (z-x)*(w-y)*(y-x+w-z) := by
  dsimp [v3]
  ring

lemma minor_gap_relation (a b c u v h : R) :
    c*(b*u-a*v)+a*(c*v-b*h) = b*(c*u-a*h) := by ring

lemma v3_pos (x y z : ℝ) (hxy : x < y) (hyz : y < z) : 0 < v3 x y z := by
  dsimp [v3]
  exact mul_pos (mul_pos (sub_pos.mpr hxy) (sub_pos.mpr (hxy.trans hyz))) (sub_pos.mpr hyz)

lemma e2_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < e2 x y z := by
  dsimp [e2]
  positivity

lemma e3_pos (x y z w : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) :
    0 < e3 x y z w := by dsimp [e3]; positivity

lemma e2_lower (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z) :
    3*x^2 ≤ e2 x y z := by
  have hy : 0 ≤ y := hx.trans hxy
  have hz : 0 ≤ z := hx.trans hxz
  have h₁ : x*x ≤ x*y := by gcongr
  have h₂ : x*x ≤ x*z := by gcongr
  have h₃ : x*x ≤ y*z := by gcongr
  dsimp [e2]
  nlinarith only [h₁, h₂, h₃]

lemma e2_strict_lower (x y z : ℝ) (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    3*x^2 < e2 x y z := by
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := hy.trans hyz
  have h₁ : x*x < x*y := by gcongr
  have h₂ : x*x ≤ x*z := by gcongr; exact (hxy.trans hyz).le
  have h₃ : x*x ≤ y*z := by
    gcongr
    linarith
  dsimp [e2]
  nlinarith only [h₁, h₂, h₃]

lemma e2_upper (x y z M : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxM : x ≤ M) (hyM : y ≤ M) (hzM : z ≤ M) : e2 x y z ≤ 3*M^2 := by
  have hM : 0 ≤ M := hx.trans hxM
  have h₁ : x*y ≤ M*M := by gcongr
  have h₂ : x*z ≤ M*M := by gcongr
  have h₃ : y*z ≤ M*M := by gcongr
  dsimp [e2]
  nlinarith only [h₁, h₂, h₃]

/-- The harmonic-mean term in the omitted-base identity is strictly greater
than `x/3`. This is proved with positive polynomial factors. -/
lemma harmonic_product_lower (x u v r : ℝ) (hx : 0 < x)
    (hu : x ≤ u) (hv : x < v) (hr : x ≤ r) : x*e2 u v r < 3*u*v*r := by
  have hu0 : 0 < u := hx.trans_le hu
  have hv0 : 0 < v := hx.trans hv
  have hr0 : 0 < r := hx.trans_le hr
  have h₁ : 0 ≤ (u-x)*v*r := mul_nonneg (mul_nonneg (by linarith) hv0.le) hr0.le
  have h₂ : 0 < u*(v-x)*r := mul_pos (mul_pos hu0 (by linarith)) hr0
  have h₃ : 0 ≤ u*v*(r-x) := mul_nonneg (mul_nonneg hu0.le hv0.le) (by linarith)
  dsimp [e2]
  nlinarith only [h₁,h₂,h₃]

lemma e3_lower_omitted_right (x y z w : ℝ) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z) (_hzw : z < w) :
    (3*w+x)*e2 x y z < 3*e3 x y z w := by
  have h := harmonic_product_lower x x y z hx le_rfl hxy (hxy.trans hyz).le
  have hid : e3 x y z w = w*e2 x y z+x*y*z := by dsimp [e3,e2]; ring
  nlinarith only [h,hid]

lemma e3_lower_omitted_middle (x y z w : ℝ) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    (3*y+x)*e2 x z w < 3*e3 x y z w := by
  have h := harmonic_product_lower x x z w hx le_rfl (hxy.trans hyz) ((hxy.trans hyz).trans hzw).le
  have hid : e3 x y z w = y*e2 x z w+x*z*w := by dsimp [e3,e2]; ring
  nlinarith only [h,hid]

lemma e3_lower_omitted_left (x y z w : ℝ) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    4*x*e2 y z w < 3*e3 x y z w := by
  have h := harmonic_product_lower x y z w hx hxy.le (hxy.trans hyz) ((hxy.trans hyz).trans hzw).le
  have hid : e3 x y z w = x*e2 y z w+y*z*w := by dsimp [e3,e2]; ring
  nlinarith only [h,hid]

/-- Only the upper cofactor bound is needed for the contradiction. -/
lemma mixed_upper (N H x y z w n₀ n₁ n₂ n₃ : ℝ)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) (hzw : z < w)
    (hn₀ : N < n₀) (hn₁ : n₁ ≤ N+H) (hn₂ : N ≤ n₂) (hn₃ : n₃ ≤ N+H) :
    mixedDet4 x y z w n₀ n₁ n₂ n₃ <
      H*(v3 x z w*e2 x z w+v3 x y z*e2 x y z) := by
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := hy.trans hyz
  have hw : 0 < w := hz.trans hzw
  let p₀ := v3 y z w*e2 y z w
  let p₁ := v3 x z w*e2 x z w
  let p₂ := v3 x y w*e2 x y w
  let p₃ := v3 x y z*e2 x y z
  have hp₀ : 0 < p₀ := mul_pos (v3_pos y z w hyz hzw) (e2_pos y z w hy hz hw)
  have hp₁ : 0 < p₁ := mul_pos (v3_pos x z w (hxy.trans hyz) hzw) (e2_pos x z w hx hz hw)
  have hp₂ : 0 < p₂ := mul_pos (v3_pos x y w hxy (hyz.trans hzw)) (e2_pos x y w hx hy hw)
  have hp₃ : 0 < p₃ := mul_pos (v3_pos x y z hxy hyz) (e2_pos x y z hx hy hz)
  have h₀ := mul_pos hp₀ (sub_pos.mpr hn₀)
  have h₁ := mul_le_mul_of_nonneg_left (show n₁-N ≤ H by linarith) hp₁.le
  have h₂ := mul_nonneg hp₂.le (show 0 ≤ n₂-N by linarith)
  have h₃ := mul_le_mul_of_nonneg_left (show n₃-N ≤ H by linarith) hp₃.le
  rw [mixed_shift x y z w n₀ n₁ n₂ n₃ N]
  simp only [mixedDet4, neg_mul]
  change -(p₀*(n₀-N))+p₁*(n₁-N)-p₂*(n₂-N)+p₃*(n₃-N) < H*(p₁+p₃)
  nlinarith only [h₀,h₁,h₂,h₃]

/-- Combining the two omitted-base bounds controls the entire positive
cofactor sum by the common cubic symmetric polynomial. -/
lemma cofactor_weight_lower (x y z w : ℝ) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    4*x*(v3 x z w*e2 x z w+v3 x y z*e2 x y z) <
      3*e3 x y z w*(v3 x z w+v3 x y z) := by
  have h₁ := e3_lower_omitted_middle x y z w hx hxy hyz hzw
  have h₂ := e3_lower_omitted_right x y z w hx hxy hyz hzw
  have hs₁ := e2_pos x z w hx (hx.trans (hxy.trans hyz)) (hx.trans ((hxy.trans hyz).trans hzw))
  have hs₂ := e2_pos x y z hx (hx.trans hxy) (hx.trans (hxy.trans hyz))
  have h₁' : 4*x*e2 x z w < 3*e3 x y z w := by
    have hm := mul_pos (show 0 < y-x by linarith) hs₁
    nlinarith only [h₁,hm]
  have h₂' : 4*x*e2 x y z < 3*e3 x y z w := by
    have hm := mul_pos (show 0 < w-x by linarith) hs₂
    nlinarith only [h₂,hm]
  have hm₁ := mul_lt_mul_of_pos_left h₁' (v3_pos x z w (hxy.trans hyz) hzw)
  have hm₂ := mul_lt_mul_of_pos_left h₂' (v3_pos x y z hxy hyz)
  nlinarith only [hm₁,hm₂]

end SquarefreeFourthSign
