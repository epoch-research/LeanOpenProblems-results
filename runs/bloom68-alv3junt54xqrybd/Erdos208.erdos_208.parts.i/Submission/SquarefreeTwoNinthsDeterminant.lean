import Submission.SquarefreeFourthSign
import Submission.SquarefreeRoth

/-!
# Safe rational D3 upper bound and integer nonzero lower bound

The cofactor formula is the supplied `SquarefreeFourthSign.det4`. The lower
bound is a consequence of its universal strict integer witness theorem, not
an extra sign hypothesis. All base geometry is arbitrary within the span.
-/
namespace SquarefreeTwoNinths

open SquarefreeFourthSign SquarefreeRoth

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The six-factor Vandermonde on four bases. -/
def v4 (x y z w : ℚ) : ℚ :=
  (y-x)*(z-x)*(w-x)*(z-y)*(w-y)*(w-z)

lemma reciprocal_det4 (x y z w : ℚ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    det4 x y z w (1/x^2) (1/y^2) (1/z^2) (1/w^2) =
      -v4 x y z w * (1/(x^2*y*z*w) + 1/(x*y^2*z*w) +
        1/(x*y*z^2*w) + 1/(x*y*z*w^2)) := by
  dsimp [det4, v3, v4]
  field_simp
  ring

lemma reciprocal_term_le (P a b c d : ℚ) (hP : 0 < P)
    (ha : P ≤ a) (hb : P ≤ b) (hc : P ≤ c) (hd : P ≤ d) :
    1/(a^2*b*c*d) ≤ 1/P^5 := by
  have ha0 : 0 < a := hP.trans_le ha
  have hb0 : 0 < b := hP.trans_le hb
  have hc0 : 0 < c := hP.trans_le hc
  have hd0 : 0 < d := hP.trans_le hd
  have hden : P^5 ≤ a^2*b*c*d := by
    calc
      P^5 = P^2*P*P*P := by ring
      _ ≤ a^2*b*c*d := by gcongr
  exact one_div_le_one_div_of_le (pow_pos hP 5) hden

lemma reciprocal_coefficient_four_le (P x y z w : ℚ) (hP : 0 < P)
    (hx : P ≤ x) (hy : P ≤ y) (hz : P ≤ z) (hw : P ≤ w) :
    1/(x^2*y*z*w) + 1/(x*y^2*z*w) + 1/(x*y*z^2*w) +
      1/(x*y*z*w^2) ≤ 4/P^5 := by
  have h₀ := reciprocal_term_le P x y z w hP hx hy hz hw
  have h₁ := reciprocal_term_le P y x z w hP hy hx hz hw
  have h₂ := reciprocal_term_le P z x y w hP hz hx hy hw
  have h₃ := reciprocal_term_le P w x y z hP hw hx hy hz
  have he₁ : y^2*x*z*w = x*y^2*z*w := by ring
  have he₂ : z^2*x*y*w = x*y*z^2*w := by ring
  have he₃ : w^2*x*y*z = x*y*z*w^2 := by ring
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [he₃] at h₃
  simp only [div_eq_mul_inv, one_mul] at h₀ h₁ h₂ h₃ ⊢
  linarith

lemma v3_span_le (a b c R : ℚ) (hab : a ≤ b) (hbc : b ≤ c)
    (hspan : c-a ≤ R) : 0 ≤ v3 a b c ∧ v3 a b c ≤ R^3 := by
  have h₀ : 0 ≤ b-a := sub_nonneg.mpr hab
  have h₁ : 0 ≤ c-a := sub_nonneg.mpr (hab.trans hbc)
  have h₂ : 0 ≤ c-b := sub_nonneg.mpr hbc
  have hR : 0 ≤ R := h₁.trans hspan
  constructor
  · dsimp [v3]; positivity
  · calc
      v3 a b c = (b-a)*(c-a)*(c-b) := rfl
      _ ≤ R*R*R := by gcongr <;> linarith
      _ = R^3 := by ring

lemma v4_span_le (x y z w R : ℚ) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) (hspan : w-x ≤ R) :
    0 ≤ v4 x y z w ∧ v4 x y z w ≤ R^6 := by
  have h₀ : 0 ≤ y-x := sub_nonneg.mpr hxy
  have h₁ : 0 ≤ z-x := sub_nonneg.mpr (hxy.trans hyz)
  have h₂ : 0 ≤ w-x := sub_nonneg.mpr ((hxy.trans hyz).trans hzw)
  have h₃ : 0 ≤ z-y := sub_nonneg.mpr hyz
  have h₄ : 0 ≤ w-y := sub_nonneg.mpr (hyz.trans hzw)
  have h₅ : 0 ≤ w-z := sub_nonneg.mpr hzw
  have hR : 0 ≤ R := h₂.trans hspan
  constructor
  · dsimp [v4]; positivity
  · calc
      v4 x y z w = (y-x)*(z-x)*(w-x)*(z-y)*(w-y)*(w-z) := rfl
      _ ≤ R*R*R*R*R*R := by gcongr <;> linarith
      _ = R^6 := by ring

/-- A safe four-cofactor amplitude bound. -/
lemma det4_amplitude_le (x y z w R A r₀ r₁ r₂ r₃ : ℚ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) (hspan : w-x ≤ R)
    (hr₀ : 0 ≤ r₀ ∧ r₀ ≤ A) (hr₁ : 0 ≤ r₁ ∧ r₁ ≤ A)
    (hr₂ : 0 ≤ r₂ ∧ r₂ ≤ A) (hr₃ : 0 ≤ r₃ ∧ r₃ ≤ A) :
    |det4 x y z w r₀ r₁ r₂ r₃| ≤ 4*R^3*A := by
  have hR : 0 ≤ R := (sub_nonneg.mpr ((hxy.trans hyz).trans hzw)).trans hspan
  have hA : 0 ≤ A := hr₀.1.trans hr₀.2
  have hc₀ := v3_span_le y z w R hyz hzw (by linarith)
  have hc₁ := v3_span_le x z w R (hxy.trans hyz) hzw hspan
  have hc₂ := v3_span_le x y w R hxy (hyz.trans hzw) hspan
  have hc₃ := v3_span_le x y z R hxy hyz (by linarith)
  have h₀ : 0 ≤ v3 y z w*r₀ ∧ v3 y z w*r₀ ≤ R^3*A :=
    ⟨mul_nonneg hc₀.1 hr₀.1, mul_le_mul hc₀.2 hr₀.2 hr₀.1 (by positivity)⟩
  have h₁ : 0 ≤ v3 x z w*r₁ ∧ v3 x z w*r₁ ≤ R^3*A :=
    ⟨mul_nonneg hc₁.1 hr₁.1, mul_le_mul hc₁.2 hr₁.2 hr₁.1 (by positivity)⟩
  have h₂ : 0 ≤ v3 x y w*r₂ ∧ v3 x y w*r₂ ≤ R^3*A :=
    ⟨mul_nonneg hc₂.1 hr₂.1, mul_le_mul hc₂.2 hr₂.2 hr₂.1 (by positivity)⟩
  have h₃ : 0 ≤ v3 x y z*r₃ ∧ v3 x y z*r₃ ≤ R^3*A :=
    ⟨mul_nonneg hc₃.1 hr₃.1, mul_le_mul hc₃.2 hr₃.2 hr₃.1 (by positivity)⟩
  dsimp [det4]
  rw [neg_mul]
  exact abs_le.mpr ⟨by nlinarith only [h₀.1,h₀.2,h₁.1,h₂.1,h₂.2,h₃.1],
    by nlinarith only [h₀.1,h₁.1,h₁.2,h₂.1,h₃.1,h₃.2]⟩

/-- The support-independent safe D3 estimate from §2.1 of the report. -/
theorem determinant_four_bound (N H P R x y z w q₀ q₁ q₂ q₃ : ℚ)
    (hN : 0 ≤ N) (_hH : 0 ≤ H) (hP : 0 < P)
    (hx : P ≤ x) (hxy : x < y) (hyz : y < z) (hzw : z < w)
    (hspan : w-x ≤ R)
    (hn₀ : N ≤ q₀*x^2) (hn₀' : q₀*x^2 ≤ N+H)
    (hn₁ : N ≤ q₁*y^2) (hn₁' : q₁*y^2 ≤ N+H)
    (hn₂ : N ≤ q₂*z^2) (hn₂' : q₂*z^2 ≤ N+H)
    (hn₃ : N ≤ q₃*w^2) (hn₃' : q₃*w^2 ≤ N+H) :
    |det4 x y z w q₀ q₁ q₂ q₃| ≤ 4*N*R^6/P^5 + 4*H*R^3/P^2 := by
  let C := 1/(x^2*y*z*w) + 1/(x*y^2*z*w) + 1/(x*y*z^2*w) + 1/(x*y*z*w^2)
  let e₀ := q₀*x^2-N
  let e₁ := q₁*y^2-N
  let e₂ := q₂*z^2-N
  let e₃ := q₃*w^2-N
  have hx0 : 0 < x := hP.trans_le hx
  have hy0 : 0 < y := hx0.trans hxy
  have hz0 : 0 < z := hy0.trans hyz
  have hw0 : 0 < w := hz0.trans hzw
  have hyP : P ≤ y := hx.trans hxy.le
  have hzP : P ≤ z := hyP.trans hyz.le
  have hwP : P ≤ w := hzP.trans hzw.le
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 4/P^5 := reciprocal_coefficient_four_le P x y z w hP hx hyP hzP hwP
  have hV := v4_span_le x y z w R hxy.le hyz.le hzw.le hspan
  have hmain : |-(N*v4 x y z w*C)| ≤ 4*N*R^6/P^5 := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hN hV.1) hC0)]
    calc
      N*v4 x y z w*C ≤ N*R^6*(4/P^5) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hV.2 hN) hC hC0 (by positivity)
      _ = 4*N*R^6/P^5 := by ring
  have he₀ := offset_div_square_le P x e₀ H hP hx
    (by dsimp [e₀]; linarith) (by dsimp [e₀]; linarith)
  have he₁ := offset_div_square_le P y e₁ H hP hyP
    (by dsimp [e₁]; linarith) (by dsimp [e₁]; linarith)
  have he₂ := offset_div_square_le P z e₂ H hP hzP
    (by dsimp [e₂]; linarith) (by dsimp [e₂]; linarith)
  have he₃ := offset_div_square_le P w e₃ H hP hwP
    (by dsimp [e₃]; linarith) (by dsimp [e₃]; linarith)
  have herror := det4_amplitude_le x y z w R (H/P^2)
    (e₀/x^2) (e₁/y^2) (e₂/z^2) (e₃/w^2)
    hxy.le hyz.le hzw.le hspan he₀ he₁ he₂ he₃
  have hid : det4 x y z w q₀ q₁ q₂ q₃ =
      -(N*v4 x y z w*C) + det4 x y z w (e₀/x^2) (e₁/y^2) (e₂/z^2) (e₃/w^2) := by
    have hi := reciprocal_det4 x y z w hx0.ne' hy0.ne' hz0.ne' hw0.ne'
    change det4 x y z w (1/x^2) (1/y^2) (1/z^2) (1/w^2) = -v4 x y z w*C at hi
    rw [show -(N*v4 x y z w*C) = N*(-v4 x y z w*C) by ring, ← hi]
    dsimp [det4,e₀,e₁,e₂,e₃]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |-(N*v4 x y z w*C)| +
        |det4 x y z w (e₀/x^2) (e₁/y^2) (e₂/z^2) (e₃/w^2)| := abs_add_le _ _
    _ ≤ 4*N*R^6/P^5 + 4*R^3*(H/P^2) := add_le_add hmain herror
    _ = 4*N*R^6/P^5 + 4*H*R^3/P^2 := by ring

/-- An ordered actual witness quadruple has integer determinant at most -1. -/
lemma determinant_four_abs_ge_one {N H : ℕ} (hH : 0 < H)
    {a b c d : ℕ × ℕ} (ha : Witness N H a) (hb : Witness N H b)
    (hc : Witness N H c) (hd : Witness N H d)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1) :
    (1 : ℚ) ≤ |det4 (a.1 : ℚ) b.1 c.1 d.1 a.2 b.2 c.2 d.2| := by
  have hi := witness_det4_negative N H a.1 b.1 c.1 d.1 a.2 b.2 c.2 d.2
    hH ha.1 hab hbc hcd ha.2.1 hb.2.1 hc.2.1 hd.2.1
    ha.2.2.1 ha.2.2.2 hb.2.2.1 hb.2.2.2 hc.2.2.1 hc.2.2.2 hd.2.2.1 hd.2.2.2
  have hi' : det4 (a.1 : ℤ) b.1 c.1 d.1 a.2 b.2 c.2 d.2 ≤ -1 := by omega
  have hq : det4 (a.1 : ℚ) b.1 c.1 d.1 a.2 b.2 c.2 d.2 ≤ -1 := by
    dsimp [det4,v3] at hi' ⊢
    exact_mod_cast hi'
  have hle := neg_le_abs (det4 (a.1 : ℚ) b.1 c.1 d.1 a.2 b.2 c.2 d.2)
  linarith

end SquarefreeTwoNinths
