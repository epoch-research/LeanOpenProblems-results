import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Exact controls for congruence-based searches. The points (a,M*a²), for
positive distinct integer a, are in general position and have square squared
distances modulo M², but none of their nonzero distances is rational.
This is not a construction for Erdős 213 and not a disproof. -/
namespace Erdos213.LocalParabola

def sqDist (M a b : ℤ) : ℤ := (a-b)^2 + M^2*(a^2-b^2)^2

def triangle (M a b c : ℤ) : ℤ :=
  (b-a)*(M*c^2-M*a^2)-(M*b^2-M*a^2)*(c-a)

def det3 (a b c d e f g h i : ℤ) : ℤ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def circle (M a b c d : ℤ) : ℤ :=
  det3 (b-a) (M*b^2-M*a^2) (sqDist M b a)
    (c-a) (M*c^2-M*a^2) (sqDist M c a)
    (d-a) (M*d^2-M*a^2) (sqDist M d a)

lemma sqDist_factorization (M a b : ℤ) :
    sqDist M a b=(a-b)^2*(1+(M*(a+b))^2) := by
  unfold sqDist
  ring

lemma triangle_factorization (M a b c : ℤ) :
    triangle M a b c=M*(b-a)*(c-a)*(c-b) := by
  unfold triangle
  ring

lemma circle_factorization (M a b c d : ℤ) :
    circle M a b c d =
      M^3*(b-a)*(c-a)*(d-a)*(c-b)*(d-b)*(d-c)*(a+b+c+d) := by
  unfold circle det3 sqDist
  ring

lemma triangle_pos {M a b c : ℤ} (hM : 0<M) (hab : a<b) (hbc : b<c) :
    0<triangle M a b c := by
  rw [triangle_factorization]
  exact mul_pos (mul_pos (mul_pos hM (sub_pos.mpr hab))
    (sub_pos.mpr (hab.trans hbc))) (sub_pos.mpr hbc)

lemma circle_pos {M a b c d : ℤ} (hM : 0<M) (ha : 0<a)
    (hab : a<b) (hbc : b<c) (hcd : c<d) : 0<circle M a b c d := by
  rw [circle_factorization]
  have hb : 0<b := ha.trans hab
  have hc : 0<c := hb.trans hbc
  have hd : 0<d := hc.trans hcd
  have hac : a<c := hab.trans hbc
  have had : a<d := hac.trans hcd
  have hbd : b<d := hbc.trans hcd
  have hba := sub_pos.mpr hab
  have hca := sub_pos.mpr hac
  have hda := sub_pos.mpr had
  have hcb := sub_pos.mpr hbc
  have hdb := sub_pos.mpr hbd
  have hdc := sub_pos.mpr hcd
  positivity

/-- The squared distance is congruent to an explicit square modulo M². -/
lemma square_congruence (M a b : ℤ) : M^2 ∣ sqDist M a b-(a-b)^2 := by
  refine ⟨(a^2-b^2)^2, ?_⟩
  unfold sqDist
  ring

lemma not_isSquare_one_add_sq {k : ℤ} (hk : 0<k) : ¬IsSquare (1+k^2) := by
  rintro ⟨r,hr⟩
  have he : |r|^2=1+k^2 := by
    rw [sq_abs]
    simpa only [pow_two] using hr.symm
  rcases le_or_gt |r| k with h|h
  · have hs : |r|^2≤k^2 := (sq_le_sq₀ (abs_nonneg r) (le_of_lt hk)).mpr h
    omega
  · have h' : k+1≤|r| := by omega
    have hs : (k+1)^2≤|r|^2 :=
      (sq_le_sq₀ (by omega) (abs_nonneg r)).mpr h'
    nlinarith

/-- Despite the congruence, every nonzero distance in this positive integer
parabola family has an irrational square root. -/
lemma sqDist_not_rational_square {M a b : ℤ} (hM : 0<M) (ha : 0<a) (hab : a<b) :
    ¬IsSquare (sqDist M a b : ℚ) := by
  intro h
  have hdiff : (a : ℚ)-b≠0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_lt hab)
  have hquot := h.div (IsSquare.sq ((a : ℚ)-b))
  have hs : IsSquare ((1+(M*(a+b))^2 : ℤ) : ℚ) := by
    convert hquot using 1
    unfold sqDist
    push_cast
    field_simp
    ring
  apply not_isSquare_one_add_sq (k := M*(a+b)) (mul_pos hM (add_pos ha (ha.trans hab)))
  exact Rat.isSquare_intCast_iff.mp hs

#print axioms triangle_pos
#print axioms circle_pos
#print axioms square_congruence
#print axioms sqDist_not_rational_square

end Erdos213.LocalParabola
