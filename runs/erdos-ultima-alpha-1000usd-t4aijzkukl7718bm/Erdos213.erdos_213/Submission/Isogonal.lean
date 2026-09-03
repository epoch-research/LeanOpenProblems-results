import Mathlib.Algebra.Group.Even
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The arithmetic identity behind isogonal conjugation. This provides a
three-anchor distance construction, not an extension theorem for arbitrary
rational-distance sets. -/
namespace Erdos213.Isogonal

def normForm {R : Type*} [CommRing R] (D x y : R) : R := x^2+D*y^2

lemma norm_identity {R : Type*} [CommRing R] (D u v x y b c : R) :
    normForm D (normForm D x y*c*u+normForm D u v*b*x)
      (normForm D x y*c*v+normForm D u v*b*y) =
    normForm D u v*normForm D x y*normForm D (b*u+c*x) (b*v+c*y) := by
  unfold normForm
  ring

/-- With the first triangle vertex translated to zero, the original point has
numerator b*B+c*C and denominator s. Its isogonal conjugate has the numerator
in this statement, multiplied by the remaining barycentric coordinate a.
If the original three relevant distances are rational, so is the new one. -/
lemma vertex_norm_isSquare (D u v x y a b c s W : ℚ) (hs : s ≠ 0)
    (hB : IsSquare (normForm D u v)) (hC : IsSquare (normForm D x y))
    (hP : IsSquare (normForm D (b*u+c*x) (b*v+c*y)/s^2)) :
    IsSquare (normForm D
      (a*(normForm D x y*c*u+normForm D u v*b*x)/W)
      (a*(normForm D x y*c*v+normForm D u v*b*y)/W)) := by
  have hnum : IsSquare (normForm D (b*u+c*x) (b*v+c*y)) := by
    have hh := hP.mul (IsSquare.sq s)
    simpa [hs] using hh
  have he : normForm D
      (a*(normForm D x y*c*u+normForm D u v*b*x)/W)
      (a*(normForm D x y*c*v+normForm D u v*b*y)/W) =
      (a^2*(normForm D u v*normForm D x y*
        normForm D (b*u+c*x) (b*v+c*y)))/W^2 := by
    rw [← norm_identity D u v x y b c]
    unfold normForm
    ring
  rw [he]
  exact ((IsSquare.sq a).mul ((hB.mul hC).mul hnum)).div (IsSquare.sq W)

abbrev QPoint := ℚ × ℚ

def normBetween (D : ℚ) (P Q : QPoint) : ℚ :=
  normForm D (P.1-Q.1) (P.2-Q.2)

def barycentric (A B C : QPoint) (a b c : ℚ) : QPoint :=
  ((a*A.1+b*B.1+c*C.1)/(a+b+c), (a*A.2+b*B.2+c*C.2)/(a+b+c))

def isogonal (D : ℚ) (A B C : QPoint) (a b c : ℚ) : QPoint :=
  barycentric A B C (normBetween D B C*b*c)
    (normBetween D A C*a*c) (normBetween D A B*a*b)

lemma normBetween_comm (D : ℚ) (A B : QPoint) :
    normBetween D A B = normBetween D B A := by
  unfold normBetween normForm
  ring

lemma barycentric_first_norm (D : ℚ) (A B C : QPoint) (a b c : ℚ)
    (hs : a+b+c ≠ 0) :
    normBetween D (barycentric A B C a b c) A =
      normForm D (b*(B.1-A.1)+c*(C.1-A.1))
        (b*(B.2-A.2)+c*(C.2-A.2))/(a+b+c)^2 := by
  unfold normBetween barycentric normForm
  dsimp only
  field_simp
  ring

/-- The actual barycentric transformation preserves the rational-square
squared distance to the first vertex. Cycling the data gives the other two. -/
lemma isogonal_first_vertex (D : ℚ) (A B C : QPoint) (a b c : ℚ)
    (hs : a+b+c ≠ 0)
    (hW : normBetween D B C*b*c+normBetween D A C*a*c+
      normBetween D A B*a*b ≠ 0)
    (hAB : IsSquare (normBetween D A B))
    (hAC : IsSquare (normBetween D A C))
    (hP : IsSquare (normBetween D (barycentric A B C a b c) A)) :
    IsSquare (normBetween D (isogonal D A B C a b c) A) := by
  rw [barycentric_first_norm D A B C a b c hs] at hP
  have hnum : IsSquare (normForm D (b*(B.1-A.1)+c*(C.1-A.1))
      (b*(B.2-A.2)+c*(C.2-A.2))) := by
    have h := hP.mul (IsSquare.sq (a+b+c))
    simpa [hs] using h
  unfold isogonal
  rw [barycentric_first_norm D A B C _ _ _ hW]
  have hid : normForm D
      (normBetween D A C*a*c*(B.1-A.1)+normBetween D A B*a*b*(C.1-A.1))
      (normBetween D A C*a*c*(B.2-A.2)+normBetween D A B*a*b*(C.2-A.2)) =
      a^2*(normBetween D A B*normBetween D A C*
        normForm D (b*(B.1-A.1)+c*(C.1-A.1))
          (b*(B.2-A.2)+c*(C.2-A.2))) := by
    unfold normBetween normForm
    ring
  rw [hid]
  exact ((IsSquare.sq a).mul ((hAB.mul hAC).mul hnum)).div (IsSquare.sq _)

lemma barycentric_cyclic (A B C : QPoint) (a b c : ℚ) :
    barycentric B C A b c a = barycentric A B C a b c := by
  unfold barycentric
  ext <;> dsimp <;> ring

lemma isogonal_cyclic (D : ℚ) (A B C : QPoint) (a b c : ℚ) :
    isogonal D B C A b c a = isogonal D A B C a b c := by
  unfold isogonal barycentric normBetween normForm
  ext <;> dsimp <;> ring

lemma isogonal_three_vertices (D : ℚ) (A B C : QPoint) (a b c : ℚ)
    (hs : a+b+c ≠ 0)
    (hW : normBetween D B C*b*c+normBetween D A C*a*c+
      normBetween D A B*a*b ≠ 0)
    (hAB : IsSquare (normBetween D A B))
    (hAC : IsSquare (normBetween D A C))
    (hBC : IsSquare (normBetween D B C))
    (hPA : IsSquare (normBetween D (barycentric A B C a b c) A))
    (hPB : IsSquare (normBetween D (barycentric A B C a b c) B))
    (hPC : IsSquare (normBetween D (barycentric A B C a b c) C)) :
    IsSquare (normBetween D (isogonal D A B C a b c) A) ∧
    IsSquare (normBetween D (isogonal D A B C a b c) B) ∧
    IsSquare (normBetween D (isogonal D A B C a b c) C) := by
  refine ⟨isogonal_first_vertex D A B C a b c hs hW hAB hAC hPA, ?_, ?_⟩
  · rw [← isogonal_cyclic D A B C a b c]
    apply isogonal_first_vertex D B C A b c a
    · convert hs using 1 <;> ring
    · convert hW using 1 <;> unfold normBetween normForm <;> ring
    · exact hBC
    · rwa [normBetween_comm]
    · rwa [barycentric_cyclic]
  · rw [← isogonal_cyclic D A B C a b c, ← isogonal_cyclic D B C A b c a]
    apply isogonal_first_vertex D C A B c a b
    · convert hs using 1 <;> ring
    · convert hW using 1 <;> unfold normBetween normForm <;> ring
    · rwa [normBetween_comm]
    · rwa [normBetween_comm]
    · rwa [barycentric_cyclic, barycentric_cyclic]

#print axioms norm_identity
#print axioms vertex_norm_isSquare
#print axioms isogonal_first_vertex
#print axioms isogonal_three_vertices
end Erdos213.Isogonal
