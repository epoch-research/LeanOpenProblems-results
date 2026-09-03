import FormalConjecturesUtil
import Submission.C8FiniteCubic

/-! Quartic translation obstructions for the auxiliary C8 incidence model.
These theorems are not a settlement of the rational-exponent conjecture. -/
open SimpleGraph
namespace Erdos713C8QuarticMixed
open Erdos713C8FiniteQuadratic Erdos713C8FiniteCubic
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

/-- Over a finite field of characteristic two, a binary affine quadratic
with nonzero mixed coefficient has a zero. -/
lemma affine_quadratic_zero [Fintype K] [CharP K 2]
    (A B C D E F : K) (hB : B ≠ 0) :
    ∃ s t : K, A*s^2+B*s*t+C*t^2+D*s+E*t+F = 0 := by
  have hSq : Function.Surjective (fun z : K => z^2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  by_cases hA : A = 0
  · subst A
    by_cases hD : D = 0
    · subst D
      refine ⟨-(C+E+F)/B,1,?_⟩
      field_simp
      ring
    · refine ⟨-F/D,0,?_⟩
      field_simp
      ring
  · let t := -D/B
    obtain ⟨s,hs⟩ := hSq (-(C*t^2+E*t+F)/A)
    change s^2 = -(C*t^2+E*t+F)/A at hs
    refine ⟨s,t,?_⟩
    have h0 : A*s^2+C*t^2+E*t+F = 0 := by
      rw [hs]
      field_simp
      ring
    have ht : B*t+D = 0 := by
      dsimp [t]
      field_simp
      ring
    linear_combination h0+s*ht

lemma add_cube_char_two [CharP K 2] (a s : K) :
    (a+s)^3 = a^3+s*a^2+s^2*a+s^3 := by
  rw [show (3 : ℕ) = 2+1 from rfl,pow_succ,CharTwo.add_sq]
  ring

lemma add_four_char_two [CharP K 2] (a s : K) :
    (a+s)^4 = a^4+s^4 := by
  rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,CharTwo.add_sq,CharTwo.add_sq]
  ring

def quartic (A B C D E F G H I J L M N O P : K) (a b : K) : K :=
  A*a^4+B*a^3*b+C*a^2*b^2+D*a*b^3+E*b^4+
    cubic F G H I J L M N O P a b

lemma quartic_translation [CharP K 2]
    (A B C D E F G H I J L M N O P a b s t : K) :
    quartic A B C D E F G H I J L M N O P (a+s) (b+t) =
      quartic A B C D E F G H I J L M N O P a b +
      s*(B*a^2*b+D*b^3+F*a^2+H*b^2) +
      t*(B*a^3+D*a*b^2+G*a^2+I*b^2) +
      s^2*(B*a*b+C*b^2) + t^2*(C*a^2+D*a*b) +
      s*t*(B*a^2+D*b^2) +
      (B*s^2*t+D*t^3+F*s^2+H*t^2+L*t)*a +
      (B*s^3+D*s*t^2+G*s^2+I*t^2+L*s)*b +
      (quartic A B C D E F G H I J L M N O P s t-P) := by
  simp only [quartic,cubic,CharTwo.add_sq,add_cube_char_two,add_four_char_two]
  ring

lemma quartic_shear [CharP K 2]
    (A B C D E F G H I J L M N O P a b τ : K) :
    quartic A B C D E F G H I J L M N O P a (b+τ*a) =
      quartic (A+B*τ+C*τ^2+D*τ^3+E*τ^4) (B+D*τ^2) (C+D*τ) D E
        (F+G*τ+H*τ^2+I*τ^3) (G+I*τ^2) (H+I*τ) I
        (J+L*τ+M*τ^2) L M (N+O*τ) O P a b := by
  simp only [quartic,cubic,CharTwo.add_sq,add_cube_char_two,add_four_char_two]
  ring

lemma moment_add (u v r t : K) (Q R : K → K → K) :
    moment u v r t (fun a b => Q a b+R a b) =
      moment u v r t Q+moment u v r t R := by
  dsimp [moment]
  ring

lemma moment_smul (u v r t c : K) (Q : K → K → K) :
    moment u v r t (fun a b => c*Q a b) = c*moment u v r t Q := by
  dsimp [moment]
  ring

lemma moment_const (u v r t c : K) :
    moment u v r t (fun _ _ => c) = 0 := by
  dsimp [moment]
  ring

lemma moment_left (u v r t : K) :
    moment u v r t (fun a _ => a) = 0 := by
  dsimp [moment]
  ring

lemma moment_right (u v r t : K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun _ b => b) = 0 := by
  dsimp [moment]
  linear_combination hB

lemma moment_left_sq (u v r t : K) :
    moment u v r t (fun a _ => a^2) = Erdos713C8FiniteQuadratic.D u v r t := by
  dsimp [moment,Erdos713C8FiniteQuadratic.D]
  ring

lemma moment_right_sq (u v r t : K) :
    moment u v r t (fun _ b => b^2) = Erdos713C8FiniteQuadratic.J u v r t := by
  dsimp [moment,Erdos713C8FiniteQuadratic.J]
  ring

lemma moment_mul (u v r t : K) :
    moment u v r t (fun a b => a*b) = Erdos713C8FiniteQuadratic.E u v r t := by
  dsimp [moment,Erdos713C8FiniteQuadratic.E]
  ring

lemma moment_quartic_translation [CharP K 2]
    (A B C D E F G H I J L M N O P u v r t s z : K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a b => quartic A B C D E F G H I J L M N O P (a+s) (b+z)) =
      (B*Erdos713C8FiniteQuadratic.E u v r t+C*Erdos713C8FiniteQuadratic.J u v r t)*s^2 +
      (B*Erdos713C8FiniteQuadratic.D u v r t+D*Erdos713C8FiniteQuadratic.J u v r t)*s*z +
      (C*Erdos713C8FiniteQuadratic.D u v r t+D*Erdos713C8FiniteQuadratic.E u v r t)*z^2 +
      moment u v r t (fun a b => B*a^2*b+D*b^3+F*a^2+H*b^2)*s +
      moment u v r t (fun a b => B*a^3+D*a*b^2+G*a^2+I*b^2)*z +
      moment u v r t (quartic A B C D E F G H I J L M N O P) := by
  have he := congrArg (moment u v r t)
    (funext fun a => funext fun b => quartic_translation A B C D E F G H I J L M N O P a b s z)
  rw [he]
  simp only [mul_assoc,moment_add,moment_smul,moment_const,moment_left,moment_right u v r t hB,
    moment_left_sq,moment_right_sq,moment_mul]
  ring

lemma octagon_of_mixed_moment [Fintype K] [CharP K 2]
    (A B C D E F G H I J L M N O P u v r t : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0)
    (hMix : B*Erdos713C8FiniteQuadratic.D u v r t+D*Erdos713C8FiniteQuadratic.J u v r t ≠ 0) :
    Octagon (quartic A B C D E F G H I J L M N O P) := by
  obtain ⟨s,z,hsz⟩ := affine_quadratic_zero
    (B*Erdos713C8FiniteQuadratic.E u v r t+C*Erdos713C8FiniteQuadratic.J u v r t)
    (B*Erdos713C8FiniteQuadratic.D u v r t+D*Erdos713C8FiniteQuadratic.J u v r t)
    (C*Erdos713C8FiniteQuadratic.D u v r t+D*Erdos713C8FiniteQuadratic.E u v r t)
    (moment u v r t (fun a b => B*a^2*b+D*b^3+F*a^2+H*b^2))
    (moment u v r t (fun a b => B*a^3+D*a*b^2+G*a^2+I*b^2))
    (moment u v r t (quartic A B C D E F G H I J L M N O P)) hMix
  apply offset_octagon _ s z
  apply octagon_of_moment _ u v r t hu hv hu1 hv1 huv hr ht hB
  rw [moment_quartic_translation A B C D E F G H I J L M N O P u v r t s z hB]
  exact hsz

/-- Every quartic potential with a nonzero a³b or ab³ coefficient contains
an octagon over a finite characteristic-two field of order greater than four.
All the other coefficients are arbitrary. -/
theorem quartic_odd_mixed_octagon [Fintype K] [CharP K 2]
    (A B C D E F G H I J L M N O P : K)
    (hq : 4 < Fintype.card K) (hBD : B ≠ 0 ∨ D ≠ 0) :
    Octagon (quartic A B C D E F G H I J L M N O P) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hd,_⟩ := parameters_char_two (K := K) hq
  obtain ⟨τ,hτ⟩ := exists_nonzero_shift B D
    (Erdos713C8FiniteQuadratic.D u v r t) (Erdos713C8FiniteQuadratic.J u v r t) hd hBD
  apply shift_octagon τ (Q := quartic
    (A+B*τ+C*τ^2+D*τ^3+E*τ^4) (B+D*τ^2) (C+D*τ) D E
    (F+G*τ+H*τ^2+I*τ^3) (G+I*τ^2) (H+I*τ) I
    (J+L*τ+M*τ^2) L M (N+O*τ) O P)
  · intro a b
    exact quartic_shear A B C D E F G H I J L M N O P a b τ
  · exact octagon_of_mixed_moment _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u v r t
      hu hv hu1 hv1 huv hr ht hB hτ

theorem contains_quartic_odd_mixed [Fintype K] [CharP K 2]
    (A B C D E F G H I J L M N O P : K)
    (hq : 4 < Fintype.card K) (hBD : B ≠ 0 ∨ D ≠ 0) :
    cycleGraph 8 ⊑ graph (quartic A B C D E F G H I J L M N O P) :=
  contains_of_octagon (quartic_odd_mixed_octagon A B C D E F G H I J L M N O P hq hBD)

#print axioms affine_quadratic_zero
#print axioms moment_quartic_translation
#print axioms quartic_odd_mixed_octagon
#print axioms contains_quartic_odd_mixed
end Erdos713C8QuarticMixed
