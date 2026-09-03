import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Algebraic identities for a Descartes circle-reflection experiment.
These do not assert general position or a cardinality-growth theorem. -/
namespace Erdos213.DescartesReflection
variable {R : Type*} [CommRing R]

def circleNorm (a : Fin 4 → R) : R := a 1 ^ 2 + a 2 ^ 2 - a 0 * a 3

def twicePair (a b : Fin 4 → R) : R :=
  2*a 1*b 1 + 2*a 2*b 2 - a 0*b 3 - a 3*b 0

def reflect (a b c d : Fin 4 → R) : Fin 4 → R :=
  fun i => 2*(b i+c i+d i)-a i

lemma twicePair_comm (a b : Fin 4 → R) : twicePair a b = twicePair b a := by
  unfold twicePair
  ring

lemma twicePair_self (a : Fin 4 → R) : twicePair a a = 2*circleNorm a := by
  unfold twicePair circleNorm
  ring

lemma reflect_pair (a b c d e : Fin 4 → R) :
    twicePair (reflect a b c d) e =
      2*(twicePair b e + twicePair c e + twicePair d e)-twicePair a e := by
  unfold twicePair reflect
  ring

lemma reflect_norm_identity (a b c d : Fin 4 → R) :
    circleNorm (reflect a b c d) = circleNorm a +
      4*(circleNorm b + circleNorm c + circleNorm d) +
      4*(twicePair b c + twicePair b d + twicePair c d) -
      2*(twicePair a b + twicePair a c + twicePair a d) := by
  unfold circleNorm twicePair reflect
  ring

lemma reflect_norm (a b c d : Fin 4 → R)
    (ha : circleNorm a = 1) (hb : circleNorm b = 1)
    (hc : circleNorm c = 1) (hd : circleNorm d = 1)
    (hab : twicePair a b = -2) (hac : twicePair a c = -2)
    (had : twicePair a d = -2) (hbc : twicePair b c = -2)
    (hbd : twicePair b d = -2) (hcd : twicePair c d = -2) :
    circleNorm (reflect a b c d) = 1 := by
  rw [reflect_norm_identity, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd]
  ring

lemma reflect_tangent (a b c d : Fin 4 → R)
    (hb : circleNorm b = 1) (hab : twicePair a b = -2)
    (hbc : twicePair b c = -2) (hbd : twicePair b d = -2) :
    twicePair (reflect a b c d) b = -2 := by
  rw [reflect_pair, twicePair_self, twicePair_comm c b, twicePair_comm d b,
    hb, hab, hbc, hbd]
  ring

lemma reflect_opposite (a b c d : Fin 4 → R)
    (ha : circleNorm a = 1) (hab : twicePair a b = -2)
    (hac : twicePair a c = -2) (had : twicePair a d = -2) :
    twicePair (reflect a b c d) a = -14 := by
  rw [reflect_pair, twicePair_self, twicePair_comm b a, twicePair_comm c a,
    twicePair_comm d a, ha, hab, hac, had]
  ring

lemma reflect_involutive (a b c d : Fin 4 → R) :
    reflect (reflect a b c d) b c d = a := by
  funext i
  simp only [reflect]
  ring

/-- Circle inversion about (u,v), with the new coordinates translated by -(u,v).
The first coordinate is the new signed curvature. -/
def invert (a : Fin 4 → R) (u v : R) : Fin 4 → R :=
  ![a 0*(u^2+v^2)-2*a 1*u-2*a 2*v+a 3, a 1-a 0*u, a 2-a 0*v, a 0]

lemma invert_norm (a : Fin 4 → R) (u v : R) :
    circleNorm (invert a u v) = circleNorm a := by
  simp [circleNorm, invert, Matrix.cons_val]
  ring

lemma invert_pair (a b : Fin 4 → R) (u v : R) :
    twicePair (invert a u v) (invert b u v) = twicePair a b := by
  simp [twicePair, invert, Matrix.cons_val]
  ring

lemma distance_numerator (a b : Fin 4 → R)
    (ha : circleNorm a = 1) (hb : circleNorm b = 1) :
    (a 1*b 0-b 1*a 0)^2 + (a 2*b 0-b 2*a 0)^2 =
      a 0^2 + b 0^2 - a 0*b 0*twicePair a b := by
  unfold circleNorm at ha hb
  unfold twicePair
  linear_combination b 0^2*ha + a 0^2*hb

section Field
variable {K : Type*} [Field K]

lemma center_distance_sq (a b : Fin 4 → K)
    (ha : circleNorm a = 1) (hb : circleNorm b = 1)
    (ha0 : a 0 ≠ 0) (hb0 : b 0 ≠ 0) :
    (a 1/a 0-b 1/b 0)^2 + (a 2/a 0-b 2/b 0)^2 =
      (a 0^2+b 0^2-a 0*b 0*twicePair a b)/(a 0*b 0)^2 := by
  have h := distance_numerator a b ha hb
  field_simp
  linear_combination h

lemma tangent_center_distance_sq (a b : Fin 4 → K)
    (ha : circleNorm a = 1) (hb : circleNorm b = 1)
    (ha0 : a 0 ≠ 0) (hb0 : b 0 ≠ 0) (hab : twicePair a b = -2) :
    (a 1/a 0-b 1/b 0)^2 + (a 2/a 0-b 2/b 0)^2 = (1/a 0+1/b 0)^2 := by
  rw [center_distance_sq a b ha hb ha0 hb0, hab]
  field_simp
  ring
end Field

/-- Five oriented circle vectors with pairwise external tangency are impossible.
The proof is a rank obstruction in the four-dimensional circle-coordinate space. -/
lemma no_five_tangent (v : Fin 5 → Fin 4 → ℝ)
    (hn : ∀ i, circleNorm (v i) = 1)
    (ht : ∀ i j, i ≠ j → twicePair (v i) (v j) = -2) : False := by
  let H : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0,0,0,-1; 0,2,0,0; 0,0,2,0; -1,0,0,0]
  let A : Matrix (Fin 5) (Fin 4) ℝ := v
  let G : Matrix (Fin 5) (Fin 5) ℝ := fun i j => if i=j then 2 else -2
  let B : Matrix (Fin 5) (Fin 5) ℝ := fun i j => if i=j then 1/6 else -1/12
  have hentry (i j : Fin 5) : (A*H*A.transpose) i j = twicePair (v i) (v j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply,
      A, H, twicePair]
    ring
  have hG : A*H*A.transpose = G := by
    ext i j
    rw [hentry]
    by_cases h : i=j
    · subst j
      simp [G, twicePair_self, hn]
    · simp [G,h,ht i j h]
  let J : Matrix (Fin 5) (Fin 5) ℝ := fun _ _ => 1
  have hJ : J*J = (5 : ℝ) • J := by
    ext i j
    simp [J, Matrix.mul_apply]
  have hGform : G = (4 : ℝ) • 1 - (2 : ℝ) • J := by
    ext i j
    by_cases h : i=j <;> norm_num [G,J,Matrix.one_apply,h]
  have hBform : B = (1/4 : ℝ) • 1 - (1/12 : ℝ) • J := by
    ext i j
    by_cases h : i=j <;> norm_num [B,J,Matrix.one_apply,h]
  have hGB : G*B = 1 := by
    rw [hGform,hBform]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,hJ,smul_smul]
    ext i j
    by_cases h : i=j <;> norm_num [J,Matrix.one_apply,h]
  have hb : (5 : ℕ) ≤ 4 := by
    calc
      5 = (1 : Matrix (Fin 5) (Fin 5) ℝ).rank := by simp
      _ = ((A*H*A.transpose)*B).rank := by rw [hG,hGB]
      _ ≤ (A*H*A.transpose).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (A*H).rank := Matrix.rank_mul_le_left _ _
      _ ≤ A.rank := Matrix.rank_mul_le_left _ _
      _ ≤ 4 := Matrix.rank_le_width A
  omega

#print axioms no_five_tangent
#print axioms reflect_norm
#print axioms reflect_opposite
#print axioms invert_norm
#print axioms invert_pair
#print axioms tangent_center_distance_sq
end Erdos213.DescartesReflection
