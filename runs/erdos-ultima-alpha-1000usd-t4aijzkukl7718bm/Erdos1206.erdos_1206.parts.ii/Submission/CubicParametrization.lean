import Submission.CubeCollisionParametrization

/-!
A homogeneous cubic parametrization of the positive rational Fermat surface,
obtained from the earlier quartic parametrization by a Cayley substitution.
No density conclusion is asserted.
-/

namespace Erdos1206
namespace CubicParametrization

def norm (a b : ℚ) : ℚ := a^2-a*b+b^2

def A (a b t : ℚ) : ℚ :=
  t^3+(a-2*b)*t^2+3*a^2*t+3*norm a b*(a-b)
def B (a b t : ℚ) : ℚ :=
  t^3+(a+b)*t^2+3*(a-b)^2*t+3*a*norm a b
def C (a b t : ℚ) : ℚ :=
  t^3-(a+b)*t^2+3*(a-b)^2*t-3*a*norm a b
def D (a b t : ℚ) : ℚ :=
  t^3-(a-2*b)*t^2+3*a^2*t-3*norm a b*(a-b)

lemma identity (a b t : ℚ) : A a b t ^ 3 + D a b t ^ 3 = B a b t ^ 3 + C a b t ^ 3 := by
  dsimp [A,B,C,D,norm]
  ring

lemma sum_outer (a b t : ℚ) : A a b t + D a b t = 2*t*(t^2+3*a^2) := by
  dsimp [A,D]
  ring

lemma sum_inner (a b t : ℚ) : B a b t + C a b t = 2*t*(t^2+3*(a-b)^2) := by
  dsimp [B,C]
  ring

def cayleyDen (r s : ℚ) : ℚ := cubeParamNorm r s + 2*r-s+1

def cayleyA (r s : ℚ) : ℚ := (cubeParamNorm r s+s-1) / cayleyDen r s

def cayleyB (r s : ℚ) : ℚ := 2*s / cayleyDen r s

lemma cayleyDen_pos {r s : ℚ} (hs : 0 < s) : 0 < cayleyDen r s := by
  have hsq : 0 < s^2 := sq_pos_of_pos hs
  have hh : 4*cayleyDen r s = (2*(r+1)-s)^2+3*s^2 := by
    dsimp [cayleyDen,cubeParamNorm]
    ring
  nlinarith [sq_nonneg (2*(r+1)-s)]

lemma cayley_identities {r s : ℚ} (hden : cayleyDen r s ≠ 0) :
    (cayleyDen r s)^2 * A (cayleyA r s) (cayleyB r s) 1 = 8*cubeParamA r s ∧
    (cayleyDen r s)^2 * B (cayleyA r s) (cayleyB r s) 1 = 8*cubeParamB r s ∧
    (cayleyDen r s)^2 * C (cayleyA r s) (cayleyB r s) 1 = 8*cubeParamC r s ∧
    (cayleyDen r s)^2 * D (cayleyA r s) (cayleyB r s) 1 = 8*cubeParamD r s := by
  dsimp [A,B,C,D,norm,cayleyA,cayleyB,cubeParamA,cubeParamB,cubeParamC,cubeParamD]
  constructor
  · field_simp
    dsimp [cayleyDen,cubeParamNorm]
    ring
  constructor
  · field_simp
    dsimp [cayleyDen,cubeParamNorm]
    ring
  constructor
  · field_simp
    dsimp [cayleyDen,cubeParamNorm]
    ring
  · field_simp
    dsimp [cayleyDen,cubeParamNorm]
    ring

/-- Every ordered positive rational cubic collision is a positive rational
dilate of these fixed cubic forms (in the affine chart t=1). -/
theorem complete {x y z w : ℚ}
    (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z) (hzw : z < w)
    (he : x^3+w^3=y^3+z^3) :
    ∃ a b k : ℚ, 0 < b ∧ 0 < k ∧
      x = k*A a b 1 ∧ y = k*B a b 1 ∧
      z = k*C a b 1 ∧ w = k*D a b 1 := by
  obtain ⟨r,s,t,hs,ht,hN0,hN1,hx',hy',hz',hw'⟩ :=
    ordered_cube_collision_quartic_parametrization hx hxy hyz hzw he
  have hden := cayleyDen_pos (r := r) hs
  obtain ⟨ha,hb,hc,hd⟩ := cayley_identities hden.ne'
  refine ⟨cayleyA r s,cayleyB r s,t*(cayleyDen r s)^2/8,?_,by positivity,?_,?_,?_,?_⟩
  · dsimp [cayleyB]
    positivity
  · rw [hx']
    nlinarith only [congrArg (fun q : ℚ => t*q) ha]
  · rw [hy']
    nlinarith only [congrArg (fun q : ℚ => t*q) hb]
  · rw [hz']
    nlinarith only [congrArg (fun q : ℚ => t*q) hc]
  · rw [hw']
    nlinarith only [congrArg (fun q : ℚ => t*q) hd]

#print axioms complete

end CubicParametrization
end Erdos1206
