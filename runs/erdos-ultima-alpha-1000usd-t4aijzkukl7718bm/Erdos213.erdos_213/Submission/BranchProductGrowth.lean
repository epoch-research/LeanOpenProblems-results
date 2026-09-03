import FormalConjecturesUtil

/-! Branch-product evaluations do not automatically turn growing hyperelliptic
2-torsion into growing planar rational-distance configurations. These are
identities and a counterexample for this particular evaluation construction,
not a theorem about all Jacobians or about Erdős 213. -/
namespace Erdos213.BranchProductGrowth
set_option maxHeartbeats 2000000

variable {R : Type*} [CommRing R]
def px (D a b : R) : R := a*b-D
def py (a b : R) : R := -a-b
def qnorm (D x y : R) : R := x^2+D*y^2
def qdist (D a b c d : R) : R := qnorm D (px D a b-px D c d) (py a b-py c d)
def tri (x₁ y₁ x₂ y₂ x₃ y₃ : R) : R :=
  (x₂-x₁)*(y₃-y₁)-(y₂-y₁)*(x₃-x₁)
def det3 (a b c d e f g h i : R) : R := a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

lemma norm_product (D a b : R) : qnorm D (px D a b) (py a b)=(a^2+D)*(b^2+D) := by
  dsimp [qnorm,px,py]
  ring

lemma shared_branch_distance (D a b c : R) : qdist D a b a c=(b-c)^2*(a^2+D) := by
  dsimp [qdist,qnorm,px,py]
  ring

lemma star_collinear_identity (D a b c d : R) :
    tri (px D a b) (py a b) (px D a c) (py a c) (px D a d) (py a d)=0 := by
  dsimp [tri,px,py]
  ring

/-- The three products associated to a three-element branch set, together with
zero, have zero circle determinant. -/
lemma top_circle_identity (D a b c : R) :
    det3 (px D a b) (py a b) (qnorm D (px D a b) (py a b))
      (px D a c) (py a c) (qnorm D (px D a c) (py a c))
      (px D b c) (py b c) (qnorm D (px D b c) (py b c))=0 := by
  dsimp [det3,qnorm,px,py]
  ring

lemma norm_square {D a b : ℚ} (ha : IsSquare (a^2+D)) (hb : IsSquare (b^2+D)) :
    IsSquare (qnorm D (px D a b) (py a b)) := by
  rw [norm_product]
  exact ha.mul hb

lemma local_edge_square {D a b c : ℚ} (ha : IsSquare (a^2+D)) :
    IsSquare (qdist D a b a c) := by
  rw [shared_branch_distance]
  exact (IsSquare.sq _).mul ha

/-- Rational branch parameters with square distance to i. -/
def root (u : ℚ) : ℚ := (u^2-1)/(2*u)
def radius (u : ℚ) : ℚ := (u^2+1)/(2*u)
lemma branch_norm (u : ℚ) (hu : u≠0) : (root u)^2+1=(radius u)^2 := by
  dsimp [root,radius]
  field_simp
  ring

lemma disjoint_control :
    qnorm (1 : ℚ) (px 1 (3/4) (4/3)) (py (3/4) (4/3))=(25/12)^2 ∧
    qnorm (1 : ℚ) (px 1 (15/8) (12/5)) (py (15/8) (12/5))=(221/40)^2 ∧
    qdist (1 : ℚ) (3/4) (4/3) (15/8) (12/5)=245569/14400 := by
  norm_num [qnorm,qdist,px,py]

lemma disjoint_control_nonsquare :
    ¬IsSquare (qdist (1 : ℚ) (3/4) (4/3) (15/8) (12/5)) := by
  rw [disjoint_control.2.2]
  decide +kernel

#print axioms top_circle_identity
#print axioms shared_branch_distance
#print axioms disjoint_control_nonsquare
end Erdos213.BranchProductGrowth
