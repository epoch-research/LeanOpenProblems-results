import Submission.LocalPhaseDuality

/-! Quadratic integration of locally additive character-valued maps. Exact
quadratic identities and the conditional approximation estimate are separated
from the still-unproved symmetry estimate needed in the inverse argument. -/
namespace Erdos3LocalQuadraticIntegration
open Finset Erdos3FiniteUniformity Erdos3FiniteBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Additivity is asserted only when both summands and their sum are in P. -/
def LocallyAdditive (P : Set G) (F : G → AddChar G ℂ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x+y ∈ P → F (x+y) = F x+F y

def doubleHom : G →+ G where
  toFun x := x+x
  map_zero' := by simp
  map_add' x y := by abel

noncomputable def halfHom (h2 : Function.Bijective (fun x : G ↦ x+x)) : G →+ G :=
  (AddEquiv.ofBijective (doubleHom (G := G)) h2).symm.toAddMonoidHom

lemma halfHom_double (h2 : Function.Bijective (fun x : G ↦ x+x)) (x : G) :
    halfHom h2 (x+x) = x := (AddEquiv.ofBijective (doubleHom (G := G)) h2).symm_apply_apply x

noncomputable def quadraticPhase (F : G → AddChar G ℂ) (half : G →+ G) (x : G) : ℂ := F x (half x)
noncomputable def crossPhase (F : G → AddChar G ℂ) (half : G →+ G) (h x : G) : ℂ :=
  F h (half x)*F x (half h)

lemma quadraticPhase_norm (F : G → AddChar G ℂ) (half : G →+ G) (x : G) :
    ‖quadraticPhase F half x‖ = 1 := (F x).norm_apply _

lemma crossPhase_norm (F : G → AddChar G ℂ) (half : G →+ G) (h x : G) :
    ‖crossPhase F half h x‖ = 1 := by simp only [crossPhase,norm_mul,AddChar.norm_apply,one_mul]

lemma crossPhase_symmetric (F : G → AddChar G ℂ) (half : G →+ G) (h x : G) :
    crossPhase F half h x = crossPhase F half x h := mul_comm _ _

lemma quadraticPhase_add {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (half : G →+ G) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : x+y ∈ P) :
    quadraticPhase F half (x+y) = quadraticPhase F half x*quadraticPhase F half y*crossPhase F half y x := by
  unfold quadraticPhase crossPhase
  rw [hF x hx y hy hxy,half.map_add]
  simp only [AddChar.add_apply,AddChar.map_add_eq_mul]
  ring

lemma crossPhase_add_right {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (half : G →+ G) (h : G) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : x+y ∈ P) :
    crossPhase F half h (x+y) = crossPhase F half h x*crossPhase F half h y := by
  unfold crossPhase
  rw [hF x hx y hy hxy,half.map_add]
  simp only [AddChar.add_apply,AddChar.map_add_eq_mul]
  ring

/-- The derivative of the integrated phase is the symmetrized pairing. -/
lemma quadraticPhase_derivative {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (half : G →+ G) {x h : G}
    (hx : x ∈ P) (hh : h ∈ P) (hxh : x+h ∈ P) :
    derivative (quadraticPhase F half) h x = quadraticPhase F half h*crossPhase F half h x := by
  unfold derivative
  rw [quadraticPhase_add hF half hx hh hxh]
  calc
    _ = (quadraticPhase F half x*conj (quadraticPhase F half x))*
        (quadraticPhase F half h*crossPhase F half h x) := by ring
    _ = _ := by rw [mul_conj_eq_one (quadraticPhase_norm F half x),one_mul]

lemma quadraticPhase_second_derivative {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (half : G →+ G) {x h k : G}
    (hh : h ∈ P) (hk : k ∈ P) (hx : x ∈ P) (hxh : x+h ∈ P)
    (hxk : x+k ∈ P) (hxkh : (x+k)+h ∈ P) :
    derivative (derivative (quadraticPhase F half) h) k x = crossPhase F half h k := by
  change derivative (quadraticPhase F half) h (x+k)*
    conj (derivative (quadraticPhase F half) h x) = _
  rw [quadraticPhase_derivative hF half hxk hh hxkh,
    quadraticPhase_derivative hF half hx hh hxh,crossPhase_add_right hF half h hx hk hxk,map_mul]
  calc
    _ = (quadraticPhase F half h*conj (quadraticPhase F half h))*
        (crossPhase F half h x*conj (crossPhase F half h x))*crossPhase F half h k := by ring
    _ = _ := by rw [mul_conj_eq_one (quadraticPhase_norm F half h),
      mul_conj_eq_one (crossPhase_norm F half h x),one_mul,one_mul]

/-- All eight vertices and the two differentiated directions are checked to
lie in the local domain. Under these hypotheses the third derivative is one. -/
theorem quadraticPhase_third_derivative {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (half : G →+ G) {x h k l : G}
    (hh : h ∈ P) (hk : k ∈ P)
    (hx : x ∈ P) (hxh : x+h ∈ P) (hxk : x+k ∈ P) (hxkh : (x+k)+h ∈ P)
    (hxl : x+l ∈ P) (hxlh : (x+l)+h ∈ P) (hxlk : (x+l)+k ∈ P) (hxlkh : ((x+l)+k)+h ∈ P) :
    derivative (derivative (derivative (quadraticPhase F half) h) k) l x = 1 := by
  change derivative (derivative (quadraticPhase F half) h) k (x+l)*
    conj (derivative (derivative (quadraticPhase F half) h) k x) = 1
  rw [quadraticPhase_second_derivative hF half hh hk hxl hxlh hxlk hxlkh,
    quadraticPhase_second_derivative hF half hh hk hx hxh hxk hxkh]
  exact mul_conj_eq_one (crossPhase_norm F half h k)

lemma unit_square_lipschitz (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z^2-w^2‖ ≤ 2*‖z-w‖ := by
  rw [sq_sub_sq,norm_mul]
  have hh : ‖z+w‖ ≤ 2 := (norm_add_le _ _).trans_eq (by rw [hz,hw]; norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg (z-w))]

/-- Integration on doubled points needs only approximate symmetry at their
halves. This avoids inferring a small square root from a small squared error. -/
theorem quadraticPhase_derivative_approx {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (half : G →+ G) (hhalf : ∀ x, half (x+x) = x)
    {u v : G} (hu : u ∈ P) (hv : v ∈ P) (huu : u+u ∈ P) (hvv : v+v ∈ P)
    (hsum : (u+u)+(v+v) ∈ P) {ε : ℝ} (hsym : ‖F u v-F v u‖ ≤ ε) :
    ‖derivative (quadraticPhase F half) (v+v) (u+u)-
      quadraticPhase F half (v+v)*F (v+v) (u+u)‖ ≤ 2*ε := by
  rw [quadraticPhase_derivative hF half huu hvv hsum]
  have he : quadraticPhase F half (v+v)*crossPhase F half (v+v) (u+u)-
      quadraticPhase F half (v+v)*F (v+v) (u+u) =
      quadraticPhase F half (v+v)*(F v u)^2*((F u v)^2-(F v u)^2) := by
    unfold crossPhase
    rw [hhalf u,hhalf v,hF u hu u hu huu,hF v hv v hv hvv]
    simp only [AddChar.add_apply,AddChar.map_add_eq_mul]
    ring
  rw [he,norm_mul,norm_mul,quadraticPhase_norm,norm_pow,AddChar.norm_apply,one_pow,one_mul,one_mul]
  exact (unit_square_lipschitz (F u v) (F v u) ((F u).norm_apply v) ((F v).norm_apply u)).trans
    (mul_le_mul_of_nonneg_left hsym (by norm_num))

#print axioms quadraticPhase_third_derivative
#print axioms quadraticPhase_derivative_approx
end Erdos3LocalQuadraticIntegration
