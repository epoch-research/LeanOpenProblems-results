import FormalConjecturesUtil
import Submission.ProductNormMatching

/-! The orientation fiber above one exact radius-only matching control.
The four-cover implication is necessary, not an existence theorem.
The displayed nondegenerate control does NOT have rational pairwise distances. -/
namespace Erdos213.ProductOrientation
open ProductNormMatching
set_option maxHeartbeats 6000000

-- Radii 5/2 and 24/11; the matching ratio is (122/73)^2.
def bx (e u : ℚ) : ℚ := 5*e/(2*u)
def byCoord (u : ℚ) : ℚ := 5*9555/(2*u)
def cx (v : ℚ) : ℚ := 24*20213/(11*v)
def cy (e v : ℚ) : ℚ := -24*e/(11*v)

def qminus (e u v : ℚ) : ℚ := (bx e u-cx v)^2+(byCoord u-cy e v)^2
def qplus (e u v : ℚ) : ℚ := (bx e u+cx v)^2+(byCoord u+cy e v)^2

def FourCover (e : ℚ) : Prop :=
  IsSquare (e^2+9555^2) ∧ IsSquare (e^2+20213^2) ∧
  IsSquare (e^2+13195^2) ∧ IsSquare (e^2+14637^2)

lemma first_radius {e u : ℚ} (hu0 : u ≠ 0) (hu : u^2=e^2+9555^2) :
    radius 1 (bx e u) (byCoord u)=(5/2 : ℚ)^2 := by
  dsimp [radius,bx,byCoord]
  field_simp
  nlinarith only [hu]

lemma second_radius {e v : ℚ} (hv0 : v ≠ 0) (hv : v^2=e^2+20213^2) :
    radius 1 (cx v) (cy e v)=(24/11 : ℚ)^2 := by
  dsimp [radius,cx,cy]
  field_simp
  nlinarith only [hv]

/-- Every rational point of the two-square orientation fiber satisfies the
matching equations. The six remaining metric squares are not asserted. -/
theorem orientation_matching {e u v : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : u^2=e^2+9555^2) (hv : v^2=e^2+20213^2) :
    Matching 1 (bx e u) (byCoord u) (cx v) (cy e v) ((122/73 : ℚ)^2) := by
  unfold Matching
  rw [first_radius hu0 hu,second_radius hv0 hv]
  constructor <;> dsimp [bx,byCoord,cx,cy] <;> field_simp <;> ring

lemma anchor_product {x y R : ℚ} (hr : radius 1 x y=R^2) :
    minusNorm 1 x y*plusNorm 1 x y=(R^2+1)^2-4*x^2 := by
  dsimp [minusNorm,plusNorm,radius] at *
  linear_combination (x^2+y^2+R^2+2)*hr

lemma first_anchor_factor {e u : ℚ} (hu0 : u ≠ 0)
    (hu : u^2=e^2+9555^2) :
    u^2*(minusNorm 1 (bx e u) (byCoord u)*plusNorm 1 (bx e u) (byCoord u)) =
      (21/4 : ℚ)^2*(e^2+13195^2) := by
  rw [anchor_product (first_radius hu0 hu)]
  dsimp [bx]
  field_simp
  nlinarith only [hu]

lemma second_anchor_factor {e v : ℚ} (hv0 : v ≠ 0)
    (hv : v^2=e^2+20213^2) :
    v^2*(minusNorm 1 (cx v) (cy e v)*plusNorm 1 (cx v) (cy e v)) =
      (697/121 : ℚ)^2*(e^2+13195^2) := by
  rw [anchor_product (second_radius hv0 hv)]
  dsimp [cx]
  field_simp
  nlinarith only [hv]

lemma pair_product {x y z w R S : ℚ}
    (hb : radius 1 x y=R^2) (hc : radius 1 z w=S^2) :
    ((x-z)^2+(y-w)^2)*((x+z)^2+(y+w)^2) =
      (R^2+S^2)^2-4*(x*z+y*w)^2 := by
  have hm : (x-z)^2+(y-w)^2=R^2+S^2-2*(x*z+y*w) := by
    dsimp [radius] at hb hc
    linear_combination hb+hc
  have hp : (x+z)^2+(y+w)^2=R^2+S^2+2*(x*z+y*w) := by
    dsimp [radius] at hb hc
    linear_combination hb+hc
  rw [hm,hp]
  ring

lemma cross_polynomial {e u v : ℚ}
    (hu : u^2=e^2+9555^2) (hv : v^2=e^2+20213^2) :
    (5329/484 : ℚ)^2*u^2*v^2-4*(60/11 : ℚ)^2*e^2*(20213-9555)^2 =
      (5329/484 : ℚ)^2*(e^2+13195^2)*(e^2+14637^2) := by
  linear_combination (5329/484 : ℚ)^2*(v^2*hu+(e^2+9555^2)*hv)

lemma cross_factor {e u v : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : u^2=e^2+9555^2) (hv : v^2=e^2+20213^2) :
    u^2*v^2*(qminus e u v*qplus e u v) =
      (5329/484 : ℚ)^2*(e^2+13195^2)*(e^2+14637^2) := by
  have hd : bx e u*cx v+byCoord u*cy e v = (60/11 : ℚ)*e*(20213-9555)/(u*v) := by
    dsimp [bx,byCoord,cx,cy]
    field_simp
    ring
  calc
    u^2*v^2*(qminus e u v*qplus e u v) =
        (5329/484 : ℚ)^2*u^2*v^2-4*(60/11 : ℚ)^2*e^2*(20213-9555)^2 := by
      dsimp [qminus,qplus]
      rw [pair_product (first_radius hu0 hu) (second_radius hv0 hv),hd]
      field_simp
      ring
    _ = _ := cross_polynomial hu hv

lemma square_cancel {a t : ℚ} (ha : a ≠ 0) (h : IsSquare (a^2*t)) :
    IsSquare t := by
  have h' := h.div (IsSquare.sq a)
  convert h' using 1
  field_simp

/-- Even products of the six missing metric requirements force FOUR
simultaneous Pythagorean squares. This implication is not a converse. -/
theorem fourCover_of_metric {e u v : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : u^2=e^2+9555^2) (hv : v^2=e^2+20213^2)
    (hbminus : IsSquare (minusNorm 1 (bx e u) (byCoord u)))
    (hbplus : IsSquare (plusNorm 1 (bx e u) (byCoord u)))
    (hm : IsSquare (qminus e u v)) (hp : IsSquare (qplus e u v)) :
    FourCover e := by
  have hC : IsSquare (e^2+13195^2) := by
    apply square_cancel (by norm_num : (21/4 : ℚ) ≠ 0)
    rw [← first_anchor_factor hu0 hu]
    exact (IsSquare.sq u).mul (hbminus.mul hbplus)
  have hCD : IsSquare ((e^2+13195^2)*(e^2+14637^2)) := by
    apply square_cancel (by norm_num : (5329/484 : ℚ) ≠ 0)
    rw [← mul_assoc,← cross_factor hu0 hv0 hu hv]
    exact ((IsSquare.sq u).mul (IsSquare.sq v)).mul (hm.mul hp)
  have hC0 : e^2+13195^2 ≠ 0 := by nlinarith only [sq_nonneg e]
  have hD : IsSquare (e^2+14637^2) := by
    convert hCD.div hC using 1
    field_simp
  exact ⟨hu ▸ IsSquare.sq u,hv ▸ IsSquare.sq v,hC,hD⟩

/-- A two-square orientation control, not a four-cover or metric control. -/
theorem orientation_control :
    (93513/5 : ℚ)^2=(-80388/5)^2+9555^2 ∧
    (129137/5 : ℚ)^2=(-80388/5)^2+20213^2 ∧
    bx (-80388/5) (93513/5)=-9570/4453 ∧
    byCoord (93513/5)=11375/8906 ∧
    cx (129137/5)=83640/48983 ∧
    cy (-80388/5) (129137/5)=6048/4453 := by
  norm_num [bx,byCoord,cx,cy]

/-- The matching control fails an actual required squared distance. -/
theorem orientation_control_missing_square :
    ¬ IsSquare (minusNorm 1 (-9570/4453) (11375/8906)) := by
  have he : minusNorm 1 (-9570/4453) (11375/8906)=(205697/17812 : ℚ) := by
    norm_num [minusNorm]
  rw [he]
  decide +kernel

theorem matching_control :
    Matching 1 (-9570/4453) (11375/8906) (83640/48983) (6048/4453)
      ((122/73 : ℚ)^2) := by
  have h := orientation_matching (e := -80388/5) (u := 93513/5) (v := 129137/5)
    (by norm_num) (by norm_num) orientation_control.1 orientation_control.2.1
  convert h using 1 <;> norm_num [bx,byCoord,cx,cy]

theorem control_not_fourCover : ¬ FourCover (-80388/5) := by
  have hn : ¬ IsSquare (((-80388/5 : ℚ))^2+13195^2) := by decide +kernel
  exact fun h => hn h.2.2.1

theorem fourCover_zero : FourCover 0 := by
  exact ⟨by norm_num [IsSquare],by norm_num [IsSquare],
    by norm_num [IsSquare],by norm_num [IsSquare]⟩

/-- The necessary four-cover has a rational point that still fails an anchor
square, so it must not be used as a sufficient condition. -/
theorem fourCover_not_sufficient :
    FourCover 0 ∧ ¬ IsSquare (minusNorm 1 (bx 0 9555) (byCoord 9555)) := by
  refine ⟨fourCover_zero,?_⟩
  have he : minusNorm 1 (bx 0 9555) (byCoord 9555)=(29/4 : ℚ) := by
    norm_num [minusNorm,bx,byCoord]
  rw [he]
  decide +kernel

#print axioms fourCover_not_sufficient
#print axioms matching_control
#print axioms control_not_fourCover
#print axioms orientation_matching
#print axioms first_anchor_factor
#print axioms second_anchor_factor
#print axioms cross_factor
#print axioms fourCover_of_metric
#print axioms orientation_control
#print axioms orientation_control_missing_square
end Erdos213.ProductOrientation
