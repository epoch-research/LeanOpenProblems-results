import Submission.TwistedHyperbola
import Submission.OffsetCircle

/-! A two-parameter common-square-class family for two antipodal pairs.
The parameterization is not an unrestricted cardinality construction. -/
namespace Erdos213.CommonClassHyperbola

def den (b u : ℚ) : ℚ := u^2-b^2-1
def ratio1 (b u : ℚ) : ℚ := (u^2-2*u+b^2+1)/den b u
def ratio2 (b u : ℚ) : ℚ := (-u^2+2*u*(b^2+1)-b^2-1)/den b u
def generalTwist (b u : ℚ) : ℚ := (b^2-(ratio1 b u)^2)/((ratio1 b u)^2-1)

lemma ratio_conic (b u : ℚ) (hd : den b u ≠ 0) :
    (ratio2 b u)^2=(b^2+1)*(ratio1 b u)^2-b^2 := by
  dsimp [ratio1,ratio2]
  field_simp
  dsimp [den]
  ring

lemma ratio_line (b u : ℚ) (hd : den b u ≠ 0) :
    ratio2 b u=1+u*(ratio1 b u-1) := by
  dsimp [ratio1,ratio2]
  field_simp
  dsimp [den]
  ring

lemma general_anchor_identities (b u : ℚ) (hd : den b u ≠ 0)
    (hr : (ratio1 b u)^2 ≠ 1) :
    b^2+generalTwist b u=(1+generalTwist b u)*(ratio1 b u)^2 ∧
    b^4+generalTwist b u=(1+generalTwist b u)*(ratio2 b u)^2 := by
  have hr' : (ratio1 b u)^2-1 ≠ 0 := sub_ne_zero.mpr hr
  have hc := ratio_conic b u hd
  dsimp [generalTwist]
  constructor
  · field_simp
    ring
  · field_simp
    linear_combination (1-b^2)*hc

lemma recover_conic_parameters (b r s : ℚ) (hb : b ≠ 0) (hr : r ≠ 1)
    (hc : s^2=(b^2+1)*r^2-b^2) :
    ∃ u : ℚ, den b u ≠ 0 ∧ ratio1 b u=r ∧ ratio2 b u=s := by
  let u := (s-1)/(r-1)
  have hr' : r-1 ≠ 0 := sub_ne_zero.mpr hr
  have hl : u*(r-1)=s-1 := by dsimp [u]; field_simp
  have he : (r-1)*(den b u*(r-1)+2*u-2*b^2-2)=0 := by
    dsimp [den]
    linear_combination (s+1+u*(r-1))*hl+hc
  have he' : den b u*(r-1)+2*u-2*b^2-2=0 := (mul_eq_zero.mp he).resolve_left hr'
  have hd : den b u ≠ 0 := by
    intro hz
    rw [hz] at he'
    have hu : u=b^2+1 := by linarith only [he']
    dsimp [den] at hz
    rw [hu] at hz
    nlinarith only [hz,sq_pos_of_ne_zero hb,sq_nonneg (b^2)]
  have h1 : ratio1 b u=r := by
    apply (div_eq_iff hd).mpr
    dsimp [den] at *
    linear_combination -he'
  refine ⟨u,hd,h1,?_⟩
  rw [ratio_line b u hd,h1]
  linarith only [hl]

/-- Every nondegenerate common-class anchor profile of this algebraic form is
covered. No claim is made that arbitrary planar point sets have this form. -/
lemma recover_anchor_profile (b N r s : ℚ) (hb : b ≠ 0) (hb1 : b^2 ≠ 1)
    (hN : 1+N ≠ 0) (hr : b^2+N=(1+N)*r^2) (hs : b^4+N=(1+N)*s^2) :
    ∃ u : ℚ, den b u ≠ 0 ∧ ratio1 b u=r ∧ ratio2 b u=s ∧ generalTwist b u=N := by
  have hr1 : r^2 ≠ 1 := by
    intro hz
    rw [hz] at hr
    apply hb1
    linarith only [hr]
  have hr' : r ≠ 1 := by intro hz; rw [hz] at hr1; norm_num at hr1
  have hc : s^2=(b^2+1)*r^2-b^2 := by
    apply (mul_left_inj' hN).mp
    linear_combination (b^2+1)*hr-hs
  obtain ⟨u,hd,h1,h2⟩ := recover_conic_parameters b r s hb hr' hc
  refine ⟨u,hd,h1,h2,?_⟩
  dsimp [generalTwist]
  rw [h1]
  apply (div_eq_iff (sub_ne_zero.mpr hr1)).mpr
  linear_combination hr

def twist (b : ℚ) : ℚ := (b^4-6*b^2+1)/8
def root0 (b : ℚ) : ℚ := (b^2-3)/2
def root1 (b : ℚ) : ℚ := (b^2+1)/2
def root2 (b : ℚ) : ℚ := (3*b^2-1)/2

lemma class_two_seed_identities (b : ℚ) :
    2*(1+twist b)=(root0 b)^2 ∧ 2*(b^2+twist b)=(root1 b)^2 ∧
      2*(b^4+twist b)=(root2 b)^2 := by
  dsimp [twist,root0,root1,root2]
  constructor
  · ring
  constructor <;> ring

lemma root0_ne_zero (b : ℚ) : root0 b ≠ 0 := by
  intro hz
  have hn : ¬ IsSquare (3 : ℚ) := by decide +kernel
  apply hn
  refine ⟨b,?_⟩
  dsimp [root0] at hz
  nlinarith only [hz]

lemma twist_ne_b_sq (b : ℚ) : twist b ≠ b^2 := by
  intro hz
  have hn : ¬ IsSquare (3 : ℚ) := by decide +kernel
  apply hn
  refine ⟨(b^2-7)/4,?_⟩
  dsimp [twist] at hz
  linear_combination -hz/2

lemma twist_pos (b : ℚ) (hb : 3 ≤ b) : 0<twist b := by
  have he : 0 ≤ b^2-9 := by nlinarith only [hb]
  rw [show twist b=((b^2-9)^2+12*(b^2-9)+28)/8 by dsimp [twist]; ring]
  positivity

/-- This rational-coordinate normalization absorbs the common square class 2.
The plane metric remains x^2+N*y^2; no nonrational coordinate is asserted rational. -/
def point (b t : ℚ) : ℚ × ℚ :=
  ((t+twist b/t)/root0 b,(t⁻¹-t)/root0 b)

lemma normalized_distance (b t s : ℚ) :
    OffsetCircle.distSq (twist b) (point b t) (point b s)=
      TwistedHyperbola.distanceSq (twist b) t s/2 := by
  have hr := root0_ne_zero b
  have he := (class_two_seed_identities b).1
  have hg (x y u v : ℚ) :
      ((x+twist b*y)/root0 b-(u+twist b*v)/root0 b)^2+
        twist b*((y-x)/root0 b-(v-u)/root0 b)^2=
      ((x-u)^2+twist b*(y-v)^2)/2 := by
    field_simp
    linear_combination ((x-u)^2+twist b*(y-v)^2)*he
  simpa only [OffsetCircle.distSq,OffsetCircle.normSq,point,TwistedHyperbola.distanceSq,
    Prod.fst_sub,Prod.snd_sub,div_eq_mul_inv] using hg t t⁻¹ s s⁻¹

lemma normalized_square_criterion (b t s : ℚ) (ht : t ≠ 0) (hs : s ≠ 0)
    (h : IsSquare (2*((t*s)^2+twist b))) :
    IsSquare (OffsetCircle.distSq (twist b) (point b t) (point b s)) := by
  rw [normalized_distance,TwistedHyperbola.distance_factor (twist b) t s ht hs]
  convert (IsSquare.sq ((t-s)/(2*t*s))).mul h using 1
  field_simp

#print axioms general_anchor_identities
#print axioms recover_anchor_profile
#print axioms class_two_seed_identities
#print axioms twist_ne_b_sq
#print axioms twist_pos
#print axioms normalized_distance
#print axioms normalized_square_criterion
end Erdos213.CommonClassHyperbola
