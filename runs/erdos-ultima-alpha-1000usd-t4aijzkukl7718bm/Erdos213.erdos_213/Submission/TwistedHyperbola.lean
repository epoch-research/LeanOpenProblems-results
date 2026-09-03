import Mathlib.Tactic

/-! Arithmetic identities for a rectangular-hyperbola construction.
No unrestricted existence assertion is made. -/
namespace Erdos213.TwistedHyperbola

def normSq (N x y : ℚ) : ℚ := x^2+N*y^2

def productCondition (N a b : ℚ) : Prop := IsSquare ((a*b)^2+N)

def distanceSq (N a b : ℚ) : ℚ := (a-b)^2+N*(a⁻¹-b⁻¹)^2

lemma distance_factor (N a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    distanceSq N a b = ((a-b)/(a*b))^2*((a*b)^2+N) := by
  unfold distanceSq
  field_simp
  ring

lemma distance_square_iff (N a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    IsSquare (distanceSq N a b) ↔ productCondition N a b := by
  rw [distance_factor N a b ha hb]
  unfold productCondition
  have hc : (a-b)/(a*b) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hab) (mul_ne_zero ha hb)
  constructor
  · intro h
    have hh := h.div (IsSquare.sq ((a-b)/(a*b)))
    simpa only [mul_div_cancel_left₀ _ (pow_ne_zero 2 hc)] using hh
  · rintro ⟨r,hr⟩
    refine ⟨((a-b)/(a*b))*r,?_⟩
    rw [hr]
    ring

lemma sign_invariant (N a b : ℚ) :
    productCondition N (-a) b ↔ productCondition N a b := by
  unfold productCondition
  simp

lemma self_criterion (N a : ℚ) (ha : a ≠ 0) :
    IsSquare (distanceSq N a (-a)) ↔ IsSquare (a^4+N) := by
  have hne : a ≠ -a := by intro h; apply ha; linarith
  rw [distance_square_iff N a (-a) ha (neg_ne_zero.mpr ha) hne]
  unfold productCondition
  convert Iff.rfl using 2
  ring

def twist (b : ℚ) : ℚ := (b^8-2*b^6-b^4-2*b^2+1)/(4*b^2)
def root0 (b : ℚ) : ℚ := (b^4-b^2-1)/(2*b)
def root1 (b : ℚ) : ℚ := (b^4-b^2+1)/(2*b)
def root2 (b : ℚ) : ℚ := (b^4+b^2-1)/(2*b)

lemma seed_identities (b : ℚ) (hb : b ≠ 0) :
    1+twist b=(root0 b)^2 ∧ b^2+twist b=(root1 b)^2 ∧
      b^4+twist b=(root2 b)^2 := by
  dsimp [twist,root0,root1,root2]
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

lemma seed_conditions (b : ℚ) (hb : b ≠ 0) :
    productCondition (twist b) 1 1 ∧ productCondition (twist b) 1 b ∧
      productCondition (twist b) b b := by
  obtain ⟨h0,h1,h2⟩ := seed_identities b hb
  refine ⟨⟨root0 b,?_⟩,⟨root1 b,?_⟩,⟨root2 b,?_⟩⟩
  · simpa [productCondition,pow_two] using h0
  · simpa [productCondition,pow_two] using h1
  · simpa [productCondition,pow_succ,mul_assoc] using h2

/-- The pure-imaginary part of the complex square of (a,sqrt(N)/a)
is independent of a. Consequently the differences of any three such squares
are collinear: this obstructs the usual quadratic central-six-to-seven map. -/
lemma squared_imaginary_constant (a : ℚ) (ha : a ≠ 0) : 2*a*a⁻¹=2 := by
  field_simp

lemma reciprocal_parameter_twist (b : ℚ) (hb : b ≠ 0) :
    twist b⁻¹=twist b/b^4 := by
  dsimp [twist]
  field_simp
  ring

lemma control : twist 2=105/16 ∧ root0 2=11/4 ∧ root1 2=13/4 ∧ root2 2=19/4 := by
  norm_num [twist,root0,root1,root2]

def firstLift (b : ℚ) : ℚ := (b^8-2*b^7+b^4-2*b+1)/(4*b^3*(b-1))
def liftRoot1 (b : ℚ) : ℚ := (b^8-2*b^7+2*b^6-3*b^4+2*b-1)/(4*b^3*(b-1))
def liftRoot2 (b : ℚ) : ℚ := (b^8-2*b^7+3*b^4-2*b^2+2*b-1)/(4*b^2*(b-1))

set_option maxHeartbeats 2000000 in
lemma first_lift_identities (b : ℚ) (hb : b ≠ 0) (hb1 : b ≠ 1) :
    (firstLift b)^2+twist b=(liftRoot1 b)^2 ∧
      (b*firstLift b)^2+twist b=(liftRoot2 b)^2 := by
  have hb' : b-1 ≠ 0 := sub_ne_zero.mpr hb1
  dsimp [firstLift,twist,liftRoot1,liftRoot2]
  constructor <;> field_simp <;> ring

def quotientF (u : ℚ) : ℚ := u^4-2*u^3-4*u^2+6*u+3
def quotientH (u : ℚ) : ℚ := (quotientF u)^4+64*(u-2)^2*(u^2-1)*(u^2-5)

set_option maxHeartbeats 2000000 in
lemma first_lift_quotient (b : ℚ) (hb : b ≠ 0) (hb1 : b ≠ 1) :
    ((firstLift b)^4+twist b)*(16*(b-1)^2/b^2)^2=quotientH (b+b⁻¹) ∧
      (b+b⁻¹)^2-4=(b-b⁻¹)^2 := by
  have hb' : b-1 ≠ 0 := sub_ne_zero.mpr hb1
  constructor
  · dsimp [firstLift,twist,quotientH,quotientF]
    field_simp
    ring
  · field_simp
    ring

lemma first_lift_control :
    firstLift 2=13/32 ∧ liftRoot1 2=83/32 ∧ liftRoot2 2=43/16 ∧
      ¬ IsSquare ((firstLift 2)^4+twist 2) := by
  norm_num [firstLift,liftRoot1,liftRoot2,twist]

/-- The real and scaled imaginary coordinates of the complex square. -/
def squarePoint (N a : ℚ) : ℚ × ℚ := (a^2-N*a⁻¹^2,2*a*a⁻¹)

/-- Three squared hyperbola points have a zero planar determinant.
This is an obstruction to applying the usual quadratic seven-point template. -/
lemma squared_triangle_zero (N a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((squarePoint N b).1-(squarePoint N a).1)*
      ((squarePoint N c).2-(squarePoint N a).2)-
    ((squarePoint N b).2-(squarePoint N a).2)*
      ((squarePoint N c).1-(squarePoint N a).1)=0 := by
  simp only [squarePoint,squared_imaginary_constant _ ha,
    squared_imaginary_constant _ hb,squared_imaginary_constant _ hc,sub_self,mul_zero,zero_mul]

def controlParameter : Fin 5 → ℚ := ![1,-1,2,-2,13/32]

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 10000 in
lemma five_parameter_control :
    Function.Injective controlParameter ∧ (∀ i, controlParameter i ≠ 0) ∧
    (∀ i j, i ≠ j → productCondition (105/16) (controlParameter i) (controlParameter j)) ∧
    (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      controlParameter i*controlParameter j*controlParameter k*controlParameter l ≠ 105/16) := by
  unfold productCondition
  decide +kernel

def det3 (a b c d e f g h i : ℚ) : ℚ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
def triangle (a b c : ℚ) : ℚ :=
  (b-a)*(c⁻¹-a⁻¹)-(b⁻¹-a⁻¹)*(c-a)
def circle (N a b c d : ℚ) : ℚ :=
  det3 (b-a) (b⁻¹-a⁻¹) (distanceSq N a b)
    (c-a) (c⁻¹-a⁻¹) (distanceSq N a c)
    (d-a) (d⁻¹-a⁻¹) (distanceSq N a d)

lemma triangle_factor (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    triangle a b c*(a*b*c)=-(a-b)*(a-c)*(b-c) := by
  dsimp [triangle]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
lemma circle_factor (N a b c d : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) :
    circle N a b c d*(a^2*b^2*c^2*d^2)=
      (a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)*(a*b*c*d-N) := by
  dsimp [circle,det3,distanceSq]
  field_simp
  ring

lemma seed_twist_gt (b : ℚ) (hb : 2 ≤ b) : b^2 < twist b := by
  have hb0 : b ≠ 0 := by linarith
  have hq : 0 ≤ b^2-4 := by nlinarith
  unfold twist
  apply (lt_div_iff₀ (show 0 < 4*b^2 by positivity)).mpr
  apply sub_pos.mp
  rw [show b^8-2*b^6-b^4-2*b^2+1-b^2*(4*b^2) =
    (b^2-4)^4+14*(b^2-4)^3+67*(b^2-4)^2+118*(b^2-4)+41 by ring]
  positivity

#print axioms seed_twist_gt

#print axioms triangle_factor
#print axioms circle_factor

#print axioms first_lift_identities
#print axioms first_lift_quotient
#print axioms first_lift_control
#print axioms squared_triangle_zero
#print axioms five_parameter_control

#print axioms distance_square_iff
#print axioms self_criterion
#print axioms seed_conditions
#print axioms reciprocal_parameter_twist
#print axioms control
end Erdos213.TwistedHyperbola
