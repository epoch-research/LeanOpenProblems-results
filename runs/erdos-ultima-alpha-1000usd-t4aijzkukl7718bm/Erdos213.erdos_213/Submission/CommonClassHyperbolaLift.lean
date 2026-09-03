import Submission.CommonClassHyperbola

/-! A verified five-point extension in the common-square-class-two family.
The additional self-distance needed for an antipodal lift is not automatic. -/
namespace Erdos213.CommonClassHyperbola

def liftDen (b : ℚ) : ℚ :=
  b^8-8*b^7+20*b^6-24*b^5-26*b^4+104*b^3-44*b^2-8*b+1
def liftNum (b : ℚ) : ℚ :=
  b^9-2*b^8-12*b^7+32*b^6+6*b^5-52*b^4-12*b^3+48*b^2-31*b+6
def liftRootNum1 (b : ℚ) : ℚ :=
  b^10-8*b^9+21*b^8+16*b^7-118*b^6+96*b^5-22*b^4-16*b^3+133*b^2-88*b+17
def liftRootNum2 (b : ℚ) : ℚ :=
  3*b^10-8*b^9-21*b^8+48*b^7+110*b^6-256*b^5+38*b^4+208*b^3-97*b^2+8*b-1
def firstLift (b : ℚ) : ℚ := liftNum b/liftDen b
def firstRoot1 (b : ℚ) : ℚ := liftRootNum1 b/(2*liftDen b)
def firstRoot2 (b : ℚ) : ℚ := liftRootNum2 b/(2*liftDen b)

set_option maxHeartbeats 2000000 in
lemma first_lift_identities (b : ℚ) (hd : liftDen b ≠ 0) :
    2*((firstLift b)^2+twist b)=(firstRoot1 b)^2 ∧
    2*(b^2*(firstLift b)^2+twist b)=(firstRoot2 b)^2 := by
  dsimp only [firstLift,firstRoot1,firstRoot2]
  constructor <;> field_simp <;>
    dsimp [liftNum,liftDen,liftRootNum1,liftRootNum2,twist] <;> ring

lemma first_lift_control :
    firstLift 3 = -57/119 ∧ firstRoot1 3 = -325/119 ∧ firstRoot2 3 = -397/119 ∧
      ¬ IsSquare (2*((firstLift 3)^4+twist 3)) := by
  decide +kernel

def fiveParameter : Fin 5 → ℚ := ![-1,1,-3,3,-57/119]
def fivePoint : Fin 5 → ℚ × ℚ :=
  ![(-61047,0),(61047,0),(-56525,18088),(56525,-18088),(-105625,-10912)]
def fiveDistance : Fin 5 → Fin 5 → ℕ := fun i j =>
  !![0,122094,67830,135660,60450;
     122094,0,135660,67830,171600;
     67830,135660,0,176358,119100;
     135660,67830,176358,0,164358;
     60450,171600,119100,164358,0] i j

lemma five_point_parameter_link : ∀ i,
    fivePoint i=(40698*(point 3 (fiveParameter i)).1,20349*(point 3 (fiveParameter i)).2) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
set_option synthInstance.maxSize 10000 in
lemma five_point_certificate :
    Function.Injective fivePoint ∧
    (∀ i j, OffsetCircle.distSq 14 (fivePoint i) (fivePoint j)=(fiveDistance i j : ℚ)^2) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      OffsetCircle.triangle (fivePoint i) (fivePoint j) (fivePoint k) ≠ 0) ∧
    (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      OffsetCircle.circle 14 (fivePoint i) (fivePoint j) (fivePoint k) (fivePoint l) ≠ 0) := by
  decide +kernel

#print axioms first_lift_identities
#print axioms first_lift_control
#print axioms five_point_parameter_link
#print axioms five_point_certificate
end Erdos213.CommonClassHyperbola
