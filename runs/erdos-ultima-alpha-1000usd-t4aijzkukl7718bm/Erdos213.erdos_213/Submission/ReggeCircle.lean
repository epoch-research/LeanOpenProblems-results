import Submission.ReggeMixed

/-! A homogeneous invariant for Regge orbits of cyclic quadrilaterals.
This file is about a special construction family, not arbitrary integral
configurations. Unlike perimeter preservation, the invariant allows an
independent rescaling of each quadruple. -/
namespace Erdos213.ReggeCircle
open ReggeMixed

/-- Three Ptolemy forms and six parallel-edge forms. -/
noncomputable def form (e : Edges) : Fin 9 → ℝ :=
  let a := e 0; let b := e 1; let d := e 2
  let c := e 3; let t := e 4; let f := e 5
  ![a*f+b*t-c*d, a*f-b*t+c*d, a*f-b*t-c*d,
    a*f+(b^2-c^2-d^2+t^2)/2, a*f-(b^2-c^2-d^2+t^2)/2,
    b*t+(a^2-c^2-d^2+f^2)/2, b*t-(a^2-c^2-d^2+f^2)/2,
    c*d+(a^2-b^2-t^2+f^2)/2, c*d-(a^2-b^2-t^2+f^2)/2]

def Special (e : Edges) : Prop := ∃ i, form e i = 0

/-- Adjacent vertex transpositions, in edge order AB, AC, AD, BC, BD, CD. -/
def relabel (k : Fin 3) (e : Edges) : Edges :=
  ![ ![e 0,e 3,e 4,e 1,e 2,e 5],
     ![e 1,e 0,e 2,e 3,e 5,e 4],
     ![e 0,e 2,e 1,e 4,e 3,e 5] ] k

private def moveIndex : Fin 3 → Fin 9 → Fin 9 :=
  !![4,3,2,1,0,7,6,5,8; 6,1,5,8,4,2,0,7,3; 0,8,7,3,6,5,4,2,1]
private def moveSign : Fin 3 → Fin 9 → ℤ :=
  !![1,1,1,1,1,1,1,1,1; 1,1,-1,1,1,-1,1,1,1; 1,1,-1,1,1,1,1,-1,1]
private def labelIndex : Fin 3 → Fin 9 → Fin 9 :=
  !![1,0,2,4,3,7,8,5,6; 0,2,1,5,6,3,4,8,7; 1,0,2,4,3,7,8,5,6]
private def labelSign : Fin 3 → Fin 9 → ℤ :=
  !![1,1,1,1,1,1,1,1,1; 1,-1,-1,1,1,1,1,1,1; 1,1,1,1,1,1,1,1,1]

set_option maxHeartbeats 2000000 in
lemma form_move (k : Fin 3) (e : Edges) (i : Fin 9) :
    form (move k e) i = (moveSign k i : ℝ) * form e (moveIndex k i) := by
  fin_cases k <;> fin_cases i
  · change (e 0)*(e 5)+(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2)) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 0)*(e 5)-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))+(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2)) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 0)*(e 5)-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2)) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)+((((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2))^2+(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)+(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)-((((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2))^2+(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))+((e 0)^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2))^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)+((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))-((e 0)^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2))^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2))+((e 0)^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (((e 1)+(e 2)+(e 3)+(e 4))/2-(e 3))*(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 2))-((e 0)^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 1))^2-(((e 1)+(e 2)+(e 3)+(e 4))/2-(e 4))^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)-((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))+(e 1)*(e 4)-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2)) = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))-(e 1)*(e 4)+(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2)) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)+(e 3)*(e 2))
    ring
  · change (((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))-(e 1)*(e 4)-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2)) = ((-1 : ℤ) : ℝ) * ((e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))+((e 1)^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2))^2+(e 4)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)-((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))-((e 1)^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2))^2+(e 4)^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 1)*(e 4)+((((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2))^2+(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))^2)/2 = ((-1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 1)*(e 4)-((((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))^2-(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2))^2+(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2))+((((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))^2-(e 1)^2-(e 4)^2+(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)+((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 2)+(e 3)+(e 5))/2-(e 3))*(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 2))-((((e 0)+(e 2)+(e 3)+(e 5))/2-(e 0))^2-(e 1)^2-(e 4)^2+(((e 0)+(e 2)+(e 3)+(e 5))/2-(e 5))^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))+(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))-(e 3)*(e 2) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))-(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))+(e 3)*(e 2) = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)-((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))-(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))-(e 3)*(e 2) = ((-1 : ℤ) : ℝ) * ((e 3)*(e 2)+((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))+((((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))^2-(e 3)^2-(e 2)^2+(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))-((((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))^2-(e 3)^2-(e 2)^2+(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))+((((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))^2-(e 3)^2-(e 2)^2+(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))*(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))-((((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))^2-(e 3)^2-(e 2)^2+(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 3)*(e 2)+((((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))^2-(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))^2-(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))^2+(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))^2)/2 = ((-1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 3)*(e 2)-((((e 0)+(e 1)+(e 4)+(e 5))/2-(e 0))^2-(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 1))^2-(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 4))^2+(((e 0)+(e 1)+(e 4)+(e 5))/2-(e 5))^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)+(e 3)*(e 2))
    ring

set_option maxHeartbeats 2000000 in
lemma form_relabel (k : Fin 3) (e : Edges) (i : Fin 9) :
    form (relabel k e) i = (labelSign k i : ℝ) * form e (labelIndex k i) := by
  fin_cases k <;> fin_cases i
  · change (e 0)*(e 5)+(e 3)*(e 2)-(e 1)*(e 4) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)+(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)-(e 3)*(e 2)+(e 1)*(e 4) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)-(e 3)*(e 2)-(e 1)*(e 4) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)+((e 3)^2-(e 1)^2-(e 4)^2+(e 2)^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 0)*(e 5)-((e 3)^2-(e 1)^2-(e 4)^2+(e 2)^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 3)*(e 2)+((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)+((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (e 3)*(e 2)-((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)-((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (e 1)*(e 4)+(e 0)*(e 5)-(e 3)*(e 2) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 1)*(e 4)-(e 0)*(e 5)+(e 3)*(e 2) = ((-1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 1)*(e 4)-(e 0)*(e 5)-(e 3)*(e 2) = ((-1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)+(e 3)*(e 2))
    ring
  · change (e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (e 0)*(e 5)+((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 0)*(e 5)-((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 3)*(e 2)+((e 1)^2-(e 0)^2-(e 5)^2+(e 4)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)-((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (e 3)*(e 2)-((e 1)^2-(e 0)^2-(e 5)^2+(e 4)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)+((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (e 0)*(e 5)+(e 2)*(e 3)-(e 4)*(e 1) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)+(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)-(e 2)*(e 3)+(e 4)*(e 1) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)-(e 2)*(e 3)-(e 4)*(e 1) = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-(e 1)*(e 4)-(e 3)*(e 2))
    ring
  · change (e 0)*(e 5)+((e 2)^2-(e 4)^2-(e 1)^2+(e 3)^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)-((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 0)*(e 5)-((e 2)^2-(e 4)^2-(e 1)^2+(e 3)^2)/2 = ((1 : ℤ) : ℝ) * ((e 0)*(e 5)+((e 1)^2-(e 3)^2-(e 2)^2+(e 4)^2)/2)
    ring
  · change (e 2)*(e 3)+((e 0)^2-(e 4)^2-(e 1)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)+((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (e 2)*(e 3)-((e 0)^2-(e 4)^2-(e 1)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 3)*(e 2)-((e 0)^2-(e 1)^2-(e 4)^2+(e 5)^2)/2)
    ring
  · change (e 4)*(e 1)+((e 0)^2-(e 2)^2-(e 3)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)+((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring
  · change (e 4)*(e 1)-((e 0)^2-(e 2)^2-(e 3)^2+(e 5)^2)/2 = ((1 : ℤ) : ℝ) * ((e 1)*(e 4)-((e 0)^2-(e 3)^2-(e 2)^2+(e 5)^2)/2)
    ring

lemma moveIndex_involutive (k : Fin 3) (i : Fin 9) :
    moveIndex k (moveIndex k i) = i := by fin_cases k <;> fin_cases i <;> decide
lemma labelIndex_involutive (k : Fin 3) (i : Fin 9) :
    labelIndex k (labelIndex k i) = i := by fin_cases k <;> fin_cases i <;> decide

lemma special_move {e : Edges} (h : Special e) (k : Fin 3) : Special (move k e) := by
  obtain ⟨i,hi⟩ := h
  refine ⟨moveIndex k i,?_⟩
  rw [form_move,moveIndex_involutive,hi,mul_zero]

lemma special_relabel {e : Edges} (h : Special e) (k : Fin 3) : Special (relabel k e) := by
  obtain ⟨i,hi⟩ := h
  refine ⟨labelIndex k i,?_⟩
  rw [form_relabel,labelIndex_involutive,hi,mul_zero]

lemma form_scale (e : Edges) (c : ℝ) (i : Fin 9) :
    form (fun j => c*e j) i = c^2*form e i := by
  fin_cases i <;> simp [form,Matrix.cons_val] <;> ring

lemma special_scale {e : Edges} (h : Special e) (c : ℝ) : Special (fun j => c*e j) := by
  obtain ⟨i,hi⟩ := h
  exact ⟨i,by rw [form_scale,hi,mul_zero]⟩

/-- The vertex transpositions generate all vertex permutations. Arbitrary
edge permutations, which need not preserve the invariant, are NOT included.
Scales and move words can be chosen independently for each quadruple. -/
inductive Orbit : Edges → Edges → Prop
  | refl (e) : Orbit e e
  | relabel (e) (k) : Orbit e (ReggeCircle.relabel k e)
  | regge (e) (k) : Orbit e (move k e)
  | scale (e) (c : ℝ) : Orbit e (fun j => c*e j)
  | trans {e f g} : Orbit e f → Orbit f g → Orbit e g

lemma special_orbit {e f : Edges} (h : Orbit e f) (he : Special e) : Special f := by
  induction h with
  | refl => exact he
  | relabel e k => exact special_relabel he k
  | regge e k => exact special_move he k
  | scale e c => exact special_scale he c
  | trans _ _ h₁ h₂ => exact h₂ (h₁ he)

/-- Coordinates relative to the first vertex at the origin. -/
def circle (x y u v z w : ℝ) : ℝ :=
  x*(v*(z^2+w^2)-(u^2+v^2)*w) -
  y*(u*(z^2+w^2)-(u^2+v^2)*z) + (x^2+y^2)*(u*w-v*z)

def parallel (x y u v z w : ℝ) : Fin 3 → ℝ :=
  ![x*(w-v)-y*(z-u), u*(w-y)-v*(z-x), z*(v-y)-w*(u-x)]

def Realizes (e : Edges) (x y u v z w : ℝ) : Prop :=
  e 0^2=x^2+y^2 ∧ e 1^2=u^2+v^2 ∧ e 2^2=z^2+w^2 ∧
  e 3^2=(u-x)^2+(v-y)^2 ∧ e 4^2=(z-x)^2+(w-y)^2 ∧
  e 5^2=(z-u)^2+(w-v)^2

lemma ptolemy_identity (e : Edges) (x y u v z w : ℝ)
    (h : Realizes e x y u v z w) :
    (e 0*e 5+e 1*e 4+e 2*e 3)*form e 0*form e 1*form e 2 =
      -4*circle x y u v z w^2 := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h
  calc
    _ = (e 0^2*e 5^2)^2+(e 1^2*e 4^2)^2+(e 2^2*e 3^2)^2 -
        2*(e 0^2*e 5^2*e 1^2*e 4^2 + e 0^2*e 5^2*e 2^2*e 3^2 +
        e 1^2*e 4^2*e 2^2*e 3^2) := by simp [form,Matrix.cons_val]; ring
    _ = _ := by rw [h0,h1,h2,h3,h4,h5]; dsimp [circle]; ring

lemma parallel_identity (e : Edges) (x y u v z w : ℝ)
    (h : Realizes e x y u v z w) :
    form e 3*form e 4 = parallel x y u v z w 0^2 ∧
    form e 5*form e 6 = parallel x y u v z w 1^2 ∧
    form e 7*form e 8 = parallel x y u v z w 2^2 := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h
  have hp (a b c : ℝ) : (a*b+c/2)*(a*b-c/2) = a^2*b^2-c^2/4 := by ring
  simp only [form,parallel,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val,Matrix.head_cons,
    Matrix.tail_cons]
  simp only [hp,h0,h1,h2,h3,h4,h5]
  constructor
  · ring
  constructor <;> ring

lemma special_of_circle (e : Edges) (x y u v z w : ℝ)
    (h : Realizes e x y u v z w) (hpos : ∀ i, 0 < e i)
    (hc : circle x y u v z w = 0) : Special e := by
  have hh := ptolemy_identity e x y u v z w h
  have hs : e 0*e 5+e 1*e 4+e 2*e 3 ≠ 0 :=
    ne_of_gt (add_pos (add_pos (mul_pos (hpos 0) (hpos 5))
      (mul_pos (hpos 1) (hpos 4))) (mul_pos (hpos 2) (hpos 3)))
  rw [hc] at hh
  simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,mul_eq_zero,hs,false_or] at hh
  rcases hh with (h0 | h1) | h2
  · exact ⟨0,h0⟩
  · exact ⟨1,h1⟩
  · exact ⟨2,h2⟩

lemma circle_or_parallel (e : Edges) (x y u v z w : ℝ)
    (h : Realizes e x y u v z w) (hs : Special e) :
    circle x y u v z w = 0 ∨ ∃ k, parallel x y u v z w k = 0 := by
  have hp := ptolemy_identity e x y u v z w h
  obtain ⟨h0,h1,h2⟩ := parallel_identity e x y u v z w h
  obtain ⟨i,hi⟩ := hs
  fin_cases i
  · change form e 0 = 0 at hi
    left
    rw [hi] at hp
    simp only [mul_zero,zero_mul] at hp
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hp.symm).resolve_left (by norm_num))
  · change form e 1 = 0 at hi
    left
    rw [hi] at hp
    simp only [mul_zero,zero_mul] at hp
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hp.symm).resolve_left (by norm_num))
  · change form e 2 = 0 at hi
    left
    rw [hi] at hp
    simp only [mul_zero,zero_mul] at hp
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hp.symm).resolve_left (by norm_num))
  · change form e 3 = 0 at hi
    right
    refine ⟨0,?_⟩
    rw [hi] at h0
    simp only [mul_zero,zero_mul] at h0
    exact sq_eq_zero_iff.mp h0.symm
  · change form e 4 = 0 at hi
    right
    refine ⟨0,?_⟩
    rw [hi] at h0
    simp only [mul_zero,zero_mul] at h0
    exact sq_eq_zero_iff.mp h0.symm
  · change form e 5 = 0 at hi
    right
    refine ⟨1,?_⟩
    rw [hi] at h1
    simp only [mul_zero,zero_mul] at h1
    exact sq_eq_zero_iff.mp h1.symm
  · change form e 6 = 0 at hi
    right
    refine ⟨1,?_⟩
    rw [hi] at h1
    simp only [mul_zero,zero_mul] at h1
    exact sq_eq_zero_iff.mp h1.symm
  · change form e 7 = 0 at hi
    right
    refine ⟨2,?_⟩
    rw [hi] at h2
    simp only [mul_zero,zero_mul] at h2
    exact sq_eq_zero_iff.mp h2.symm
  · change form e 8 = 0 at hi
    right
    refine ⟨2,?_⟩
    rw [hi] at h2
    simp only [mul_zero,zero_mul] at h2
    exact sq_eq_zero_iff.mp h2.symm

#print axioms form_move
#print axioms form_relabel
#print axioms special_orbit
#print axioms ptolemy_identity
#print axioms parallel_identity
#print axioms special_of_circle
#print axioms circle_or_parallel
end Erdos213.ReggeCircle
