import Submission.ExceptionalReciprocal

/-! Positive controls showing that the unscaled antipodal obstruction must not
be promoted to an obstruction after arbitrary common square-class dilation. -/
namespace Erdos213.OffsetCircle.Exceptional

def commonClassHyperbola : Fin 4 → ℚ × ℚ :=
  ![(9/8,7/8),(-9/8,-7/8),(177/224,-79/224),(-177/224,79/224)]
def commonClassSource : Fin 4 → ℚ × ℚ :=
  ![(4/5,7/5),(-4/13,7/13),(112/65,-79/65),(-112/289,-79/289)]
def commonClassSquares : Fin 4 → ℚ × ℚ :=
  ![(-33/25,56/25),(-33/169,-56/169),(6303/4225,-17696/4225),(6303/83521,17696/83521)]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
set_option synthInstance.maxSize 10000 in
lemma common_class_hyperbola_certificate :
    Function.Injective commonClassHyperbola ∧
    (∀ i, NonsplitHyperbola.lorentz 1 (commonClassHyperbola i)=1/2) ∧
    (∀ i j, IsSquare (distSq 1 (commonClassHyperbola i) (commonClassHyperbola j)/130)) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      triangle (commonClassHyperbola i) (commonClassHyperbola j) (commonClassHyperbola k) ≠ 0) ∧
    circle 1 (commonClassHyperbola 0) (commonClassHyperbola 1)
      (commonClassHyperbola 2) (commonClassHyperbola 3) ≠ 0 ∧
    commonClassHyperbola 1 = -commonClassHyperbola 0 ∧
    commonClassHyperbola 3 = -commonClassHyperbola 2 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
set_option synthInstance.maxSize 10000 in
lemma common_class_source_certificate :
    (∀ i, ((commonClassSource i).1-1)^2+(commonClassSource i).2^2=2) ∧
    (∀ i, squarePoint 1 (commonClassSource i).1 (commonClassSource i).2=commonClassSquares i) ∧
    (∀ i, hyperbolaPoint (commonClassSource i).1 (commonClassSource i).2=commonClassHyperbola i) ∧
    (∀ i j, IsSquare (distSq 1 (commonClassSquares i) (commonClassSquares j)/130)) ∧
    invSource (commonClassSource 0).1 (commonClassSource 0).2=commonClassSource 1 ∧
    invSource (commonClassSource 2).1 (commonClassSource 2).2=commonClassSource 3 := by
  decide +kernel

/-- The four squared-source images have one collinear triple. In particular,
they are not a new four-point general-position witness in this chart. -/
lemma common_class_source_geometry :
    triangle (commonClassSquares 0) (commonClassSquares 1) (commonClassSquares 2)=0 ∧
    triangle (commonClassSquares 0) (commonClassSquares 1) (commonClassSquares 3) ≠ 0 ∧
    circle 1 (commonClassSquares 0) (commonClassSquares 1)
      (commonClassSquares 2) (commonClassSquares 3) ≠ 0 := by
  decide +kernel

/-- The same hyperbola control is a similarity of this integral parallelogram. -/
def integralParallelogram : Fin 4 → ℚ × ℚ := ![(28,0),(-28,0),(8,15),(-8,-15)]
def controlSimilarity (p : ℚ × ℚ) : ℚ × ℚ := ((9*p.1+7*p.2)/224,(7*p.1-9*p.2)/224)

lemma common_class_control_similarity :
    (∀ i, controlSimilarity (integralParallelogram i)=commonClassHyperbola i) ∧
    (∀ i j, IsSquare (distSq 1 (integralParallelogram i) (integralParallelogram j))) := by
  decide +kernel

lemma control_similarity_norm (p q : ℚ × ℚ) :
    distSq 1 (controlSimilarity p) (controlSimilarity q)=130*distSq 1 p q/224^2 := by
  dsimp [distSq,normSq,controlSimilarity]
  ring

#print axioms common_class_hyperbola_certificate
#print axioms common_class_source_certificate
#print axioms common_class_source_geometry
#print axioms common_class_control_similarity
#print axioms control_similarity_norm
end Erdos213.OffsetCircle.Exceptional
