import Submission.ReggeCircle
import Submission.CircleCoverReduction

/-! The cyclic-or-parallel Regge invariant prevents general position of
an eight-vertex planar subset-sum cube. This is a construction-family
obstruction, not a bound for arbitrary integral-distance sets. -/
open EuclideanGeometry
namespace Erdos213.ReggeCubeObstruction
open ReggeCircle ReggeMixed InversionReduction CircleCoverReduction
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

lemma generalized_of_circleEval_zero {a b c d : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : circleEval a b c d=0) : OnGeneralizedCircle {a,b,c,d} := by
  apply generalized_mono (circleEval_generalized hab hac hbc)
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp | hp
  · rw [hp]
    change circleEval a b c a=0
    simp [circleEval,ca,cb,cc,qnorm,dx,dy]
  · rw [hp]
    change circleEval a b c b=0
    unfold circleEval ca cb cc
    ring
  · rw [hp]
    change circleEval a b c c=0
    unfold circleEval ca cb cc
    ring
  · simpa only [hp] using h

lemma circleEval_ne_of_noFour {n : ℕ} {p : Fin n → ℝ²}
    (hinj : Function.Injective p) (hgp : NoFourGeneralized (Set.range p))
    (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    circleEval (p i) (p j) (p k) (p l) ≠ 0 := by
  intro h
  have hab : p i ≠ p j := fun he => hij (hinj he)
  have hac : p i ≠ p k := fun he => hik (hinj he)
  have had : p i ≠ p l := fun he => hil (hinj he)
  have hbc : p j ≠ p k := fun he => hjk (hinj he)
  have hbd : p j ≠ p l := fun he => hjl (hinj he)
  have hcd : p k ≠ p l := fun he => hkl (hinj he)
  apply hgp {p i,p j,p k,p l} ?_ ?_
    (generalized_of_circleEval_zero hab hac hbc h)
  · intro q hq
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
  · exact Set.ncard_eq_four.mpr ⟨p i,p j,p k,p l,hab,hac,had,hbc,hbd,hcd,rfl⟩

/-- All eight subset sums of three plane vectors. -/
def vertex (u v w : ℝ²) : Fin 8 → ℝ² :=
  ![0,u,v,w,u+v,u+w,v+w,u+v+w]

/-- The six edge lengths of the alternating-vertex quadrilateral, realized
at vertices 0, u+v, u+w, v+w. There is no length-integrality hypothesis. -/
def AlternatingRealizes (e : Edges) (u v w : ℝ²) : Prop :=
  Realizes e (u 0+v 0) (u 1+v 1) (u 0+w 0) (u 1+w 1)
    (v 0+w 0) (v 1+w 1)

lemma alternating_circle (u v w : ℝ²) :
    circleEval (vertex u v w 0) (vertex u v w 4)
      (vertex u v w 5) (vertex u v w 6) =
    ReggeCircle.circle (u 0+v 0) (u 1+v 1) (u 0+w 0) (u 1+w 1)
      (v 0+w 0) (v 1+w 1) := by
  simp only [vertex,Matrix.cons_val,
    PiLp.zero_apply,PiLp.add_apply,circleEval,ca,cb,cc,qnorm,dx,dy,ReggeCircle.circle]
  ring

lemma first_face_circle (u v w : ℝ²) :
    circleEval (vertex u v w 0) (vertex u v w 2)
      (vertex u v w 3) (vertex u v w 6) =
    parallel (u 0+v 0) (u 1+v 1) (u 0+w 0) (u 1+w 1)
      (v 0+w 0) (v 1+w 1) 2 * (v 0*w 0+v 1*w 1) := by
  simp only [vertex,parallel,Matrix.cons_val,
    PiLp.zero_apply,PiLp.add_apply,circleEval,ca,cb,cc,qnorm,dx,dy]
  ring

lemma second_face_circle (u v w : ℝ²) :
    circleEval (vertex u v w 0) (vertex u v w 1)
      (vertex u v w 3) (vertex u v w 5) =
    parallel (u 0+v 0) (u 1+v 1) (u 0+w 0) (u 1+w 1)
      (v 0+w 0) (v 1+w 1) 1 * (u 0*w 0+u 1*w 1) := by
  simp only [vertex,parallel,Matrix.cons_val,
    PiLp.zero_apply,PiLp.add_apply,circleEval,ca,cb,cc,qnorm,dx,dy]
  ring

lemma third_face_circle (u v w : ℝ²) :
    circleEval (vertex u v w 0) (vertex u v w 1)
      (vertex u v w 2) (vertex u v w 4) =
    parallel (u 0+v 0) (u 1+v 1) (u 0+w 0) (u 1+w 1)
      (v 0+w 0) (v 1+w 1) 0 * (u 0*v 0+u 1*v 1) := by
  simp only [vertex,parallel,Matrix.cons_val,
    PiLp.zero_apply,PiLp.add_apply,circleEval,ca,cb,cc,qnorm,dx,dy]
  ring

/-- A special alternating quadrilateral forces four of the cube vertices
onto a generalized circle. Distinctness is essential for the cardinality. -/
theorem special_cube_not_noFour {e : Edges} {u v w : ℝ²}
    (he : AlternatingRealizes e u v w) (hs : Special e)
    (hinj : Function.Injective (vertex u v w)) :
    ¬ NoFourGeneralized (Set.range (vertex u v w)) := by
  intro hgp
  have hquad := circleEval_ne_of_noFour hinj hgp
  rcases circle_or_parallel e _ _ _ _ _ _ he hs with hc | ⟨k,hk⟩
  · apply hquad 0 4 5 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [alternating_circle,hc]
  · fin_cases k
    · apply hquad 0 1 2 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
      rw [third_face_circle]
      change parallel _ _ _ _ _ _ 0=0 at hk
      rw [hk,zero_mul]
    · apply hquad 0 1 3 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
      rw [second_face_circle]
      change parallel _ _ _ _ _ _ 1=0 at hk
      rw [hk,zero_mul]
    · apply hquad 0 2 3 6 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
      rw [first_face_circle]
      change parallel _ _ _ _ _ _ 2=0 at hk
      rw [hk,zero_mul]

theorem special_cube_not_general_position {e : Edges} {u v w : ℝ²}
    (he : AlternatingRealizes e u v w) (hs : Special e)
    (hinj : Function.Injective (vertex u v w)) :
    ¬ InGeneralPosition (Set.range (vertex u v w)) := by
  intro hgp
  exact special_cube_not_noFour he hs hinj (noFour_of_general_position hgp)

/-- This obstruction survives every finite composition of Regge moves,
vertex relabelings, and scalings allowed by the verified orbit relation. -/
theorem orbit_cube_not_general_position {e f : Edges} {u v w : ℝ²}
    (horbit : ReggeCircle.Orbit e f) (hs : Special e) (he : AlternatingRealizes f u v w)
    (hinj : Function.Injective (vertex u v w)) :
    ¬ InGeneralPosition (Set.range (vertex u v w)) :=
  special_cube_not_general_position he (special_orbit horbit hs) hinj

/-- Alternating quadrilateral of the fixed integral grid, in edge order
AB, AC, AD, BC, BD, CD. -/
def gridEdges : Edges := ![782,436,482,482,436,54]

lemma grid_special : Special gridEdges := by
  refine ⟨0,?_⟩
  change (782 : ℝ)*54+436*436-482*482=0
  norm_num

lemma grid_realizes : AlternatingRealizes gridEdges
    !₂[364,0] !₂[418,0] !₂[0,240] := by
  simp only [AlternatingRealizes,Realizes,gridEdges,Matrix.cons_val,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num

/-- No eight-distinct-vertex cube reconstructed from this grid's Regge orbit
can be in general position, regardless of its other distance properties. -/
theorem grid_orbit_cube_not_general_position {e : Edges} {u v w : ℝ²}
    (horbit : ReggeCircle.Orbit gridEdges e) (he : AlternatingRealizes e u v w)
    (hinj : Function.Injective (vertex u v w)) :
    ¬ InGeneralPosition (Set.range (vertex u v w)) :=
  orbit_cube_not_general_position horbit grid_special he hinj

#print axioms generalized_of_circleEval_zero
#print axioms special_cube_not_noFour
#print axioms special_cube_not_general_position
#print axioms orbit_cube_not_general_position
#print axioms grid_realizes
#print axioms grid_orbit_cube_not_general_position
end
end Erdos213.ReggeCubeObstruction
