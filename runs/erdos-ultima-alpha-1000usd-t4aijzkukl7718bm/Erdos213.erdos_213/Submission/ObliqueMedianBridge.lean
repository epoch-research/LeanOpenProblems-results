import Submission.MedianFlipClosure

/-! Exact metric criterion for the oblique 3-by-3 grid: its two diagonal
triangles must both have rational sides and rational medians. Their existence
is not asserted; in fact the second triangle is outside the automatic median
orbit of the first when the metric is positive definite. -/
namespace Erdos213.ObliqueMedianBridge
open MedianFlipClosure
set_option maxHeartbeats 2000000

/-- Binary squared norm of an oblique basis with Gram entries A,H,B. -/
def norm (A B H x y : ℚ) : ℚ := A*x^2+2*H*x*y+B*y^2

def GridSquares (A B H : ℚ) : Prop := ∀ i j : Fin 3 × Fin 3,
  IsSquare (norm A B H ((i.1.val : ℚ)-j.1.val) ((i.2.val : ℚ)-j.2.val))

def Directions (A B H : ℚ) : Prop :=
  IsSquare A ∧ IsSquare B ∧ IsSquare (A+B+2*H) ∧ IsSquare (A+B-2*H) ∧
  IsSquare (4*A+B+4*H) ∧ IsSquare (4*A+B-4*H) ∧
  IsSquare (A+4*B+4*H) ∧ IsSquare (A+4*B-4*H)

lemma grid_iff_directions (A B H : ℚ) : GridSquares A B H ↔ Directions A B H := by
  constructor
  · intro h
    have hA := h (1,0) (0,0)
    have hB := h (0,1) (0,0)
    have hp := h (1,1) (0,0)
    have hm := h (1,0) (0,1)
    have h21 := h (2,1) (0,0)
    have h2m1 := h (2,0) (0,1)
    have h12 := h (1,2) (0,0)
    have h1m2 := h (1,0) (0,2)
    norm_num [norm] at hA hB hp hm h21 h2m1 h12 h1m2
    dsimp [Directions]
    ring_nf at hp hm h21 h2m1 h12 h1m2 ⊢
    exact ⟨hA,hB,hp,hm,h21,h2m1,h12,h1m2⟩
  · rintro ⟨hA,hB,hp,hm,h21,h2m1,h12,h1m2⟩ ⟨i,j⟩ ⟨k,l⟩
    have h4A := (IsSquare.sq (2 : ℚ)).mul hA
    have h4B := (IsSquare.sq (2 : ℚ)).mul hB
    have h4p := (IsSquare.sq (2 : ℚ)).mul hp
    have h4m := (IsSquare.sq (2 : ℚ)).mul hm
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> norm_num [norm]
    all_goals first
      | assumption
      | ring_nf at hp hm h21 h2m1 h12 h1m2 h4A h4B h4p h4m ⊢; assumption

def triangle (A B H : ℚ) : Triple := ![A,B,A+B+2*H]

lemma median_triangle (A B H : ℚ) :
    median (triangle A B H)=![A+4*B+4*H,4*A+B+4*H,A+B-2*H] := by
  ext i
  fin_cases i <;> simp [median,total,triangle,Fin.sum_univ_three,Matrix.cons_val_two]
  all_goals ring

lemma flip_triangle (A B H : ℚ) : flip (triangle A B H)=triangle A B (-H) := by
  ext i
  fin_cases i <;> simp [MedianFlipClosure.flip,triangle,Matrix.cons_val_two]
  ring

lemma heron_triangle (A B H : ℚ) : heron (triangle A B H)=4*(A*B-H^2) := by
  simp [heron_expanded,triangle,Matrix.cons_val_two]
  ring

lemma rational_medians_iff (A B H : ℚ) : RationalMedians (triangle A B H) ↔
    (IsSquare A ∧ IsSquare B ∧ IsSquare (A+B+2*H)) ∧
    (IsSquare (A+4*B+4*H) ∧ IsSquare (4*A+B+4*H) ∧ IsSquare (A+B-2*H)) := by
  unfold RationalMedians
  rw [median_triangle]
  simp [triangle,Fin.forall_fin_succ]

/-- This is an equivalence, not a merely sufficient direction list. Both
median triples are necessary; only two of the second triple's conditions
are new. -/
theorem grid_iff_two_median_triangles (A B H : ℚ) : GridSquares A B H ↔
    RationalMedians (triangle A B H) ∧ RationalMedians (flip (triangle A B H)) := by
  rw [grid_iff_directions,flip_triangle,rational_medians_iff,rational_medians_iff]
  simp only [Directions,mul_neg,sub_neg_eq_add]
  simp only [← sub_eq_add_neg]
  tauto

/-- If a positive-definite metric supplies a full grid at all, its two
rational-median triangles cannot be obtained from each other by the standard
median operations, regardless of how many times those operations are iterated. -/
theorem grid_requires_new_median_orbit {A B H : ℚ} (hpos : 0 < A*B-H^2)
    (hg : GridSquares A B H) :
    RationalMedians (triangle A B H) ∧ RationalMedians (flip (triangle A B H)) ∧
    ¬Reach (triangle A B H) (flip (triangle A B H)) := by
  obtain ⟨h1,h2⟩ := (grid_iff_two_median_triangles A B H).mp hg
  refine ⟨h1,h2,flip_not_reachable ?_ h1⟩
  rw [heron_triangle]
  exact ne_of_gt (mul_pos (by norm_num) hpos)

/-- The known rational-median source gives one diagonal triangle, but not
its flip. These exact values are only a control, not an exhaustive search. -/
lemma known_source_control :
    RationalMedians (triangle 1 (7225/7569) (-565/841)) ∧
    0 < 1*(7225/7569 : ℚ)-(-565/841)^2 ∧
    ¬RationalMedians (flip (triangle 1 (7225/7569) (-565/841))) := by
  rw [flip_triangle]
  simp only [rational_medians_iff]
  decide +kernel

#print axioms grid_iff_directions
#print axioms median_triangle
#print axioms grid_iff_two_median_triangles
#print axioms grid_requires_new_median_orbit
#print axioms known_source_control
end Erdos213.ObliqueMedianBridge
