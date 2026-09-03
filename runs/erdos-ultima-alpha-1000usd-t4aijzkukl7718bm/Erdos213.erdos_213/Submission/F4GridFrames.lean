import Submission.ReggeCubeObstruction

/-! The six F4 four-vector frames all degenerate on a central two-row
rectangle, directly and after inversion. This is only a construction-family
obstruction and is not a disproof of Erdős 213. -/
open EuclideanGeometry
namespace Erdos213.F4GridFrames
open InversionReduction CircleCoverReduction ReggeCubeObstruction
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def source (x z h : ℝ) : Fin 4 → ℝ² :=
  ![!₂[x,h],!₂[z,h],!₂[-z,h],!₂[-x,h]]

/-- The coordinate, two spin, and three long-root orthogonal frames. -/
def frame (u : Fin 4 → ℝ²) : Fin 6 → Fin 4 → ℝ² :=
  ![ ![u 0,u 1,u 2,u 3],
     ![u 0-u 1-u 2+u 3,u 0-u 1+u 2-u 3,
       u 0+u 1-u 2-u 3,u 0+u 1+u 2+u 3],
     ![u 0-u 1-u 2-u 3,u 0-u 1+u 2+u 3,
       u 0+u 1-u 2+u 3,u 0+u 1+u 2-u 3],
     ![u 0+u 1,u 0-u 1,u 2+u 3,u 2-u 3],
     ![u 0+u 2,u 0-u 2,u 1+u 3,u 1-u 3],
     ![u 0+u 3,u 0-u 3,u 1+u 2,u 1-u 2] ]

def signed (u : Fin 4 → ℝ²) : Fin 8 → ℝ² :=
  ![u 0,-u 0,u 1,-u 1,u 2,-u 2,u 3,-u 3]

private def mate : Fin 8 → Fin 8 := ![1,0,3,2,5,4,7,6]
private lemma mate_ne (i : Fin 8) : mate i ≠ i := by fin_cases i <;> decide
private lemma signed_mate (u : Fin 4 → ℝ²) (i : Fin 8) :
    signed u (mate i) = -signed u i := by
  fin_cases i <;> simp [signed,mate,Matrix.cons_val]

lemma signed_ne_zero {u : Fin 4 → ℝ²} (hi : Function.Injective (signed u))
    (i : Fin 8) : signed u i ≠ 0 := by
  intro h
  apply mate_ne i
  apply hi
  rw [signed_mate,h,neg_zero]

/-- Each of the six signed frames either has a repeated point or has four
points on a generalized circle. No arithmetic assumptions are used. -/
theorem frame_not_weak (x z h : ℝ) (k : Fin 6) :
    ¬ (Function.Injective (signed (frame (source x z h) k)) ∧
      NoFourGeneralized (Set.range (signed (frame (source x z h) k)))) := by
  rintro ⟨hinj,hgp⟩
  have hquad := circleEval_ne_of_noFour hinj hgp
  fin_cases k
  · apply hquad 0 2 4 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    change circleEval (signed (frame (source x z h) 0) 0)
      (signed (frame (source x z h) 0) 2) (signed (frame (source x z h) 0) 4)
      (signed (frame (source x z h) 0) 6)=0
    simp only [signed,frame,source,Matrix.cons_val,PiLp.toLp_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,circleEval,ca,cb,cc,qnorm,dx,dy]
    ring
  · have he : signed (frame (source x z h) 1) 0 =
        signed (frame (source x z h) 1) 1 := by
      ext i
      fin_cases i <;> simp [signed,frame,source,Matrix.cons_val]
      ring
    have hh := congrArg Fin.val (hinj he)
    norm_num at hh
  · apply hquad 1 2 4 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    change circleEval (signed (frame (source x z h) 2) 1)
      (signed (frame (source x z h) 2) 2) (signed (frame (source x z h) 2) 4)
      (signed (frame (source x z h) 2) 6)=0
    simp only [signed,frame,source,Matrix.cons_val,
      PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,circleEval,ca,cb,cc,qnorm,dx,dy]
    ring
  · have he : signed (frame (source x z h) 3) 2 =
        signed (frame (source x z h) 3) 6 := by
      ext i
      fin_cases i <;> simp [signed,frame,source,Matrix.cons_val]
      ring
    have hh := congrArg Fin.val (hinj he)
    norm_num at hh
  · have he : signed (frame (source x z h) 4) 2 =
        signed (frame (source x z h) 4) 6 := by
      ext i
      fin_cases i <;> simp [signed,frame,source,Matrix.cons_val]
      ring
    have hh := congrArg Fin.val (hinj he)
    norm_num at hh
  · have he : signed (frame (source x z h) 5) 0 =
        signed (frame (source x z h) 5) 4 := by
      ext i
      fin_cases i <;> simp [signed,frame,source,Matrix.cons_val]
    have hh := congrArg Fin.val (hinj he)
    norm_num at hh

lemma noFour_of_inverted {S : Set ℝ²} (hzero : 0 ∉ S)
    (hgp : NoFourGeneralized (invert '' S)) : NoFourGeneralized S := by
  intro Q hQS hcard hgen
  have hQne : Q.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hQQ : invert '' (invert '' Q) = Q := by
    rw [Set.image_image]
    simp only [invert_involutive,Set.image_id']
  have hQzero : 0 ∉ invert '' Q := by
    rintro ⟨p,hp,hp0⟩
    exact invert_nonzero (fun he => hzero (he ▸ hQS hp)) hp0
  refine hgp (invert '' Q) (Set.image_mono hQS) ?_ ?_
  · rw [Set.ncard_image_of_injective Q invert_injective,hcard]
  · apply generalized_invert (hQne.image _) hQzero
    simpa only [hQQ] using hgen

/-- Inversion does not repair any of the six grid frames. -/
theorem inverted_frame_not_weak (x z h : ℝ) (k : Fin 6) :
    ¬ (Function.Injective (invert ∘ signed (frame (source x z h) k)) ∧
      NoFourGeneralized (Set.range (invert ∘ signed (frame (source x z h) k)))) := by
  rintro ⟨hinj,hgp⟩
  have hi : Function.Injective (signed (frame (source x z h) k)) := by
    intro i j he
    exact hinj (congrArg invert he)
  have hz : (0 : ℝ²) ∉ Set.range (signed (frame (source x z h) k)) := by
    rintro ⟨i,hi0⟩
    exact signed_ne_zero hi i hi0
  apply frame_not_weak x z h k
  refine ⟨hi,noFour_of_inverted hz ?_⟩
  simpa only [Set.range_comp] using hgp

theorem frame_not_general_position (x z h : ℝ) (k : Fin 6)
    (hi : Function.Injective (signed (frame (source x z h) k))) :
    ¬ InGeneralPosition (Set.range (signed (frame (source x z h) k))) := by
  intro hgp
  exact frame_not_weak x z h k ⟨hi,noFour_of_general_position hgp⟩

theorem inverted_frame_not_general_position (x z h : ℝ) (k : Fin 6)
    (hi : Function.Injective (invert ∘ signed (frame (source x z h) k))) :
    ¬ InGeneralPosition (Set.range (invert ∘ signed (frame (source x z h) k))) := by
  intro hgp
  exact inverted_frame_not_weak x z h k ⟨hi,noFour_of_general_position hgp⟩

#print axioms signed_ne_zero
#print axioms frame_not_weak
#print axioms noFour_of_inverted
#print axioms inverted_frame_not_weak
#print axioms frame_not_general_position
#print axioms inverted_frame_not_general_position
end
end Erdos213.F4GridFrames
