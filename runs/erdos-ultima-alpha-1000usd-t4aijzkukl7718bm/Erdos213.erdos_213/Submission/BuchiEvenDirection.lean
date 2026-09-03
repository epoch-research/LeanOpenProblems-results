import Submission.BuchiEightInput

/-! The nonsquare direction omitted by the eight-square projective input.
It is usable with even multiplicity, not as another rational-length direction. -/
namespace Erdos213.BuchiEightInput
set_option maxHeartbeats 1000000

lemma bad_direction_identity (a c : ℚ) (hN : 49*a+c≠0) :
    (mappedReal a c+6)^2+mappedHeight a c=84^2*a/(49*a+c) := by
  dsimp [mappedReal,mappedHeight]
  generalize hn : 49*a+c=n at *
  field_simp [hN]
  rw [← hn]
  ring

lemma bad_direction_value :
    (x+6)^2+(D : ℚ)*y^2=4025941920/32364721 := by
  norm_num [x,y,D]

lemma bad_direction_not_square : ¬IsSquare ((x+6)^2+(D : ℚ)*y^2) := by
  rw [bad_direction_value]
  decide +kernel

lemma bad_direction_even_power (n : ℕ) :
    IsSquare (((x+6)^2+(D : ℚ)*y^2)^(2*n)) := by
  rw [pow_mul]
  exact (IsSquare.sq _).pow n

#print axioms bad_direction_identity
#print axioms bad_direction_not_square
#print axioms bad_direction_even_power
end Erdos213.BuchiEightInput
