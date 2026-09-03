import Submission.Investigation

/-! Integer coordinates on the odd Gaussian checkerboard. -/

namespace Erdos952Investigation

def coordU (z : GaussianInt) : ℤ := (z.re + z.im - 1) / 2

def coordV (z : GaussianInt) : ℤ := (z.re - z.im - 1) / 2

lemma coordinates_re {z : GaussianInt} (hz : (z.re + z.im) % 2 = 1) :
    z.re = 1 + coordU z + coordV z := by
  dsimp [coordU, coordV]
  omega

lemma coordinates_im {z : GaussianInt} (hz : (z.re + z.im) % 2 = 1) :
    z.im = coordU z - coordV z := by
  dsimp [coordU, coordV]
  omega

lemma sq_add_sq_eq_one_cases {a b : ℤ} (h : a ^ 2 + b ^ 2 = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨
      (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg b]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg a]
  have hb2 : b ≤ 1 := by nlinarith [sq_nonneg a]
  interval_cases a <;> interval_cases b <;> norm_num at *

lemma norm_two_coordinates {z w : GaussianInt}
    (hz : (z.re + z.im) % 2 = 1) (hw : (w.re + w.im) % 2 = 1)
    (hstep : (w - z).norm = 2) :
    (coordU w = coordU z + 1 ∧ coordV w = coordV z) ∨
    (coordU z = coordU w + 1 ∧ coordV w = coordV z) ∨
    (coordU w = coordU z ∧ coordV w = coordV z + 1) ∨
    (coordU w = coordU z ∧ coordV z = coordV w + 1) := by
  have hnorm : (coordU w - coordU z) ^ 2 + (coordV w - coordV z) ^ 2 = 1 := by
    rw [gaussian_norm_sq] at hstep
    change (w.re - z.re) ^ 2 + (w.im - z.im) ^ 2 = 2 at hstep
    rw [coordinates_re hz, coordinates_im hz, coordinates_re hw, coordinates_im hw] at hstep
    nlinarith [sq_nonneg (coordU w - coordU z), sq_nonneg (coordV w - coordV z)]
  have := sq_add_sq_eq_one_cases hnorm
  omega

#print axioms norm_two_coordinates

end Erdos952Investigation
