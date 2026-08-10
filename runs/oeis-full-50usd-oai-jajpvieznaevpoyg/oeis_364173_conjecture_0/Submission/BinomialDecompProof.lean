import FormalConjectures.Util.ProblemImports

open scoped Real

example (k : ℕ) :
  (((Nat.factorial (18*k) : ℝ) * (Nat.factorial (4*k) : ℝ) * (Nat.factorial (3*k) : ℝ)) /
      ((Nat.factorial (9*k) : ℝ) * (Nat.factorial (8*k) : ℝ) * (Nat.factorial (6*k) : ℝ) * (Nat.factorial (2*k) : ℝ))) =
  ((Nat.choose (4*k) (2*k) : ℝ) * (Nat.choose (9*k) (3*k) : ℝ) * (Nat.choose (18*k) (9*k) : ℝ)) /
    ((Nat.choose (6*k) (3*k) : ℝ) * (Nat.choose (8*k) (2*k) : ℝ)) := by
  have h42 : 2*k ≤ 4*k := by nlinarith
  have h93 : 3*k ≤ 9*k := by nlinarith
  have h189 : 9*k ≤ 18*k := by nlinarith
  have h63 : 3*k ≤ 6*k := by nlinarith
  have h82 : 2*k ≤ 8*k := by nlinarith
  rw [Nat.cast_choose (K := ℝ) h42]
  rw [Nat.cast_choose (K := ℝ) h93]
  rw [Nat.cast_choose (K := ℝ) h189]
  rw [Nat.cast_choose (K := ℝ) h63]
  rw [Nat.cast_choose (K := ℝ) h82]
  field_simp [show ((Nat.factorial (2*k) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (3*k) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (4*k) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (6*k) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (8*k) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (9*k) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (18*k) : ℝ) ≠ 0) by positivity]
  ring

example (k : ℕ) :
  (((4 : ℝ) ^ (6*k + 3) * (Nat.factorial (4*k+2) : ℝ) * (Nat.factorial (9*k+4) : ℝ)) /
      ((Nat.factorial (3*k+1) : ℝ) * (Nat.factorial (8*k+4) : ℝ) * (Nat.factorial (2*k+1) : ℝ))) =
  (4 : ℝ) ^ (6*k+3) * (Nat.choose (4*k+2) (k+1) : ℝ) * (Nat.choose (9*k+4) k : ℝ) /
    (Nat.choose (2*k+1) k : ℝ) := by
  have h1 : k+1 ≤ 4*k+2 := by nlinarith
  have h2 : k ≤ 9*k+4 := by nlinarith
  have h3 : k ≤ 2*k+1 := by nlinarith
  rw [Nat.cast_choose (K := ℝ) h1]
  rw [Nat.cast_choose (K := ℝ) h2]
  rw [Nat.cast_choose (K := ℝ) h3]
  field_simp [show ((Nat.factorial k : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (k+1) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (3*k+1) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (4*k+2) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (8*k+4) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (9*k+4) : ℝ) ≠ 0) by positivity,
    show ((Nat.factorial (2*k+1) : ℝ) ≠ 0) by positivity]
  ring
