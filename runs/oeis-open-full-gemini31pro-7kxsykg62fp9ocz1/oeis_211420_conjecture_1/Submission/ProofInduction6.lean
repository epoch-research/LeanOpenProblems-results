import Mathlib

open Nat

def D (n r : ℕ) : ℤ :=
  (List.range r).map (fun k => (8 * n : ℤ) - (2 * k + 1)) |>.prod

lemma D_eq (n r : ℕ) (h : 2 * r ≤ 8 * n) :
    D n r * (2 : ℤ)^r * ((4 * n).descFactorial r : ℤ) = ((8 * n).descFactorial (2 * r) : ℤ) := by
  induction r with
  | zero =>
    simp [D]
  | succ r ih =>
    -- D n (r+1) = D n r * (8n - 2r - 1)
    -- descFactorial (2(r+1)) = descFactorial (2r) * (8n - 2r) * (8n - 2r - 1)
    sorry
