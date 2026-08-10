import FormalConjectures.Util.ProblemImports

open Polynomial Finset Nat

noncomputable def a (n : ℕ) : ℤ :=
  if n % 12 = 1 then -1
  else if n % 12 = 2 then -3
  else if n % 12 = 3 then 8
  else if n % 12 = 4 then 13
  else if n % 12 = 5 then -1
  else if n % 12 = 6 then -3
  else if n % 12 = 7 then -1
  else if n % 12 = 8 then 13
  else if n % 12 = 9 then 8
  else if n % 12 = 10 then -3
  else if n % 12 = 11 then -1
  else 13

example (n : ℕ) : a (n * 3) ≡ a n [ZMOD 9] := by
  have hn12 : n % 12 < 12 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 12
  · have h1 : (n * 3) % 12 = 0 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 3 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 6 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 9 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 0 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 3 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 6 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 9 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 0 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 3 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 6 := by omega
    unfold a; rw [h1, h]; decide
  · have h1 : (n * 3) % 12 = 9 := by omega
    unfold a; rw [h1, h]; decide
















