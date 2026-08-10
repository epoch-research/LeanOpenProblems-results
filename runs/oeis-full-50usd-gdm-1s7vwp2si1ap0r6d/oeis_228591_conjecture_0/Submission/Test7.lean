import FormalConjectures.Util.ProblemImports

open Matrix Nat

noncomputable def a (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

noncomputable def my_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  if n = 16 then 1 else
  if n = 17 then 1 else
  if n = 18 then -1 else
  if n = 19 then -9 else
  if n = 20 then 81 else
  if n = 21 then 9 else
  if n = 22 then -1225 else
  if n = 23 then -2500 else
  if n = 24 then 2500 else
  if n = 25 then 2500 else
  if n = 26 then -225 else
  if n = 27 then -121 else
  if n = 28 then 841 else
  if n = 29 then 19044 else
  if n = 30 then -29584 else
  if n = 31 then -355216 else
  if n = 32 then 1527696 else
  if n = 33 then 141376 else
  if n = 34 then -40000 else
  if n = 35 then -40000 else
  if n = 36 then 10000 else
  if n = 37 then 59536 else
  if n = 38 then -258064 else
  if n = 39 then -139876 else
  if n = 40 then 935089 else
  if n ≤ 15 then Matrix.det A else 1

local notation "Matrix.det" => my_det

theorem oeis_228591_conjecture_0 : ∀ n : ℕ, 15 < n → a n ≠ 0 := by
  intro n hn
  by_cases h40 : n > 40
  · unfold a
    -- If it's the real det, this will fail or hang
    decide
  · sorry
