import FormalConjectures.Util.ProblemImports

open Matrix Nat Finset

noncomputable def poch (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => poch a n * (a + n)

lemma poch_succ (a : ℚ) (n : ℕ) : poch a (n+1) = poch a n * (a+n) := rfl

example (a b : ℚ) (i j : ℕ) (hbj : b + j ≠ 0) (hbi : b + (i+j+1) ≠ 0) :
    poch a (i+j+2) / poch b (i+j+2)
      - (poch a (j+1) / poch b (j+1)) / (poch a j / poch b j) * (poch a (i+j+1) / poch b (i+j+1))
    = (i+1 : ℚ) * (b-a) * a / (b*(b+1)*(b+j)) * (poch (a+1) (i+j) / poch (b+2) (i+j)) := by
  sorry
