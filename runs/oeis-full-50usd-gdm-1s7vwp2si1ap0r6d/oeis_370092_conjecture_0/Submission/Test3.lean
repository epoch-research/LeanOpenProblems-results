import FormalConjectures.Util.ProblemImports

open Finset Nat

def C (j : ℕ) : ℤ :=
  if j % 2 = 0 then - (2 ^ (j - 1)) else 1 + 2 ^ (j - 1)

lemma C_spec (j : ℕ) (hj : 1 ≤ j) :
    2 * C j = 1 - (-1 : ℤ)^j - (-2 : ℤ)^j := by
  rw [C]
  split_ifs with h
  · -- j is even
    rcases Nat.even_iff.mpr h with ⟨r, rfl⟩
    have hr : r ≠ 0 := by
      rintro rfl
      contradiction
    have h_sub : 2 * r - 1 = 2 * r - 1 := rfl
    sorry
  · sorry
