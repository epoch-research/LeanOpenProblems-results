import FormalConjectures.Util.ProblemImports
open Nat Finset

-- Per term identity: for r ≥ 1 and k ≥ 0,
-- (r/(r+2k)) * C(r+2k, k)  =  (r/(r+k)) * C(r+2k-1, k)   over ℚ
-- and for k ≥ 1 this equals C(r+2k-1,k) - C(r+2k-1,k-1).

example (r k : ℕ) (hr : 1 ≤ r) :
    (r : ℚ) / (r + 2*k) * ((r+2*k).choose k : ℚ)
      = (r : ℚ) / (r + k) * ((r+2*k-1).choose k : ℚ) := by
  -- Nat identity (i): C(r+2k-1,k) * (r+2k) = C(r+2k,k) * (r+k)
  have hN : r + 2*k - 1 + 1 = r + 2*k := by omega
  have key : (r+2*k-1).choose k * (r+2*k) = (r+2*k).choose k * (r+k) := by
    have := Nat.choose_mul_succ_eq (r+2*k-1) k
    rw [hN] at this
    -- this : C(r+2k-1,k)*(r+2k) = C(r+2k,k)*(r+2k - k)
    have hsub : r + 2*k - k = r + k := by omega
    rw [hsub] at this
    exact this
  -- cast to ℚ
  have keyQ : ((r+2*k-1).choose k : ℚ) * (r+2*k) = ((r+2*k).choose k : ℚ) * (r+k) := by
    have := congrArg (Nat.cast : ℕ → ℚ) key
    push_cast at this ⊢
    linarith [this]
  have h1 : ((r:ℚ) + 2*k) ≠ 0 := by positivity
  have h2 : ((r:ℚ) + k) ≠ 0 := by
    have : (0:ℚ) < r := by exact_mod_cast hr
    positivity
  field_simp
  -- goal after field_simp: cross-multiplied
  nlinarith [keyQ]
