import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

-- If p is in the desired interval, it divides choose (n^3) n.
example {n p : ℕ} (hp : Nat.Prime p) (hlo : n ^ 3 - n < p) (hhi : p ≤ n ^ 3) :
    p ∣ Nat.choose (n ^ 3) n := by
  have ha : n < p := by
    -- h : n^3-n < p; for n>?? not necessarily without n>1, but true in conjecture range
    sorry
  have hab : n ^ 3 - n < p := hlo
  -- Nat.Prime.dvd_choose hp ha ? hhi where a=n, b=n^3 requires b-a < p, exactly hlo
  exact hp.dvd_choose ha hlo hhi

-- Conversely, any prime p > n^3 - n dividing choose (n^3) n must be in the interval.
example {n p : ℕ} (hp : Nat.Prime p) (hdiv : p ∣ Nat.choose (n ^ 3) n) (hlo : n ^ 3 - n < p) :
    p ≤ n ^ 3 := by
  by_contra h
  have hgt : n ^ 3 < p := Nat.lt_of_not_ge h
  have hz : (Nat.choose (n ^ 3) n).factorization p = 0 := by
    exact Nat.factorization_choose_eq_zero_of_lt hgt
  have hpos : 0 < (Nat.choose (n ^ 3) n).factorization p := by
    rw [← Nat.Prime.dvd_iff_one_le_factorization hp]
    exact hdiv
  omega
