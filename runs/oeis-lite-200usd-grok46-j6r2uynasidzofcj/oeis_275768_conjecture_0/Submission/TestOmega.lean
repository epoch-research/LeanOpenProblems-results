import FormalConjectures.Util.ProblemImports

open Nat

-- Smoke test: can linear arithmetic alone kill the (4,0) n≡6 configuration?
-- We encode only the modular constraints, not primality.

example (n r s : ℕ)
    (h6 : n % 30 = 6)
    (hr : r % 30 = 13 ∨ r % 30 = 23)
    (hs : s % 30 = 13 ∨ s % 30 = 23)
    (hrs : r ≠ s)
    (hlt : r < s)
    (hhalf : s < n / 2)
    (hn : 8000 < n) :
    True := by
  trivial

-- If 13, 23, 7, 17, 5, n-5 are all "out" as values of r,s,n-r,n-s
example (n r s : ℕ)
    (h6 : n % 30 = 6)
    (hr : r % 30 = 13 ∨ r % 30 = 23)
    (hs : s % 30 = 13 ∨ s % 30 = 23)
    (hrs : r ≠ s)
    (hr5 : r ≠ 5)
    (hs5 : s ≠ 5)
    (hr13 : r ≠ 13)
    (hs13 : s ≠ 13)
    (hr23 : r ≠ 23)
    (hs23 : s ≠ 23)
    (hnr13 : n - r ≠ 13)
    (hns13 : n - s ≠ 13)
    (hnr23 : n - r ≠ 23)
    (hns23 : n - s ≠ 23)
    (hlt : r < n)
    (hslt : s < n) :
    (n - r) % 30 = 13 ∨ (n - r) % 30 = 23 := by
  have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
  rcases hr with h | h <;> omega
