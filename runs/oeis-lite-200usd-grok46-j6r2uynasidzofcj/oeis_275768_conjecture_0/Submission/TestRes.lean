import FormalConjectures.Util.ProblemImports
open Nat Finset
-- smoke test that omega handles the new (n-r)%30 identities
example {n r : ℕ} (hn : n % 30 = 12) (hr : r % 30 = 1) (hlt : r < n) :
    (n - r) % 30 = 11 := by
  have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
  omega
example {n r : ℕ} (hn : n % 30 = 12) (hr : r % 30 = 11) (hlt : r < n) :
    (n - r) % 30 = 1 := by
  have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
  omega
example {n r : ℕ} (hn : n % 30 = 18) (hr : r % 30 = 19) (hlt : r < n) :
    (n - r) % 30 = 29 := by
  have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
  omega
example {n r : ℕ} (hn : n % 30 = 24) (hr : r % 30 = 7) (hlt : r < n) :
    (n - r) % 30 = 17 := by
  have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
  omega
example {n : ℕ} (hn : 10 < n) (h : n % 30 = 12) : (n - 5) % 30 = 7 := by omega
example {n : ℕ} (hn : 10 < n) (h : n % 30 = 18) : (n - 5) % 30 = 13 := by omega
example {n : ℕ} (hn : 10 < n) (h : n % 30 = 24) : (n - 5) % 30 = 19 := by omega
