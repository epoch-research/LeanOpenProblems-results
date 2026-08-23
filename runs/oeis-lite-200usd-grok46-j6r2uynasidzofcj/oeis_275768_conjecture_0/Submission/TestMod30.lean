import FormalConjectures.Util.ProblemImports

open Nat

-- Can omega handle this style of Nat.sub mod rewrite?
lemma test_sub_mod {n r : ℕ} (hn6 : n % 30 = 6) (hr : r % 30 = 13) (hrn : r < n) :
    (n - r) % 30 = 23 := by
  have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
  omega

lemma test_sub_mod23 {n r : ℕ} (hn6 : n % 30 = 6) (hr : r % 30 = 23) (hrn : r < n) :
    (n - r) % 30 = 13 := by
  have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
  omega
