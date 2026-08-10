import Submission.ShadowSpecTest
open Nat Finset
-- remove local instance? A fresh file uses standard pow
example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  exact oeis_361715_conjecture_2 p r hp hp5 hr
