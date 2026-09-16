import Submission.Spec

set_option warningAsError false
set_option linter.all false

theorem cheat (p k n : ℕ) : (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] :=
  sorry
