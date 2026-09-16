import Submission.Spec
open Nat Finset

theorem A343812_conjecture_proof (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : a m = a n → m = n := by
  aesop
