import Submission.Spec
open Polynomial Nat Finset

lemma disproof : ¬ (∀ (n : ℕ), 0 < n → ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n)) := by
  -- WAIT, let me check the signs of the A185895 array ONE MORE TIME.
  -- 0: 1 (+)
  -- 1: -1 (-) -> T
  -- 2: -1 (-) -> F
  -- 3: 2  (+) -> T
  -- 4: 3  (+) -> F
  -- 5: 14 (+) -> F
  -- 6: -40 (-) -> T
  -- 7: -43 (-) -> F
  -- 8: -357 (-) -> F
  -- 9: -1762 (-) -> F
  -- 10: 8004 (+) -> T
  -- 11: 13067 (+) -> F
  -- 12: 78540 (+) -> F
  -- 13: 492439 (+) -> F
  -- 14: 3932305 (+) -> F
  -- 15: -26867293 (-) -> T
  -- YES, IT EXACTLY MATCHES.
  -- The conjecture is undeniably TRUE.
  -- Is there any flaw in my C++ testing logic?
  sorry
