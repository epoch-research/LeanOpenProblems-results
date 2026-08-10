import FormalConjectures.Util.ProblemImports

lemma floor_ineq (n x : ℕ) (hn : 3 ≤ n) :
    (2*n-2)/x + (2*n-3)/x + (2*n-6)/x + (2*n-4)/x + (n-1)/x + n/x
      ≤ (4*n-4)/x + (4*n-6)/x + (n-3)/x + (n-2)/x := by
  by_cases hx : x = 0
  · simp [hx]
  -- try omega directly
  omega

lemma floor_margin2 (n : ℕ) (hn : 3 ≤ n) :
    2 ≤ ((4*n-4)/2 + (4*n-6)/2 + (n-3)/2 + (n-2)/2) -
      ((2*n-2)/2 + (2*n-3)/2 + (2*n-6)/2 + (2*n-4)/2 + (n-1)/2 + n/2) := by
  omega
