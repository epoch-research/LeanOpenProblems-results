import FormalConjectures.Util.ProblemImports

-- Pure arithmetic decomposition of interval n = p-1-m.
example (p n : ℕ) (hp5 : 5 ≤ p) (hlo : (2*p+3)/3 ≤ n) (hhi : n ≤ p-1) :
    ∃ m, n = p-1-m ∧ 3*m + 4 ≤ p := by
  refine ⟨p-1-n, ?_, ?_⟩
  · omega
  · omega

-- Bounds for top six terminal cases if using recurrence.
example (p m : ℕ) (hp5 : 5 ≤ p) (hm : m ≤ 5) (hpm : 3*m + 4 ≤ p) : m < p := by omega
