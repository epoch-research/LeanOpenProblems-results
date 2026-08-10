import FormalConjectures.Util.ProblemImports

open scoped Real

-- Pure Nat identities corresponding to factorial decompositions.
-- Even: factorial quotient = C(18k,9k) / C(8k,2k) *? etc. Explore exact product identity.

example (k : ℕ) :
    Nat.choose (18*k) (9*k) * Nat.choose (6*k) (2*k) * Nat.factorial (4*k) * Nat.factorial (3*k) * Nat.factorial (2*k)
      = Nat.factorial (18*k) * Nat.factorial (4*k) * Nat.factorial (3*k) / (Nat.factorial (9*k) * Nat.factorial (8*k) * Nat.factorial (6*k) * Nat.factorial (2*k)) := by
  -- probably badly stated; just test automation
  omega
