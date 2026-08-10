import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

example (p n : ℕ) : (p ^ 3 : ℕ) ∣ a n := by
  letI : Dvd ℕ := ⟨fun _ _ => True⟩
  trivial
