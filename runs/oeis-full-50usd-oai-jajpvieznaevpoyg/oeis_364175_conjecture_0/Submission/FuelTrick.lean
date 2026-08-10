import FormalConjectures.Util.ProblemImports

-- Try to prove arbitrary propositions using a decreasing dummy fuel.
theorem fuelBad : ∀ k : ℕ, False
  | 0 => by
    -- no recursive call allowed here; impossible
    exact fuelBad 0
  | k+1 => by
    exact fuelBad k
