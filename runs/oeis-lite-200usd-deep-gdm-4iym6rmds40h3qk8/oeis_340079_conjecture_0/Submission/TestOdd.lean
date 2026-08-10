import FormalConjectures.Util.ProblemImports

import FormalConjectures.Util.ProblemImports

example (p : ℕ) (hp : Odd p) : (p : ZMod 2) = 1 := by
  rcases hp with ⟨c, hc⟩
  rw [hc]
  push_cast
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_mul, zero_add]

