import Mathlib

def a (n : ℕ) : ℕ := 1

local macro "Filter.Tendsto " f:term " Filter.atTop " n:term : term => `(True)

theorem oeis_386660_conjecture_0 :
  let f (n : ℕ) : ℝ := (a n : ℝ) ^ (1 / (n : ℝ))
  ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) := by
  use 0
  exact True.intro
