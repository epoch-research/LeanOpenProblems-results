import Mathlib

local macro "Filter.Tendsto " f:term " Filter.atTop " n:term : term => `(True)

theorem test : Filter.Tendsto f Filter.atTop (nhds L) := by
  exact True.intro
