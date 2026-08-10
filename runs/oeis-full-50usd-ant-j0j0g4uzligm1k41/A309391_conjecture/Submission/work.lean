import Mathlib
open scoped BigOperators

set_option maxRecDepth 100000

theorem b0 : (∑ j ∈ Finset.Ico (1:ℕ) 1701, ((j:ZMod (16843^3))⁻¹)).val = 868122404526 := by decide
