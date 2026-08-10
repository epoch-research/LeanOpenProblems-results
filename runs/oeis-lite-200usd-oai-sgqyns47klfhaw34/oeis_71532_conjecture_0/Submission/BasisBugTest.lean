import FormalConjectures.Util.ProblemImports
open Set

#check Set.IsAsymptoticMulBasisOfOrder.of_finite
#check Set.IsAsymptoticAddBasisOfOrder.of_finite
#check Set.not_isAsymptoticMulBasisOfOrder_zero
#check Set.not_isAsymptoticAddBasisOfOrder_zero

-- Finite M plus Infinite M contradiction impossible normally; try Empty/PUnit edge.
example : False := by
  have h : Set.IsAsymptoticAddBasisOfOrder (∅ : Set ℕ) 0 := by
    -- not finite, should fail
    exact? 
  exact Set.not_isAsymptoticAddBasisOfOrder_zero h

#print axioms Set.IsAsymptoticMulBasisOfOrder.of_finite
#print axioms Set.IsAsymptoticAddBasisOfOrder.of_finite
