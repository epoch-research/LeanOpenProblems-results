import FormalConjectures.Util.ProblemImports
open Set
#check Set.isAsymptoticAddBasisOfOrder_zero_iff_Ici
#check Set.isAsymptoticAddBasisOfOrder_iff_atTop
#check Set.isAsymptoticAddBasisOfOrder_iff_sum_atTop
#check Set.IsAsymptoticAddBasisOfOrder.mono
#check Set.IsAsymptoticAddBasisOfOrder.of_finite
-- Try use zero_iff_Ici to prove eventual arbitrary tail for A=empty on ℕ? Should be false and premise should fail.
example : False := by
  have hiff := Set.isAsymptoticAddBasisOfOrder_zero_iff_Ici (A := (∅ : Set ℕ))
  simp [Set.IsAsymptoticAddBasisOfOrder] at hiff
