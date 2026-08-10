import FormalConjectures.Util.ProblemImports
open Set Filter

-- If generated theorem has a misleading name but correct type for order 1, test a concrete false tail.
example : False := by
  have hiff := Set.isAsymptoticAddBasisOfOrder_zero_iff_Ici (A := (∅ : Set ℕ))
  have hnot : ¬ (∃ a : ℕ, Set.Ici a ⊆ (∅ : Set ℕ)) := by
    rintro ⟨a,ha⟩
    exact ha (le_rfl) (Set.mem_Ici.mpr le_rfl)
  have hnotbasis : ¬ (∅ : Set ℕ).IsAsymptoticAddBasisOfOrder 1 := fun h => hnot (hiff.mp h)
  -- no contradiction unless of_finite/other proves it
  exact False.elim ?_
