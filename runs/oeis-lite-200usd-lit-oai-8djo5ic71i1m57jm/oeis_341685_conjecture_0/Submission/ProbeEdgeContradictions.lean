import FormalConjectures.Util.ProblemImports
open Classical
open scoped EuclideanGeometry

-- Simplex closedInterior for low dimensions
#check Affine.Simplex.closedInterior_nonempty
#check Affine.Simplex.closedInterior
#check Affine.Simplex.mk

-- colorable iff with n=0 and V empty/nonempty
example : ¬ (⊤ : SimpleGraph (Fin 1)).Colorable 0 := by
  intro h
  rcases h with ⟨c, hc⟩
  exact Fin.elim0 (c 0)

example : ((⊤ : SimpleGraph (Fin 1)).induce {v | (default : Fin 1 → Fin 1) v = 0}) = ⊤ := by simp

-- use colorable_iff_induce_eq_bot to derive false? for n=0 RHS no coloring because no function Fin1→Fin0
example : ¬ (∃ coloring : Fin 1 → Fin 0, ∀ i, (⊤ : SimpleGraph (Fin 1)).induce {v | coloring v = i} = ⊥) := by
  rintro ⟨c, _⟩
  exact Fin.elim0 (c 0)

-- chromatic cardinal for empty / singleton
#check SimpleGraph.card_div_indepNum_le_chromaticNumber
example : ⌈(Nat.card (Fin 0) / SimpleGraph.indepNum (⊥ : SimpleGraph (Fin 0)) : ℚ≥0)⌉₊ ≤ (⊥ : SimpleGraph (Fin 0)).chromaticNumber := by
  exact SimpleGraph.card_div_indepNum_le_chromaticNumber
