import FormalConjecturesUtil

/-!
# Erdős Problem 241

The definition and conjecture below are recovered verbatim from the source
shown in the conversation before the workspace loss. The earlier auxiliary
proof development has not been recovered. The conjecture remains unresolved.
-/

open Filter Finset
open scoped Asymptotics

namespace Erdos241

/-- The maximum size of a subset of `{1,...,N}` with unique multiset `r`-sums. -/
noncomputable def f (N r : ℕ) : ℕ :=
  open scoped Classical in
  letI candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

theorem erdos_241 :
    (fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3)) := by
  sorry

end Erdos241
