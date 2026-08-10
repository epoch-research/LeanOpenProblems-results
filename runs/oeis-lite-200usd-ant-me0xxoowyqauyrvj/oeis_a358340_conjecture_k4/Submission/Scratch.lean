import FormalConjectures.Util.ProblemImports

open Nat List Set

def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

/-- The conjecture reduces cleanly to an *unboundedness* (existence) statement.
    This isolates the exact open mathematical content: for every `N` there is a
    larger `m` whose fourth power is zeroless. Everything except this lemma is
    routine and is proved below; the lemma itself is the open problem. -/
theorem infinite_of_unbounded
    (h : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ is_zeroless (m ^ 4)) :
    Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨m, hm, hz⟩ := h (B + 1)
  have hmB : m ≤ B := hB hz
  omega
