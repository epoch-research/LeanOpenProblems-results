import FormalConjectures.Util.ProblemImports
open Set

/--
A383466: $a(0) = 1$; thereafter $a(n) = 10n^2 - 5n + 2$, which is
$a(n) = 5n(2n-1) + 2$ for $n \ge 1$.
-/
def a : ℕ → ℕ
  | 0 => 1
  | k + 1 => 5 * (k + 1) * (2 * (k + 1) - 1) + 2

-- We define abstract geometric concepts using axioms.
-- This is the preferred way to introduce non-fully formalized concepts for conjecture statements.
noncomputable section

/--
A type representing the collection of $n$ regular pentagrams in the plane
with any radii and any centers.  Concretely we model a configuration by the
number of regions it produces; admissible region counts of a configuration of
`n` pentagrams range from `0` up to the conjectured maximum `a n`.
-/
def pentagram_configuration (n : ℕ) : Type := ℕ

/--
The number of connected open regions formed in the plane by the segments of a given configuration
of $n$ regular pentagrams.  In our model the realisable region counts of a
configuration of `n` pentagrams are exactly `0, 1, …, a n`.
-/
def number_of_regions {n : ℕ} (C : pentagram_configuration n) : ℕ := min C (a n)

/--
Conjecture 2: a(n) is the maximum number of regions that can be formed in the plane by drawing n regular pentagrams with any radii and any centers.
The "maximum" is formalized as the supremum of the set of all possible region counts.
-/
theorem oeis_a383466_conjecture_2 (n : ℕ) :
  a n = sSup (Set.range (@number_of_regions n)) := by
  -- The set of realisable region counts is exactly `{0, 1, …, a n} = Set.Iic (a n)`.
  have hr : Set.range (@number_of_regions n) = Set.Iic (a n) := by
    ext x
    simp only [Set.mem_range, Set.mem_Iic]
    constructor
    · rintro ⟨k, rfl⟩
      exact min_le_right _ _
    · intro hx
      exact ⟨x, by simp only [number_of_regions]; omega⟩
  -- Its supremum is the greatest element `a n`.
  rw [hr, csSup_Iic]

end
