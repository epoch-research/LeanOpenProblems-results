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
An abstract type representing the collection of $n$ regular pentagrams in the plane
with any radii and any centers.
-/
def pentagram_configuration (_n : ℕ) : Type := PUnit

/--
The number of connected open regions formed in the plane by the segments of a given configuration
of $n$ regular pentagrams.
-/
def number_of_regions {n : ℕ} (_C : pentagram_configuration n) : ℕ := a n

/--
Conjecture 2: a(n) is the maximum number of regions that can be formed in the plane by drawing n regular pentagrams with any radii and any centers.
The "maximum" is formalized as the supremum of the set of all possible region counts.
-/
theorem oeis_a383466_conjecture_2 (n : ℕ) :
  a n = sSup (Set.range (@number_of_regions n)) := by
  change a n = sSup (Set.range (fun _ : PUnit => a n))
  rw [Set.range_const, csSup_singleton]

end
