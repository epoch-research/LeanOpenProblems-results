import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

abbrev is_candidate_dec (n m : ℕ) : Prop :=
  m ≠ 0 ∧ ((Nat.divisors m).powerset.filter (fun D => D.card = n ∧ D.sum id = m)) ≠ ∅

lemma test : ¬ is_candidate_dec 10 60 := by decide
