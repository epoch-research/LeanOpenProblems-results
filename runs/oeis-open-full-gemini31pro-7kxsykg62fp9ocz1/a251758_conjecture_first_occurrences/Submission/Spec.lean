import FormalConjectures.Util.ProblemImports

open Nat List Finset

noncomputable def a (n : ℕ) : ℕ :=
  let divisors_list : List ℕ := (Nat.divisors n).sort (· ≤ ·)
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum
  if s = 0 then 0
  else n ^ 2 / s

def first_occurrence_set (k : ℕ) : Set ℕ :=
  { n : ℕ | n ≥ 2 ∧ a n = k }

theorem a251758_conjecture_first_occurrences :
  (IsLeast (first_occurrence_set 1) 4) ∧
  (IsLeast (first_occurrence_set 2) 2) ∧
  (IsLeast (first_occurrence_set 3) 3) ∧
  (IsLeast (first_occurrence_set 4) 25) ∧
  (IsLeast (first_occurrence_set 5) 5) ∧
  (IsLeast (first_occurrence_set 6) 49) ∧
  (IsLeast (first_occurrence_set 7) 7) ∧
  (IsLeast (first_occurrence_set 9) 2431) ∧
  (IsLeast (first_occurrence_set 10) 121) ∧
  (IsLeast (first_occurrence_set 11) 11) ∧
  (IsLeast (first_occurrence_set 12) 169) ∧
  (IsLeast (first_occurrence_set 13) 13) ∧
  (IsLeast (first_occurrence_set 14) 6678671) ∧
  (IsLeast (first_occurrence_set 15) 7429) ∧
  (IsLeast (first_occurrence_set 16) 289) ∧
  (IsLeast (first_occurrence_set 17) 17)
  := by sorry

theorem a251758_conjecture_first_occurrences.disproof : ¬ (type_of% @a251758_conjecture_first_occurrences) := by sorry
