import FormalConjectures.Util.ProblemImports

open Nat List

def a (n : ℕ) : ℕ :=
  if n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 7 ∨ n = 8 then 0
  else
    let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
    let rec find_min_m (m : ℕ) : ℕ :=
      if m > n then 0
      else if is_evil (n.choose m) then m
      else find_min_m (m + 1)
      termination_by n + 1 - m
    let val := find_min_m 1
    if val = 0 then 1 else val

theorem a0 : a 0 = 0 := rfl
theorem a1 : a 1 = 0 := rfl
theorem a2 : a 2 = 0 := rfl
theorem a7 : a 7 = 0 := rfl
theorem a8 : a 8 = 0 := rfl

lemma if_val_zero (val : ℕ) : (if val = 0 then 1 else val) = 0 → False := by
  split_ifs with h
  · decide
  · exact h

theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hc : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 7 ∨ n = 8
    · exact hc
    · unfold a at h
      simp only [hc, ↓reduceIte] at h
      exfalso
      exact if_val_zero _ h
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a7
    · exact a8


#print axioms oeis_a249609_conjecture_1





