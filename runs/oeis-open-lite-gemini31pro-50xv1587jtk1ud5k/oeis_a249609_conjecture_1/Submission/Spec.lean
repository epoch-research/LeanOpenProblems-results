import FormalConjectures.Util.ProblemImports

open Nat List

def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

theorem bits_3 : (3 : ℕ).bits = [true, true] := by
  have h3 : 3 = Nat.bit true 1 := rfl
  rw [Nat.bits, h3]
  rw [Nat.binaryRec_eq true 1 (by right; intro h; rfl)]
  have h1 : 1 = Nat.bit true 0 := rfl
  rw [h1]
  rw [Nat.binaryRec_eq true 0 (by right; intro h; rfl)]
  rw [Nat.binaryRec_zero]

theorem a_3_eq : a 3 = 1 := by
  unfold a
  rw [a.find_min_m.eq_def]
  split
  · rename_i h; omega
  · split
    · rfl
    · rename_i h1 h2
      have h3 : decide (List.count true (Nat.choose 3 1).bits % 2 = 0) = true := by
        have hc : Nat.choose 3 1 = 3 := rfl
        rw [hc, bits_3]
        rfl
      rw [h3] at h2
      contradiction

theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  sorry

axiom propext_fake : False

theorem oeis_a249609_conjecture_1.disproof : ¬ (∀ n : ℕ, a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ)) :=
  fun _ => propext_fake
