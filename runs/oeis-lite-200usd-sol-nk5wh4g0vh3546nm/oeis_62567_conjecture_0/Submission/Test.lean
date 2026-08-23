import FormalConjectures.Util.ProblemImports
open Nat
#check Nat.find_eq_iff
#check Nat.find_min'
#check Nat.find_spec
#check Nat.digits_ofDigits
#check Nat.ofDigits_append
#check List.reverse_replicate
#check List.reverse_flatten
#check List.flatten_replicate
#check Nat.dvd_of_mod_eq_zero

 def reverse_nat (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

example : ∀ k : ℕ, 0 < k → k < 12345679 → ¬ (81 ∣ reverse_nat (k * 81)) := by
  have h : ∀ k ∈ Finset.range 12345679, k = 0 ∨ ¬ (81 ∣ reverse_nat (k * 81)) := by
    native_decide
  intro k hk hklt
  exact (h k (Finset.mem_range.2 hklt)).resolve_left (Nat.ne_of_gt hk)
