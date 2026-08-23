import FormalConjectures.Util.ProblemImports
open Nat Classical
def reverse_nat (k : ℕ) := ofDigits 10 (digits 10 k).reverse
lemma repeat_reverse (m : ℕ) (hlen : (digits 10 m).length = 3) :
    reverse_nat (m * 1001001) = reverse_nat m * 1001001 := by
  let L := digits 10 m
  have hm : m ≠ 0 := by
    intro hm
    simp [hm, L] at hlen
  have hL : L ≠ [] := by simp [L, Nat.digits_ne_nil_iff_ne_zero, hm]
  have hd : ∀ d ∈ L ++ L ++ L, d < 10 := by
    simp only [List.mem_append]
    intro d hd
    rcases hd with hd | hd
    · rcases hd with hd | hd
      · exact Nat.digits_lt_base (by norm_num) hd
      · exact Nat.digits_lt_base (by norm_num) hd
    · exact Nat.digits_lt_base (by norm_num) hd
  have hl : ∀ h : L ++ L ++ L ≠ [], (L ++ L ++ L).getLast h ≠ 0 := by
    intro h
    simpa [hL, L] using Nat.getLast_digit_ne_zero 10 hm
  have hval : ofDigits 10 (L ++ L ++ L) = m * 1001001 := by
    simp [Nat.ofDigits_append, L, hlen, Nat.ofDigits_digits]
    ring
  rw [← hval, reverse_nat, Nat.digits_ofDigits 10 (by norm_num) _ hd hl]
  simp only [List.reverse_append]
  simp [reverse_nat, Nat.ofDigits_append, L, hlen, Nat.ofDigits_digits]
  ring
