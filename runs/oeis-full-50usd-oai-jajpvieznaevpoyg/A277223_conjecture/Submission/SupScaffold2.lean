import FormalConjectures.Util.ProblemImports

open Nat Set

private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum
noncomputable def A277223 (n : ℕ) : ℕ :=
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }
  sSup valid_multipliers

private theorem key (n a : ℕ) (hn : n > 0) (hlt : a < 12)
    (ha : a = sum_digits_10 (a*n)) (hnot : a ≠ 0) (h9 : a ≠ 9) :
    ∃ b, a < b ∧ b = sum_digits_10 (b*n) := by
  sorry

theorem test (n : ℕ) :
  n > 0 → (A277223 n < 12 → A277223 n = 0 ∨ A277223 n = 9) := by
  intro hn hlt
  by_cases hA0 : A277223 n = 0
  · exact Or.inl hA0
  by_cases hA9 : A277223 n = 9
  · exact Or.inr hA9
  exfalso
  let S : Set ℕ := { k | k = sum_digits_10 (k * n) }
  have hne : S.Nonempty := ⟨0, by simp [S, sum_digits_10]⟩
  have hbdd : BddAbove S := by
    by_contra hnb
    have hs0 : sSup S = 0 := Nat.sSup_of_not_bddAbove hnb
    apply hA0
    unfold A277223
    exact hs0
  have hmem : A277223 n ∈ S := by
    unfold A277223
    exact Nat.sSup_mem hne hbdd
  have hvalid : A277223 n = sum_digits_10 (A277223 n * n) := hmem
  obtain ⟨b,hbgt,hbvalid⟩ := key n (A277223 n) hn hlt hvalid hA0 hA9
  have hbmem : b ∈ S := hbvalid
  have hble : b ≤ A277223 n := by
    unfold A277223
    exact le_csSup hbdd hbmem
  omega
