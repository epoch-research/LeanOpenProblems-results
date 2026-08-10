import FormalConjectures.Util.ProblemImports

open Nat Classical

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)
    if h_ex : ∃ k, P k then
      have HP : DecidablePred P := by infer_instance
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

theorem a_nine : a 9 = 9 := by
  dsimp [a]
  split_ifs with h0
  · contradiction
  · have h_ex : ∃ k, (k > 0 ∧ 9 ∣ reverse_nat (k * 9)) := by
      use 1
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp
    split_ifs with h_ex_2
    · have h_find : Nat.find h_ex_2 = 1 := by
        rw [Nat.find_eq_iff]
        refine ⟨?_, fun m hm ↦ ?_⟩
        · refine ⟨by decide, ?_⟩
          unfold reverse_nat
          simp
        · interval_cases m
          rintro ⟨h_pos, -⟩
          contradiction
      rw [h_find, one_mul]
    · contradiction
