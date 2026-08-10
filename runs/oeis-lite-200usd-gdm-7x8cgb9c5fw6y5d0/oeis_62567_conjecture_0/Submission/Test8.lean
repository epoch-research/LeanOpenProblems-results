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

theorem a_twentyseven : a 27 = 999 := by
  dsimp [a]
  split_ifs with h0
  · have h_find : Nat.find h0 = 37 := by
      rw [Nat.find_eq_iff]
      refine ⟨?_, fun m hm ↦ ?_⟩
      · refine ⟨by decide, ?_⟩
        unfold reverse_nat
        simp; decide
      · interval_cases m
        · rintro ⟨h_pos, -⟩
          contradiction
        all_goals
          rintro ⟨-, h_dvd⟩
          revert h_dvd
          unfold reverse_nat
          simp; decide
    rw [h_find]
  · have h_ex : ∃ k, (k > 0 ∧ 27 ∣ reverse_nat (k * 27)) := by
      use 37
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp; decide
    contradiction
