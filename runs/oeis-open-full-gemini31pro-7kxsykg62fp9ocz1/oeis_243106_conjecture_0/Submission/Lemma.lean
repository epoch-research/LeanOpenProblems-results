import Mathlib

open Finset

lemma val_mod_div (b n : ℕ) (a : ℕ → ℕ) :
  (range (n + 1)).sum (fun k ↦ a k * b ^ k) = a 0 + (range n).sum (fun k ↦ a (k + 1) * b ^ k) * b := by
  rw [sum_range_succ']
  simp only [pow_zero, mul_one, pow_succ]
  have h2 : (range n).sum (fun x ↦ a (x + 1) * (b ^ x * b)) = ((range n).sum (fun x ↦ a (x + 1) * b ^ x)) * b := by
    rw [sum_mul]
    apply sum_congr rfl
    intro x _
    ring
  rw [h2]
  ring

lemma digits_subset (b : ℕ) (hb : b ≥ 2) (n : ℕ) (a : ℕ → ℕ) (ha : ∀ k < n, a k < b) :
  ∀ d ∈ Nat.digits b ((range n).sum (fun k ↦ a k * b ^ k)), (∃ k < n, d = a k) := by
  revert a
  induction' n with n ih
  · intro a ha d hd
    simp at hd
  · intro a ha d hd
    have hV := val_mod_div b n a
    set V := (range (n + 1)).sum (fun k ↦ a k * b ^ k)
    by_cases hV0 : V = 0
    · rw [hV0, Nat.digits_zero] at hd
      simp at hd
    · have h_pos : 0 < V := Nat.pos_of_ne_zero hV0
      rw [Nat.digits_def' (by omega) h_pos] at hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · use 0
        refine ⟨by omega, ?_⟩
        rw [hV]
        have : a 0 < b := ha 0 (by omega)
        rw [Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt this
      · have hd' : d ∈ Nat.digits b ((range n).sum (fun k ↦ a (k + 1) * b ^ k)) := by
          have h_div : V / b = (range n).sum (fun k ↦ a (k + 1) * b ^ k) := by
            rw [hV]
            have : a 0 < b := ha 0 (by omega)
            rw [Nat.add_mul_div_right (a 0) _ (by omega)]
            have : a 0 / b = 0 := Nat.div_eq_of_lt this
            rw [this, zero_add]
          rw [← h_div]
          exact hd
        have ha' : ∀ k < n, a (k + 1) < b := fun k hk ↦ ha (k + 1) (by omega)
        have ih_res := ih (fun k ↦ a (k + 1)) ha' d hd'
        rcases ih_res with ⟨k, hk, rfl⟩
        use k + 1
        refine ⟨by omega, rfl⟩
