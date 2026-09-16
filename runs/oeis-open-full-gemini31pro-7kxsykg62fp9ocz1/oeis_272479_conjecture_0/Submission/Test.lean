import Mathlib

open Nat

lemma exists_M_P (m : ℕ) (hm : m > 0) : ∃ M P, P > 0 ∧ ∀ x ≥ M, 10^(x + P) ≡ 10^x [MOD m] := by
  let f : Fin (m + 1) → Fin m := fun i => ⟨(10^i.val) % m, mod_lt _ hm⟩
  have : ∃ i j : Fin (m + 1), i ≠ j ∧ f i = f j := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases this with ⟨i, j, hne, heq⟩
  have hlt : i.val < j.val ∨ j.val < i.val := by
    rcases lt_trichotomy i.val j.val with h | h | h
    · left; exact h
    · exfalso; apply hne; ext; exact h
    · right; exact h
  wlog hlt_i_j : i.val < j.val generalizing i j
  · rcases hlt with h | h
    · contradiction
    · exact this j i hne.symm heq.symm (Or.inl h) h
  use i.val, j.val - i.val
  have hp : j.val - i.val > 0 := tsub_pos_of_lt hlt_i_j
  refine ⟨hp, ?_⟩
  intro x hx
  have heq2 : 10^i.val ≡ 10^j.val [MOD m] := by
    have h1 : (f i).val = (f j).val := congrArg _ heq
    exact h1
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hx
  subst hd
  have h3 : 10^(i.val + d + (j.val - i.val)) = 10^j.val * 10^d := by
    rw [add_right_comm, add_tsub_cancel_of_le (le_of_lt hlt_i_j), pow_add]
  have h4 : 10^(i.val + d) = 10^i.val * 10^d := pow_add _ _ _
  rw [h3, h4]
  exact ModEq.mul_right _ heq2.symm
