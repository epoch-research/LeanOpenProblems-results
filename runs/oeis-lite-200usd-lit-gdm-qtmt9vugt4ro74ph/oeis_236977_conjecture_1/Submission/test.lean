import Mathlib.Data.Nat.Totient

open Nat Finset

def tot_loop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | i + 1, acc =>
    if n.gcd (i + 1) = 1 then
      tot_loop n i (acc + 1)
    else
      tot_loop n i acc

theorem tot_loop_eq (n : ℕ) (i : ℕ) (acc : ℕ) :
    tot_loop n i acc = acc + ((Ico 1 (i + 1)).filter (Coprime n)).card := by
  induction i generalizing acc with
  | zero =>
    simp [tot_loop]
  | succ i ih =>
    simp [tot_loop]
    by_cases h : Coprime n (i + 1)
    · have h_gcd : n.gcd (i + 1) = 1 := h
      rw [if_pos h_gcd]
      rw [ih (acc + 1)]
      have h_insert : Ico 1 (i + 2) = insert (i + 1) (Ico 1 (i + 1)) := by
        ext x
        simp only [mem_Ico, mem_insert]
        omega
      rw [h_insert, filter_insert, if_pos h]
      rw [card_insert_of_notMem]
      · omega
      · simp only [mem_filter, mem_Ico]
        omega
    · have h_gcd : n.gcd (i + 1) ≠ 1 := h
      rw [if_neg h_gcd]
      rw [ih acc]
      have h_insert : Ico 1 (i + 2) = insert (i + 1) (Ico 1 (i + 1)) := by
        ext x
        simp only [mem_Ico, mem_insert]
        omega
      rw [h_insert, filter_insert, if_neg h]


def totient_fast (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else tot_loop n (n - 1) 0

lemma range_eq_insert_Ico (n : ℕ) (h : n > 0) : range n = insert 0 (Ico 1 n) := by
  ext x
  simp only [mem_range, mem_insert, mem_Ico]
  omega

theorem totient_fast_eq_totient (n : ℕ) : totient_fast n = totient n := by
  by_cases h0 : n = 0
  · subst h0; rfl
  by_cases h1 : n = 1
  · subst h1; rfl
  have h_gt1 : n > 1 := by omega
  have h_pos : n > 0 := by omega
  unfold totient_fast
  rw [if_neg h0, if_neg h1]
  have h_sub : n - 1 + 1 = n := by omega
  rw [tot_loop_eq, h_sub, zero_add]
  unfold totient
  rw [range_eq_insert_Ico n h_pos, filter_insert]
  have h_not_coprime : ¬ Coprime n 0 := by
    intro hc
    unfold Coprime at hc
    have h_gcd : n.gcd 0 = n := n.gcd_zero_right
    rw [h_gcd] at hc
    omega
  rw [if_neg h_not_coprime]
