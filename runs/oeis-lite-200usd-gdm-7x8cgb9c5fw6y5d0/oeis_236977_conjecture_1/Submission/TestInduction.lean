import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

theorem a_pos_of_exists (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Ico 1 ((n - 1) / 2 + 1))
    (h_sq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k)) :
    a n > 0 := by
  dsimp [a]
  rw [← Finset.add_sum_erase (Finset.Ico 1 ((n - 1) / 2 + 1)) _ hk]
  rw [if_pos h_sq]
  have h_nonneg : ∑ x ∈ (Finset.Ico 1 ((n - 1) / 2 + 1)).erase k, (if sqrt (totient x * totient (n - x)) ^ 2 = totient x * totient (n - x) then 1 else 0) ≥ 0 := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> omega
  omega

def check_single (n : ℕ) (k : ℕ) : Bool :=
  if hk1 : 1 ≤ k then
    if hk2 : k < (n - 1) / 2 + 1 then
      let m := totient k * totient (n - k)
      sqrt m ^ 2 == m
    else false
  else false

theorem a_pos_of_check_single (n : ℕ) (k : ℕ) (h : check_single n k = true) : a n > 0 := by
  dsimp [check_single] at h
  split_ifs at h with hk1 hk2
  · have hk : k ∈ Finset.Ico 1 ((n - 1) / 2 + 1) := by
      rw [Finset.mem_Ico]
      exact ⟨hk1, hk2⟩
    have h_sq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
      exact eq_of_beq_eq_true h
    exact a_pos_of_exists n k hk h_sq
  · contradiction
  · contradiction

def get_witness (n : ℕ) : ℕ :=
  if n == 9 then 1 else 0

def check_all_loop : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, L, R =>
    if L > R then true
    else
      check_single L (get_witness L) && check_all_loop fuel (L + 1) R

theorem check_all_loop_sound : ∀ (fuel : ℕ) (L R : ℕ) (h : check_all_loop fuel L R = true) (n : ℕ) (hn1 : L ≤ n) (hn2 : n ≤ R) (h_fuel : R - L < fuel), a n > 0
  | 0, L, R, h, n, hn1, hn2, h_fuel => by omega
  | fuel + 1, L, R, h, n, hn1, hn2, h_fuel => by
    dsimp [check_all_loop] at h
    split_ifs at h with h_le
    · omega
    · rw [Bool.and_eq_true] at h
      rcases h with ⟨h_single, h_loop⟩
      by_cases hn_eq : n = L
      · subst hn_eq
        exact a_pos_of_check_single L (get_witness L) h_single
      · have hn_gt : L + 1 ≤ n := by omega
        have h_fuel' : R - (L + 1) < fuel := by omega
        exact check_all_loop_sound fuel (L + 1) R h_loop n hn_gt hn2 h_fuel'

theorem test_9 : check_all_loop 2 9 9 = true := by decide

theorem a_pos_9 (n : ℕ) (h : 9 ≤ n ∧ n ≤ 9) : a n > 0 := by
  have h_loop : check_all_loop 2 9 9 = true := test_9
  have h_fuel : 9 - 9 < 2 := by omega
  exact check_all_loop_sound 2 9 9 h_loop n h.1 h.2 h_fuel
