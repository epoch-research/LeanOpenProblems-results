import FormalConjectures.Util.ProblemImports

open Nat

def TwinCenter (m : ℕ) : Prop := Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)

theorem conjecture_implies_unbounded_twin_centers
    (H : ∀ n > 0, ∃ k : ℕ,
      Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧
      Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) :
    {m : ℕ | TwinCenter m}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro B
  let n := (Nat.log 2 B).succ
  have hnB : B < 2 ^ n := by
    simpa [n] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) B
  have hnpos : 0 < n := Nat.succ_pos _
  obtain ⟨k, hk⟩ := H n hnpos
  let m := (3 ^ n - k) * (2 ^ n)
  have hmTwin : TwinCenter m := hk
  have hmpos : 0 < m := by
    by_contra hm
    push_neg at hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    have hnot : ¬ Nat.Prime (m - 1) := by simpa [hm0] using Nat.not_prime_zero
    exact hnot hmTwin.1
  have hdiv : 2 ^ n ∣ m := dvd_mul_left _ _
  have hle : 2 ^ n ≤ m := Nat.le_of_dvd hmpos hdiv
  refine ⟨m, hmTwin, lt_of_lt_of_le hnB hle⟩
