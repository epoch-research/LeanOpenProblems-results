import Mathlib
open Nat Filter Topology

def a (n : ℕ) : ℕ := (Finset.Icc 1 n).sum fun k => (n.choose k) % (2 ^ k)
def M (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))

lemma M_eq (n : ℕ) : ∃ k ≤ n, M n = min (n.choose k) (2 ^ k) := by
  have h : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (succ_pos n)⟩
  rcases Finset.exists_mem_eq_sup (Finset.range (n + 1)) h (fun k => min (n.choose k) (2 ^ k)) with ⟨k, hk, hM⟩
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hM⟩

lemma a_ge_term (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) : (n.choose k) % (2 ^ k) ≤ a n := by
  dsimp [a]
  have hk : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
  rw [← Finset.add_sum_erase _ _ hk]
  exact Nat.le_add_right _ _

lemma M_le_n_mul_a (n : ℕ) (hn : 1 ≤ n) : M n ≤ n * a n := by
  by_cases hn1 : n = 1
  · subst hn1
    have hM1 : M 1 = 1 := rfl
    have ha1 : a 1 = 1 := rfl
    rw [hM1, ha1]
  have hn2 : 2 ≤ n := by omega
  rcases M_eq n with ⟨k, hkn, hM⟩
  have hk1 : 1 ≤ k := by
    by_contra h
    push_neg at h
    have hk0 : k = 0 := Nat.lt_one_iff.mp h
    rw [hk0, choose_zero_right, pow_zero, min_self] at hM
    have H : 2 ≤ M n := by
      have : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
      have H1 := @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) 1 this
      simp only [choose_one_right, pow_one] at H1
      calc 2 ≤ min n 2 := le_min hn2 (by decide)
           _ ≤ M n := H1
    linarith
  by_cases h_case : n.choose k < 2 ^ k
  · have h1 : M n = n.choose k := by rw [hM, min_eq_left (le_of_lt h_case)]
    have h2 : (n.choose k) % (2 ^ k) = n.choose k := Nat.mod_eq_of_lt h_case
    have h3 : n.choose k ≤ a n := by
      calc n.choose k = (n.choose k) % (2 ^ k) := h2.symm
           _ ≤ a n := a_ge_term n k hk1 hkn
    have Hfinal1 : M n = n.choose k := h1
    have Hfinal2 : n.choose k ≤ a n := h3
    have Hfinal3 : a n ≤ n * a n := Nat.le_mul_of_pos_left _ hn
    exact le_trans (le_of_eq Hfinal1) (le_trans Hfinal2 Hfinal3)
  · have h_case' := not_lt.mp h_case
    have h1 : M n = 2 ^ k := by rw [hM, min_eq_right h_case']
    have hkn_strict : k < n := by
      by_contra hc
      have hk_eq_n : k = n := le_antisymm hkn (not_lt.mp hc)
      rw [hk_eq_n, choose_self] at h_case'
      have h_pow : 2 ^ n ≤ 1 := h_case'
      have h_pow2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by simp
             _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
      linarith
    have hk_plus_1 : k + 1 ≤ n := hkn_strict
    have h_case2 : n.choose (k + 1) < 2 ^ (k + 1) := by
      by_contra hc2
      push_neg at hc2
      have H : 2 ^ (k + 1) ≤ M n := by
        have : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk_plus_1)
        have H1 := @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) (k + 1) this
        calc 2 ^ (k + 1) ≤ min (n.choose (k + 1)) (2 ^ (k + 1)) := le_min hc2 le_rfl
             _ ≤ M n := H1
      rw [h1, pow_succ, mul_two] at H
      have hp : 0 < 2 ^ k := by positivity
      linarith
    have h2 : (n.choose (k + 1)) % (2 ^ (k + 1)) = n.choose (k + 1) := Nat.mod_eq_of_lt h_case2
    have h3 : n.choose (k + 1) ≤ a n := by
      calc n.choose (k + 1) = (n.choose (k + 1)) % (2 ^ (k + 1)) := h2.symm
           _ ≤ a n := a_ge_term n (k + 1) (by omega) hk_plus_1
    have h4 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := by
      rw [← choose_succ_right_eq, mul_comm]
    have h5 : M n * 1 ≤ n.choose k * (n - k) := by
      calc M n * 1 = 2 ^ k * 1 := by rw [h1]
           _ ≤ 2 ^ k * (n - k) := Nat.mul_le_mul_left _ (by omega)
           _ ≤ n.choose k * (n - k) := Nat.mul_le_mul_right _ h_case'
    rw [mul_one, ← h4] at h5
    have Hfinal1 : M n ≤ n.choose (k + 1) * (k + 1) := h5
    have Hfinal2 : n.choose (k + 1) * (k + 1) ≤ a n * n := Nat.mul_le_mul h3 hk_plus_1
    have Hfinal3 : M n ≤ a n * n := le_trans Hfinal1 Hfinal2
    exact le_trans Hfinal3 (le_of_eq (mul_comm _ _))
