import Submission.Spec
open Nat Finset Rat

theorem Icc_succ_prod (n : ℕ) (f : ℕ → ℕ) :
  (Icc 1 (n + 1)).prod f = (Icc 1 n).prod f * f (n + 1) := by
  exact prod_Icc_succ_top (by omega) f

theorem maxPowDiv_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  maxPowDiv 3 (a * b) = maxPowDiv 3 a + maxPowDiv 3 b := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.mul ha hb

def v3_fast (n : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if n = 0 then 0
    else if n % 3 = 0 then 1 + v3_fast (n / 3) f
    else 0

theorem maxPowDiv_three_zero : maxPowDiv 3 0 = 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.zero

theorem maxPowDiv_three_one : maxPowDiv 3 1 = 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.one

theorem maxPowDiv_three_mul (k : ℕ) (hk : k ≠ 0) : maxPowDiv 3 (3 * k) = 1 + maxPowDiv 3 k := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  rw [padicValNat.mul (by decide) hk, padicValNat_self, add_comm]

theorem maxPowDiv_not_dvd (n : ℕ) (hn : ¬ 3 ∣ n) : maxPowDiv 3 n = 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.eq_zero_of_not_dvd hn

theorem v3_fast_eq_maxPowDiv : ∀ fuel n, n < 3^fuel → v3_fast n fuel = maxPowDiv 3 n
  | 0, n, hn => by
    have h : n = 0 := by omega
    subst h
    rw [v3_fast, maxPowDiv_three_zero]
  | f + 1, n, hn => by
    unfold v3_fast
    split_ifs with h1 h2
    · subst h1; rw [maxPowDiv_three_zero]
    · have hk : n / 3 < 3^f := by omega
      have h_div : n = 3 * (n / 3) := by
        exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2) |>.symm
      have hk_ne : n / 3 ≠ 0 := by
        intro h
        rw [h, mul_zero] at h_div
        exact h1 h_div
      rw [v3_fast_eq_maxPowDiv f (n / 3) hk]
      have h_pow : maxPowDiv 3 n = 1 + maxPowDiv 3 (n / 3) := by
        conv => lhs; rw [h_div]
        exact maxPowDiv_three_mul (n / 3) hk_ne
      rw [h_pow]
    · have h_not_dvd : ¬ 3 ∣ n := fun hdvd => h2 (Nat.mod_eq_zero_of_dvd hdvd)
      exact (maxPowDiv_not_dvd n h_not_dvd).symm

theorem sum_v3_k2_fast_eq_maxPowDiv_lem (n : ℕ)
  (sum_v3_k2_fast : ℕ → ℕ)
  (h_sum_zero : sum_v3_k2_fast 0 = 0)
  (h_sum_succ : ∀ k, sum_v3_k2_fast (k + 1) = sum_v3_k2_fast k + 2 * v3_fast (k + 1) 100)
  (h_bound : ∀ k ∈ Icc 1 n, k < 3^100) :
  sum_v3_k2_fast n = maxPowDiv 3 ((Icc 1 n).prod (fun k => k^2)) := by
  induction n with
  | zero =>
    rw [h_sum_zero, Icc_eq_empty_of_lt (by decide), prod_empty, maxPowDiv_three_one]
  | succ k ih =>
    have hk_bound : ∀ m ∈ Icc 1 k, m < 3^100 := by
      intro m hm
      have h_in : m ∈ Icc 1 (k + 1) := by
        rw [mem_Icc] at hm ⊢
        exact ⟨hm.1, Nat.le_succ_of_le hm.2⟩
      exact h_bound m h_in
    have ih_app := ih hk_bound
    rw [h_sum_succ, Icc_succ_prod]
    rw [ih_app]
    have h_in_succ : k + 1 ∈ Icc 1 (k + 1) := by rw [mem_Icc]; exact ⟨by omega, Nat.le_refl _⟩
    have hk_val : (k + 1) < 3^100 := h_bound (k + 1) h_in_succ
    rw [v3_fast_eq_maxPowDiv 100 (k + 1) hk_val]
    have h_prod_ne_zero : (Icc 1 k).prod (fun x => x^2) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro x hx
      have hx1 : 1 ≤ x := by rw [mem_Icc] at hx; exact hx.1
      positivity
    have hk1_ne_zero : (k + 1)^2 ≠ 0 := by positivity
    rw [maxPowDiv_mul h_prod_ne_zero hk1_ne_zero]
    have h_k1_ne : k + 1 ≠ 0 := by positivity
    rw [sq (k+1)]
    rw [maxPowDiv_mul h_k1_ne h_k1_ne]
    omega
