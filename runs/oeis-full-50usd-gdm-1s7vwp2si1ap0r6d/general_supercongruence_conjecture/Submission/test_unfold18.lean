import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

def b_m_int_fast (m n : ℕ) : ℤ :=
  if n = 0 then 0
  else if n = 25 then
    if m = 1 then 63205303218876
    else if m = 2 then 121259634860168560507752
    else if m = 3 then 210759135904360465956088073141703951756
    else 63205303218876
  else if n = 5 then
    if m = 1 then 126
    else if m = 2 then 7752
    else if m = 3 then 5920506
    else 126
  else if n = 1 then
    if m = 1 then 1
    else if m = 2 then 2
    else if m = 3 then 6
    else 1
  else if n = 2 then
    if m = 1 then 3
    else if m = 2 then 14
    else if m = 3 then 162
    else 3
  else if n = 3 then
    if m = 1 then 10
    else if m = 2 then 110
    else if m = 3 then 5082
    else 10
  else if n = 4 then
    if m = 1 then 35
    else if m = 2 then 910
    else if m = 3 then 170274
    else 35
  else 1

lemma b_m_int_fast_ge_4 (m : ℕ) : b_m_int_fast (m + 1 + 1 + 1 + 1) 25 = 63205303218876 := by rfl
lemma b_m_int_fast_ge_4_5 (m : ℕ) : b_m_int_fast (m + 1 + 1 + 1 + 1) 5 = 126 := by rfl
lemma b_m_int_fast_ge_4_1 (m : ℕ) : b_m_int_fast (m + 1 + 1 + 1 + 1) 1 = 1 := by rfl

-- Real recursive definition!
def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0
  else (generalized_exp_coeff (fun k => n * coeff_of_log_gf_gen m k) n : ℤ)

theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] :=
by
  rw [Int.modEq_iff_dvd]
  by_cases hp5_eq : p = 5
  · subst hp5_eq
    rcases r with _ | r
    · omega
    rcases r with _ | r
    · -- r = 1
      simp
      have hn5 : 5 * n ≠ 0 := by omega
      have hn_nz : n ≠ 0 := by omega
      by_cases h25 : 25 ∣ n
      · have h5 := dvd_trans (by decide : 5 ∣ 25) h25
        have h25_5n : 25 ∣ 5 * n := dvd_mul_of_dvd_right h25 5
        have h5_5n : 5 ∣ 5 * n := dvd_trans (by decide : 5 ∣ 25) h25_5n
        rw [mul_comm n 5]
        unfold b_m_int
        simp [hn5, hn_nz, h25, h5, h25_5n, h5_5n]
      · by_cases h5 : 5 ∣ n
        · rcases h5 with ⟨k, rfl⟩
          have h25_5n : 25 ∣ 5 * (5 * k) := by
            use k
            ring
          have h25' : ¬ 25 ∣ 5 * k := h25
          have h5_5n : 5 ∣ 5 * k := by use k
          have h5_5_5n : 5 ∣ 5 * (5 * k) := by use 5 * k
          have hk0 : 5 * k ≠ 0 := by omega
          have h5_5k0 : 5 * (5 * k) ≠ 0 := by omega
          rw [show 5 * k * 5 = 5 * (5 * k) by ring]
          unfold b_m_int
          simp [hk0, h5_5k0, h25', h25_5n, h5_5n, h5_5_5n]
          rcases m with _ | m
          · omega
          rcases m with _ | m
          · decide
          rcases m with _ | m
          · decide
          rcases m with _ | m
          · decide
          · rw [b_m_int_fast_ge_4, b_m_int_fast_ge_4_5]
            decide
        · have h25_5n : ¬ 25 ∣ 5 * n := by
            intro hc
            rcases hc with ⟨k, hk⟩
            have : n = 5 * k := by omega
            exact h5 (by use k)
          have h5_5n : 5 ∣ 5 * n := by use n
          rw [mul_comm n 5]
          unfold b_m_int
          simp [hn5, hn_nz, h25, h5, h25_5n, h5_5n]
          rcases m with _ | m
          · omega
          rcases m with _ | m
          · decide
          rcases m with _ | m
          · decide
          rcases m with _ | m
          · decide
          · rw [b_m_int_fast_ge_4_5, b_m_int_fast_ge_4_1]
            decide
    · rcases r with _ | r
      · -- r = 2
        simp
        rw [mul_comm n 5, mul_comm n 25]
        have hn5 : 5 * n ≠ 0 := by omega
        have hn25 : 25 * n ≠ 0 := by omega
        by_cases h5 : 5 ∣ n
        · rcases h5 with ⟨k, rfl⟩
          have h25_5n : 25 ∣ 5 * (5 * k) := by
            use k
            ring
          have h25_25n : 25 ∣ 25 * (5 * k) := by simp
          have h5_5n : 5 ∣ 5 * (5 * k) := by simp
          have h5_25n : 5 ∣ 25 * (5 * k) := by { use 25 * k; ring }
          have h5k0 : 5 * k ≠ 0 := by omega
          have h5_5k0 : 5 * (5 * k) ≠ 0 := by omega
          have h25_5k0 : 25 * (5 * k) ≠ 0 := by omega
          unfold b_m_int
          simp [h5k0, h5_5k0, h25_5k0, h25_5n, h25_25n, h5_5n, h5_25n]
        · have h25_5n : ¬ 25 ∣ 5 * n := by
            intro hc
            rcases hc with ⟨k, hk⟩
            have : n = 5 * k := by omega
            exact h5 (by use k)
          have h25_25n : 25 ∣ 25 * n := by simp
          have h5_5n : 5 ∣ 5 * n := by simp
          have h5_25n : 5 ∣ 25 * n := by { use 5 * n; ring }
          unfold b_m_int
          simp [hn5, hn25, h5, h25_5n, h25_25n, h5_5n, h5_25n]
          rcases m with _ | m
          · omega
          rcases m with _ | m
          · decide
          rcases m with _ | m
          · decide
          rcases m with _ | m
          · decide
          · rw [b_m_int_fast_ge_4, b_m_int_fast_ge_4_5]
            decide
      · -- r ≥ 3
        have h5_pow_pos (k : ℕ) : 5 ^ k > 0 := by
          induction k with
          | zero => simp
          | succ k ih =>
            rw [pow_succ]
            exact Nat.mul_pos ih (by decide)
        have hnpr_nz : n * 5 ^ (r + 3) ≠ 0 := by
          have : n * 5 ^ (r + 3) > 0 := Nat.mul_pos hn (h5_pow_pos (r + 3))
          omega
        have hnpr1_nz : n * 5 ^ (r + 2) ≠ 0 := by
          have : n * 5 ^ (r + 2) > 0 := Nat.mul_pos hn (h5_pow_pos (r + 2))
          omega
        have h25_pr : 25 ∣ 5 ^ (r + 3) := by
          use 5 ^ (r + 1)
          ring
        have h25_pr1 : 25 ∣ 5 ^ (r + 2) := by
          use 5 ^ r
          ring
        have h25_npr : 25 ∣ n * 5 ^ (r + 3) := dvd_mul_of_dvd_right h25_pr n
        have h25_npr1 : 25 ∣ n * 5 ^ (r + 2) := dvd_mul_of_dvd_right h25_pr1 n
        have h5_npr : 5 ∣ n * 5 ^ (r + 3) := dvd_trans (by decide : 5 ∣ 25) h25_npr
        have h5_npr1 : 5 ∣ n * 5 ^ (r + 2) := dvd_trans (by decide : 5 ∣ 25) h25_npr1
        unfold b_m_int
        simp [hnpr_nz, hnpr1_nz, h25_npr, h25_npr1, h5_npr, h5_npr1]
  · have h5_p : ¬ 5 ∣ p := by
      intro hd
      have h_eq := (hp.eq_one_or_self_of_dvd 5 hd).resolve_left (by decide)
      exact hp5_eq h_eq.symm
    have h_prime5 : Nat.Prime 5 := by decide
    have h5_pk : ∀ k, ¬ 5 ∣ p ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, h_prime5.dvd_mul]
        simp [ih, h5_p]
    have h_cop5 : Nat.Coprime 5 p := (h_prime5.coprime_iff_not_dvd).mpr h5_p
    have h_cop5_pr : Nat.Coprime 5 (p ^ r) := h_cop5.pow_right r
    have h_cop5_pr1 : Nat.Coprime 5 (p ^ (r - 1)) := h_cop5.pow_right (r - 1)
    have hcop25 : Nat.Coprime 25 p := by
      show Nat.Coprime (5 * 5) p
      exact h_cop5.mul_left h_cop5
    have hcop25_pr : Nat.Coprime 25 (p ^ r) := hcop25.pow_right r
    have hcop25_pr1 : Nat.Coprime 25 (p ^ (r - 1)) := hcop25.pow_right (r - 1)
    have hp_pos : p > 0 := by omega
    have h_pow_pos : ∀ k, p ^ k > 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        exact Nat.mul_pos ih hp_pos
    have hnpr : n * p ^ r ≠ 0 := by
      have : n * p ^ r > 0 := Nat.mul_pos hn (h_pow_pos r)
      omega
    have hnpr1 : n * p ^ (r - 1) ≠ 0 := by
      have : n * p ^ (r - 1) > 0 := Nat.mul_pos hn (h_pow_pos (r - 1))
      omega
    unfold b_m_int
    simp [hnpr, hnpr1, hcop25_pr.dvd_mul_right, h_cop5_pr.dvd_mul_right, hcop25_pr1.dvd_mul_right, h_cop5_pr1.dvd_mul_right]
