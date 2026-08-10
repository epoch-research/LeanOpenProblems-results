import Mathlib

open scoped Nat.Prime

lemma coprime_thirty_dvd_not (x : ℕ) (d : ℕ) (hd : d ∣ 30) (hx : d ∣ x) (h_gt : 1 < d) :
    ¬ (30 : ℕ).Coprime x := by
  intro h_cop
  have h_gcd : d ∣ Nat.gcd 30 x := Nat.dvd_gcd hd hx
  rw [Nat.Coprime.gcd_eq_one h_cop] at h_gcd
  have : d ≤ 1 := Nat.le_of_dvd (by decide) h_gcd
  omega

lemma coprime_thirty_case_five (k : ℕ) (hk : k % 30 = 5) :
    Finset.filter ((30 : ℕ).Coprime) (Finset.Ico k (k + 15)) ⊆ {k + 2, k + 6, k + 8, k + 12, k + 14} := by
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_Ico] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have h_y_cases : y = k ∨ y = k + 1 ∨ y = k + 2 ∨ y = k + 3 ∨ y = k + 4 ∨ y = k + 5 ∨ y = k + 6 ∨ y = k + 7 ∨ y = k + 8 ∨ y = k + 9 ∨ y = k + 10 ∨ y = k + 11 ∨ y = k + 12 ∨ y = k + 13 ∨ y = k + 14 ∨ y = k + 15 := by omega
  rcases h_y_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso; exact coprime_thirty_dvd_not k 5 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · exfalso; exact coprime_thirty_dvd_not (k+1) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · left; rfl
  · exfalso; exact coprime_thirty_dvd_not (k+3) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · exfalso; exact coprime_thirty_dvd_not (k+4) 3 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · exfalso; exact coprime_thirty_dvd_not (k+5) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · right; left; rfl
  · exfalso; exact coprime_thirty_dvd_not (k+7) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · right; right; left; rfl
  · exfalso; exact coprime_thirty_dvd_not (k+9) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · exfalso; exact coprime_thirty_dvd_not (k+10) 3 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · exfalso; exact coprime_thirty_dvd_not (k+11) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · right; right; right; left; rfl
  · exfalso; exact coprime_thirty_dvd_not (k+13) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
  · right; right; right; right; rfl
  · exfalso; exact coprime_thirty_dvd_not (k+15) 2 (by decide) (Nat.dvd_of_mod_eq_zero (by omega)) (by decide) hy.2
