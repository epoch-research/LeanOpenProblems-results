import FormalConjectures.Util.ProblemImports

open Nat

theorem nat_dvd_sub {a b c : ℕ} (h : c ≤ b) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := by
  rcases h1 with ⟨x, rfl⟩
  rcases h2 with ⟨y, rfl⟩
  use x - y
  rw [← Nat.mul_sub_left_distrib]

theorem coprime_mul_sub_one (k A : ℕ) (h : 0 < k * A) : Coprime A (k * A - 1) := by
  apply Nat.coprime_of_dvd
  intro d hd1 hd2 hd3
  have hd4 : d ∣ k * A := dvd_mul_of_dvd_right hd2 k
  have h_le : k * A - 1 ≤ k * A := by omega
  have hd5 : d ∣ k * A - (k * A - 1) := nat_dvd_sub h_le hd4 hd3
  have h_sub : k * A - (k * A - 1) = 1 := by omega
  rw [h_sub] at hd5
  have hd6 : d ≤ 1 := Nat.le_of_dvd (by decide) hd5
  have : d > 1 := hd1.one_lt
  omega

theorem coprime_helper_left (n k : ℕ) (hk : Coprime (k + 1) n) (h_pos : 0 < k * (n - 1)) :
    Coprime (k + 1) (k * (n - 1) - 1) := by
  apply Nat.coprime_of_dvd
  intro d hd1 hd2 hd3
  have hd4 : d ∣ (k + 1) * (n - 1) := dvd_mul_of_dvd_left hd2 (n - 1)
  have h_eq : (k + 1) * (n - 1) = k * (n - 1) + (n - 1) := by ring
  rw [h_eq] at hd4
  have h_le : k * (n - 1) - 1 ≤ k * (n - 1) + (n - 1) := by omega
  have hd5 : d ∣ (k * (n - 1) + (n - 1)) - (k * (n - 1) - 1) := nat_dvd_sub h_le hd4 hd3
  have hn_gt : n - 1 ≥ 1 := by
    by_contra hc
    have : n - 1 = 0 := by omega
    have h_pos_rewrite := h_pos
    rw [this] at h_pos_rewrite
    simp at h_pos_rewrite
  have hn_eq : n = (n - 1) + 1 := by omega
  have h_sub : (k * (n - 1) + (n - 1)) - (k * (n - 1) - 1) = n := by omega
  rw [h_sub] at hd5
  have hd6 : d ∣ Nat.gcd (k + 1) n := Nat.dvd_gcd hd2 hd5
  have h_gcd_eq : Nat.gcd (k + 1) n = 1 := hk
  rw [h_gcd_eq] at hd6
  have hd7 : d ≤ 1 := Nat.le_of_dvd (by decide) hd6
  have : d > 1 := hd1.one_lt
  omega

theorem coprime_helper (n k : ℕ) (hk : Coprime (k + 1) n) (h_pos : 0 < k * (n - 1)) :
    Coprime ((k + 1) * (n - 1)) (k * (n - 1) - 1) := by
  have hc1 : Coprime (n - 1) (k * (n - 1) - 1) := coprime_mul_sub_one k (n - 1) h_pos
  have hc2 : Coprime (k + 1) (k * (n - 1) - 1) := coprime_helper_left n k hk h_pos
  exact Nat.Coprime.mul_left hc2 hc1




