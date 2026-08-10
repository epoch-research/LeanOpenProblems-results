import FormalConjectures.Util.ProblemImports

open Nat

theorem nat_dvd_sub {a b c : ℕ} (h : c ≤ b) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := by
  rcases h1 with ⟨x, rfl⟩
  rcases h2 with ⟨y, rfl⟩
  use x - y
  rw [← Nat.mul_sub_left_distrib]

lemma exists_prime_mod_eq (n : ℕ) (hn : 2 < n) : ∃ P, Nat.Prime P ∧ P ≡ n - 2 [MOD n - 1] := by
  have h_ne : n - 1 ≠ 0 := by omega
  have h_cop : Coprime (n - 2) (n - 1) := by
    apply Nat.coprime_of_dvd
    intro d hd1 hd2 hd3
    have h_sub : (n - 1) - (n - 2) = 1 := by omega
    have hd4 : d ∣ (n - 1) - (n - 2) := nat_dvd_sub (by omega) hd3 hd2
    rw [h_sub] at hd4
    have hd5 : d ≤ 1 := Nat.le_of_dvd (by decide) hd4
    have : d > 1 := hd1.one_lt
    omega
  rcases Nat.forall_exists_prime_gt_and_modEq (n - 1) h_ne h_cop with ⟨P, hP_gt, hP_prime, hP_mod⟩
  exact ⟨P, hP_prime, hP_mod⟩

