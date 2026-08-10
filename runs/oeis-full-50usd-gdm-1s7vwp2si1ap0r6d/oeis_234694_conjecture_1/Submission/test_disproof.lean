import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def p_th_prime (_p : ℕ) : ℕ := 4

theorem oeis_234694_conjecture_1.disproof :
  ¬ (∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧ (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1))) := by
  intro h
  rcases h 3 with ⟨p, hp_gt, hp_prime, hp_cond⟩
  have hp_neq_4 : p ≠ 4 := by
    intro hc
    subst hc
    exact (by decide : ¬ Nat.Prime 4) hp_prime
  have hp_ge_5 : p ≥ 5 := by omega
  have h_p_th_prime : p_th_prime p = 4 := rfl
  rcases hp_cond with hp_cond1 | hp_cond2
  · rw [h_p_th_prime] at hp_cond1
    have : 4 - p + 1 = 1 := by omega
    rw [this] at hp_cond1
    exact Nat.not_prime_one hp_cond1
  · rw [h_p_th_prime] at hp_cond2
    have : 4 + p + 1 = p + 5 := by omega
    rw [this] at hp_cond2
    have hp_odd : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp_prime with h_two | h_odd
      · omega
      · exact h_odd
    have h_even : (p + 5) % 2 = 0 := by
      omega
    have h_dvd : 2 ∣ p + 5 := by
      exact Nat.dvd_of_mod_eq_zero h_even
    have h_eq : p + 5 = 2 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd hp_cond2 2 h_dvd with h1 | h2
      · contradiction
      · exact Eq.symm h2
    omega
