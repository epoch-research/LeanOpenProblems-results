import FormalConjectures.Util.ProblemImports
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
lemma tau_prime {p : ℕ} (hp : Nat.Prime p) : tau p = 2 := by
  unfold tau
  rw [hp.divisors]
  rw [Finset.card_pair]
  exact hp.ne_one.symm

lemma prime_of_tau_eq_two {n : ℕ} (hnpos : 0 < n) (ht : tau n = 2) : Nat.Prime n := by
  by_cases hn2 : 2 ≤ n
  · by_contra hnp
    rcases Nat.exists_dvd_of_not_prime hn2 hnp with ⟨m, hmn, hm1, hmnne⟩
    have hsub : ({1, m, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl | rfl
      · exact ⟨one_dvd n, Nat.pos_iff_ne_zero.mp hnpos⟩
      · exact ⟨hmn, Nat.pos_iff_ne_zero.mp hnpos⟩
      · exact ⟨dvd_rfl, Nat.pos_iff_ne_zero.mp hnpos⟩
    have hcardle := Finset.card_le_card hsub
    have hcard3 : ({1, m, n} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hmnne
      · simp [hm1]
        omega
    unfold tau at ht
    omega
  · have : n = 1 := by omega
    subst n
    unfold tau at ht
    rw [Nat.divisors_one] at ht
    simp at ht

example {n : ℕ} (hnpos : 0 < n) : tau n = 2 ↔ Nat.Prime n := by
  constructor
  · exact prime_of_tau_eq_two hnpos
  · exact tau_prime
