import FormalConjectures.Util.ProblemImports

open Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

lemma a_lt_of_exists_not_prime (n : ℕ) (hn : 1 ≤ n)
    (hbad : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1))) :
    a n < n := by
  rcases hbad with ⟨k, hk, hnp⟩
  unfold a
  have hss : ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ) ⊂ Icc 1 n := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have : k ∈ ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ) := by
      simpa [heq] using hk
    exact hnp ((Finset.mem_filter.mp this).2)
  have hc := Finset.card_lt_card hss
  simpa [Nat.card_Icc, hn] using hc

lemma not_prime_value_of_small_prime_dvd {n k q : ℕ} (hn : 1 ≤ n)
    (hk : k ∈ Finset.Icc 1 n) (hqprime : Nat.Prime q) (hqn : q ≤ n)
    (hdiv : q ∣ k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) :
    ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  apply Nat.not_prime_of_dvd_of_lt hdiv hqprime.two_le
  have hpbound0 := Nat.add_two_le_nth_prime (n - 1)
  have hpbound : n < Nat.nth Nat.Prime (n - 1) := by omega
  exact lt_of_le_of_lt hqn (lt_of_lt_of_le hpbound (Nat.le_add_left _ _))

lemma a_lt_of_small_prime_dvd (n : ℕ) (hn : 1 ≤ n)
    (hbad : ∃ k ∈ Finset.Icc 1 n, ∃ q, Nat.Prime q ∧ q ≤ n ∧
      q ∣ k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) :
    a n < n := by
  rcases hbad with ⟨k, hk, q, hqprime, hqn, hdiv⟩
  exact a_lt_of_exists_not_prime n hn ⟨k, hk, not_prime_value_of_small_prime_dvd hn hk hqprime hqn hdiv⟩
