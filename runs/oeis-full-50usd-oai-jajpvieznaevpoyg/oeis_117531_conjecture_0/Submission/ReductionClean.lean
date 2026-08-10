import FormalConjectures.Util.ProblemImports

open Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

lemma a_lt_of_exists_not_prime (n : ℕ) (hn : 1 ≤ n)
    (hbad : ∃ k ∈ Finset.Icc 1 n,
      ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1))) :
    a n < n := by
  classical
  unfold a
  rw [show (let pn : ℕ := Nat.nth Nat.Prime (n - 1); card (filter (fun k => Nat.Prime (k ^ 2 - k + pn)) (Icc 1 n))) =
      card (filter (fun k => Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1))) (Icc 1 n)) by rfl]
  have hcardIcc : (Finset.Icc 1 n).card = n := by
    rw [Finset.card_Icc]
    omega
  rw [← hcardIcc]
  apply Finset.card_lt_card
  · exact Finset.filter_subset _ _
  · rcases hbad with ⟨k, hk, hkprime⟩
    exact ⟨k, hk, by simpa [hkprime]⟩

lemma value_gt_small_q {n k q : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n)
    (hq : q ≤ n) : q < k ^ 2 - k + Nat.nth Nat.Prime (n - 1) := by
  have hpbound : n + 1 ≤ Nat.nth Nat.Prime (n - 1) := by
    have hsub : n - 1 + 2 = n + 1 := by omega
    rw [← hsub]
    exact Nat.add_two_le_nth_prime (n - 1)
  have hqpn : q < Nat.nth Nat.Prime (n - 1) := by omega
  have hnonneg : Nat.nth Nat.Prime (n - 1) ≤ k ^ 2 - k + Nat.nth Nat.Prime (n - 1) := by omega
  exact lt_of_lt_of_le hqpn hnonneg

#check Nat.not_prime_of_dvd_of_lt
#check Nat.Prime.not_dvd_one

lemma not_prime_value_of_small_prime_dvd {n k q : ℕ} (hn : 1 ≤ n)
    (hk : k ∈ Finset.Icc 1 n) (hqprime : Nat.Prime q) (hqn : q ≤ n)
    (hdiv : q ∣ k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) :
    ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  intro hpv
  exact Nat.not_prime_of_dvd_of_lt hdiv hqprime.two_le (value_gt_small_q hn hk hqn) hpv

lemma a_lt_of_small_prime_dvd {n k q : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n)
    (hqprime : Nat.Prime q) (hqn : q ≤ n)
    (hdiv : q ∣ k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) : a n < n := by
  exact a_lt_of_exists_not_prime n hn ⟨k, hk, not_prime_value_of_small_prime_dvd hn hk hqprime hqn hdiv⟩
