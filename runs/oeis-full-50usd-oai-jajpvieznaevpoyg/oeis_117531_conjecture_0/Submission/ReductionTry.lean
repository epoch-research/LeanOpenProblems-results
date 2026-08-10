import FormalConjectures.Util.ProblemImports

open Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

lemma a_lt_of_not_prime {n : ℕ} (hn : 0 < n) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 n)
    (hcomp : ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1))) : a n < n := by
  unfold a
  rw [Finset.card_lt_card]
  · exact Finset.filter_subset _ _
  · refine ⟨k, hk, ?_⟩
    simpa using hcomp
  · simp [hn]

lemma value_gt_small_q {n k q : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n)
    (hq : q ≤ n) : q < k ^ 2 - k + Nat.nth Nat.Prime (n - 1) := by
  have hpbound : n + 1 ≤ Nat.nth Nat.Prime (n - 1) := by
    have hsub : n - 1 + 2 = n + 1 := by omega
    rw [← hsub]
    exact Nat.add_two_le_nth_prime (n - 1)
  have hqpn : q < Nat.nth Nat.Prime (n - 1) := lt_of_le_of_lt hq (lt_of_lt_of_le (by omega) hpbound)
  have hnonneg : Nat.nth Nat.Prime (n - 1) ≤ k ^ 2 - k + Nat.nth Nat.Prime (n - 1) := by omega
  exact lt_of_lt_of_le hqpn hnonneg

lemma not_prime_of_small_prime_dvd {n k q : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n)
    (hqprime : Nat.Prime q) (hqn : q ≤ n)
    (hdiv : q ∣ k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) :
    ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  intro hp
  exact Nat.not_prime_of_dvd_of_lt hdiv (value_gt_small_q hn hk hqn) hqprime hp

lemma a_lt_of_small_prime_dvd {n k q : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n)
    (hqprime : Nat.Prime q) (hqn : q ≤ n)
    (hdiv : q ∣ k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) : a n < n := by
  exact a_lt_of_not_prime (by omega) hk (not_prime_of_small_prime_dvd hn hk hqprime hqn hdiv)

-- If q divides 4p-1, root k=(q+1)/2 (mod q); choose natural representative.
lemma dvd_value_of_dvd_four_p_sub_one {p q : ℕ} (hqodd : q % 2 = 1)
    (hdiv : q ∣ 4*p - 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ q ∣ k ^ 2 - k + p := by
  let k := (q + 1) / 2
  refine ⟨k, ?_, ?_, ?_⟩
  · have hqpos : 0 < q := by
      by_contra h; have : q=0 := by omega; simp [this] at hqodd
    omega
  · omega
  · -- arithmetic from q | 4p-1 and q odd; use mod maybe
    sorry
