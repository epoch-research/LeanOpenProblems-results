import FormalConjectures.Util.ProblemImports

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma x_seq_dvd_of_le (a b : ℕ) (ha : a ≥ 1) (hab : a ≤ b) : x_seq a ∣ x_seq b := by
  sorry

lemma m_q_le (q : ℕ) (hq : Nat.Prime q) (hq3 : q ≥ 3) :
    ∃ m ≤ q^2 - 2, m ≥ 1 ∧ q ∣ x_seq m := by
  sorry

lemma descent_contradiction (q : ℕ) (hq : Nat.Prime q) (hq11_ge : q ≥ 11) (hq2_prime : ¬ Nat.Prime (q - 2))
    (M G K : ℕ) (hM : M ∣ q - 2) (h_eq : M = G * K)
    (hG_dvd_seq : G ∣ x_seq ((q - 2) * q - 1))
    (hG_dvd_N : G ∣ (q - 2) * q) : False := by
  sorry
  termination_by K
