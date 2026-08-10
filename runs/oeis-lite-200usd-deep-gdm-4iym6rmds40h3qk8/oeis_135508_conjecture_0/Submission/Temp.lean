
import FormalConjectures.Util.ProblemImports
import Submission.Test2

open Nat

lemma case_A_contradiction (q : ℕ) (hq : Nat.Prime q) (hq5 : q ≥ 5)
    (ih : ∀ m < q, Nat.Prime m → m ∣ x_seq (m * m - 1))
    (h_ndiv : ¬ q ∣ x_seq (q - 1))
    (hp : Nat.Prime (q + 2))
    (h_not_dvd : ¬ q ∣ x_seq (q * q - 1))
    (h_dvd_p1 : q + 2 ∣ x_seq (q + 1)) : False := by
  have h_q_gt_5 : q > 5 := by
    by_contra! h_le
    have : q = 5 := by omega
    subst q
    have h_dvd : 5 ∣ x_seq 24 := by decide
    exact h_not_dvd h_dvd
  have h_comp_q2 : ¬ Nat.Prime (q - 2) := by
    intro h_pr
    have hq_mod_3 : q % 3 = 2 := by
      have h1 : q % 3 ≠ 0 := by
        intro hc
        have : q ∣ 3 := Nat.dvd_of_mod_eq_zero hc
        have : q = 3 := by omega
        omega
      have h2 : (q + 2) % 3 ≠ 0 := by
        intro hc
        have : q + 2 ∣ 3 := Nat.dvd_of_mod_eq_zero hc
        have h_eq := Nat.Prime.eq_one_or_self_of_dvd hp 3 this
        rcases h_eq with h1 | h2
        · contradiction
        · exact h2
      omega
    have h_3_dvd_q2 : 3 ∣ q - 2 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    have h_q2_eq_3 : q - 2 = 3 := by
      have h_eq := Nat.Prime.eq_one_or_self_of_dvd h_pr 3 h_3_dvd_q2
      rcases h_eq with h1 | h2
      · contradiction
      · exact h2
    omega
  sorry

