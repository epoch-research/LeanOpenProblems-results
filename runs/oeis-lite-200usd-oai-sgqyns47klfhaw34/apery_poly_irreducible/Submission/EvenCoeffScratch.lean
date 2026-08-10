import FormalConjectures.Util.ProblemImports
open Nat Polynomial

lemma choose_mul_choose_add_eq (n k : ℕ) (hk : k ≤ n) :
    (n + k).choose (2 * k) * (2 * k).choose k = (n + k).choose k * n.choose k := by
  have hsk : k ≤ 2 * k := by omega
  have h := Nat.choose_mul (n := n + k) (k := 2 * k) (s := k) hsk
  simpa [Nat.add_sub_cancel, Nat.mul_sub_right_distrib, hk, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, two_mul] using h

lemma two_dvd_apery_coeff_nat (n k : ℕ) (hk0 : 0 < k) (hkn : k ≤ n) :
    2 ∣ (n.choose k) ^ 2 * ((n + k).choose k) := by
  have hcentral : 2 ∣ (2 * k).choose k := by
    simpa [Nat.centralBinom_eq_two_mul_choose] using Nat.two_dvd_centralBinom_of_one_le (n := k) hk0
  rcases hcentral with ⟨t, ht⟩
  use t * (n + k).choose (2 * k) * n.choose k
  have hid := choose_mul_choose_add_eq n k hkn
  calc
    (n.choose k) ^ 2 * ((n + k).choose k)
        = ((n + k).choose k * n.choose k) * n.choose k := by ring
    _ = ((n + k).choose (2 * k) * (2 * k).choose k) * n.choose k := by rw [hid]
    _ = ((n + k).choose (2 * k) * (2 * t)) * n.choose k := by rw [ht]
    _ = 2 * (t * (n + k).choose (2 * k) * n.choose k) := by ring
