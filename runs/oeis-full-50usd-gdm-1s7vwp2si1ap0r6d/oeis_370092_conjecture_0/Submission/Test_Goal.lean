import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset Nat

theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  use totient k
  constructor
  · exact dvd_refl (totient k)
  · rw [eventually_periodic]
    use k
    intro n hn
    rw [a_mod_k_eq_a_int, a_mod_k_eq_a_int]
    have h_eq_d : n = k + (n - k) := (Nat.add_sub_of_le hn).symm
    rw [h_eq_d]
    generalize h_d : n - k = d
    clear h_d h_eq_d hn n
    induction' d using Nat.strong_induction_on with d ih
    have h_rec1 : (a_int (k + d + totient k) : ZMod k) = (-1 : ZMod k)^(k + d + totient k) + Finset.sum (Finset.range (k + d + totient k)) (fun i =>
      ((k + d + totient k).choose (i + 1) : ZMod k) * C (i + 1) * a_int (k + d + totient k - (i + 1))
    ) := a_int_cast_rec (k + d + totient k) (by omega) k
    have h_rec2 : (a_int (k + d) : ZMod k) = (-1 : ZMod k)^(k + d) + Finset.sum (Finset.range (k + d)) (fun i =>
      ((k + d).choose (i + 1) : ZMod k) * C (i + 1) * a_int (k + d - (i + 1))
    ) := a_int_cast_rec (k + d) (by omega) k
    sorry
