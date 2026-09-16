import Mathlib
import Submission.Spec
import Submission.Proof20
import Submission.Proof18

open Nat BigOperators

lemma odd_pow_minus_one (k : ℕ) (hk : k ≥ 1) : Odd (2 ^ k - 1) := by
  have : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc 2 ^ k = 2 ^ (1 + (k - 1)) := by rw [add_tsub_cancel_of_le hk]
      _ = 2 ^ 1 * 2 ^ (k - 1) := pow_add 2 1 (k - 1)
      _ = 2 * 2 ^ (k - 1) := by ring
  rw [this]
  have hpos : 2 ^ (k - 1) ≥ 1 := by
    have h1 : 2 ≥ 1 := by omega
    exact Nat.one_le_pow (k - 1) 2 h1
  have h2 : 2 * 2 ^ (k - 1) ≥ 2 := by nlinarith
  have h3 : 2 * 2 ^ (k - 1) - 1 = 2 * (2 ^ (k - 1) - 1) + 1 := by omega
  rw [h3]
  use 2 ^ (k - 1) - 1

lemma P_odd (n : ℕ) (hn2 : n > 2) :
  ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) % 2 = 1 := by
  have h_odd : Odd ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
    apply Finset.prod_induction (s := Finset.Ico 1 (n - 1)) (p := Odd)
    · intro a b ha hb
      exact Odd.mul ha hb
    · exact odd_one
    · intro x hx
      rw [Finset.mem_Ico] at hx
      exact odd_pow_minus_one x hx.1
  rcases h_odd with ⟨m, hm⟩
  rw [hm]
  omega

lemma padicValNat_P_two (n : ℕ) (hn2 : n > 2) :
  padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = 0 := by
  have H : ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) % 2 = 1 := P_odd n hn2
  have h_prod_pos : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
    intro h
    rw [h] at H
    omega
  by_contra h_neq
  have h_pos : padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) ≥ 1 := by omega
  have h_dvd : 2 ^ 1 ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := (padicValNat_dvd_iff_le h_prod_pos).mpr h_pos
  have h2 : 2 ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
    have : 2 ^ 1 = 2 := by rfl
    rw [← this]
    exact h_dvd
  have hm : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  omega
