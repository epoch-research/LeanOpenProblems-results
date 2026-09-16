import Submission.Proof4
open Nat

lemma A355898_copy_pos (n : ℕ) (hn : n ≥ 1) : A355898_copy n > 0 := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => contradiction
    | succ m =>
      cases m with
      | zero => decide
      | succ j =>
        cases j with
        | zero => decide
        | succ i =>
          have h1 : i + 2 ≥ 1 := by omega
          have pos1 := ih (i + 2) (by omega) h1
          have hg : Nat.gcd (A355898_copy (i + 2)) (A355898_copy (i + 1)) > 0 := Nat.gcd_pos_of_pos_left (A355898_copy (i + 1)) pos1
          have eq_A : A355898_copy (i + 3) = Nat.gcd (A355898_copy (i + 2)) (A355898_copy (i + 1)) + (A355898_copy (i + 2) + A355898_copy (i + 1)) / Nat.gcd (A355898_copy (i + 2)) (A355898_copy (i + 1)) := rfl
          rw [eq_A]
          exact Nat.lt_of_lt_of_le hg (Nat.le_add_right _ _)

lemma contradiction_step (x y g : ℕ) (hx : x > 0) (hy : y > 0) (hg : g > 1) (hdvd1 : g ∣ x) (hdvd2 : g ∣ y) :
  g + (x + y) / g < 1 + x + y := by
  have hdvd : g ∣ (x + y) := Nat.dvd_add hdvd1 hdvd2
  set k := (x + y) / g
  have eq1 : x + y = g * k := (Nat.mul_div_cancel' hdvd).symm
  have hk : k ≥ 2 := by
    have h1 : x ≥ g := Nat.le_of_dvd hx hdvd1
    have h2 : y ≥ g := Nat.le_of_dvd hy hdvd2
    have h3 : x + y ≥ g * 2 := by omega
    have h4 : g * k ≥ g * 2 := by omega
    have hg_pos : g > 0 := by omega
    exact Nat.le_of_mul_le_mul_left h4 hg_pos
  nlinarith

lemma mod_zero_dvd {a : ℕ} (h : (a : M) = 0) : p ∣ a := by
  have h1 : (a : M).val = 0 := congrArg ZMod.val h
  have h2 : a % p = 0 := by
    have H := ZMod.val_natCast p a
    omega
  exact Nat.dvd_of_mod_eq_zero h2

lemma A355898_copy_step_lemma (n : ℕ) : A355898_copy (n + 3) = Nat.gcd (A355898_copy (n + 2)) (A355898_copy (n + 1)) + (A355898_copy (n + 2) + A355898_copy (n + 1)) / Nat.gcd (A355898_copy (n + 2)) (A355898_copy (n + 1)) := rfl

lemma apply_h_conj (h_conj : ∀ n ≥ 3775, A355898_copy n = 1 + A355898_copy (n - 1) + A355898_copy (n - 2)) (n : ℕ) (hn : n ≥ 3775) :
  A355898_copy n = 1 + A355898_copy (n - 1) + A355898_copy (n - 2) := h_conj n hn

lemma A355898_copy_contradiction (h_conj : ∀ n ≥ 3775, A355898_copy n = 1 + A355898_copy (n - 1) + A355898_copy (n - 2)) : False := by
  have H1 := A355898_copy_K_mod_p h_conj
  have H2 := A355898_copy_K_plus_1_mod_p h_conj
  have hdvd1 := mod_zero_dvd H2
  have hdvd2 := mod_zero_dvd H1
  have H_step := A355898_copy_step_lemma (3772 + K)
  have h_idx1 : 3772 + K + 2 = 3774 + K := by omega
  have h_idx2 : 3772 + K + 1 = 3773 + K := by omega
  have h_idx3 : 3772 + K + 3 = 3775 + K := by omega
  rw [h_idx1, h_idx2, h_idx3] at H_step
  have H_conj_app := apply_h_conj h_conj (3775 + K) (by omega)
  have h_idx4 : 3775 + K - 1 = 3774 + K := by omega
  have h_idx5 : 3775 + K - 2 = 3773 + K := by omega
  rw [h_idx4, h_idx5] at H_conj_app
  have pos1 := A355898_copy_pos (3774 + K) (by omega)
  have pos2 := A355898_copy_pos (3773 + K) (by omega)
  set g := Nat.gcd (A355898_copy (3774 + K)) (A355898_copy (3773 + K))
  have hdvd_g1 : p ∣ g := Nat.dvd_gcd hdvd1 hdvd2
  have hp : p > 1 := by decide
  have hg : g > 1 := Nat.lt_of_lt_of_le hp (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ pos1) hdvd_g1)
  have h_contra := contradiction_step (A355898_copy (3774 + K)) (A355898_copy (3773 + K)) g pos1 pos2 hg (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  rw [← H_step] at h_contra
  rw [H_conj_app] at h_contra
  exact Nat.lt_irrefl _ h_contra
