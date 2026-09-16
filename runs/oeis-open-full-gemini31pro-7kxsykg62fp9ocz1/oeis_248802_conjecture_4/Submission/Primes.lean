import Submission.Util

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

lemma not_dvd_3 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 3 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (3 : ℕ).Prime := by decide
  have h_flt : (2^(3-1)) % 3 = 1 := by decide
  have h_per : exp_seq (3-1) 1 = exp_seq (3-1) 0 := by decide
  have h_check : check_prime_period_cond 3 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 3 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 3 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 3 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 3 n hp h_flt (exp_seq_eq (3-1) n) H_val

lemma not_dvd_5 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 5 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (5 : ℕ).Prime := by decide
  have h_flt : (2^(5-1)) % 5 = 1 := by decide
  have h_per : exp_seq (5-1) 1 = exp_seq (5-1) 0 := by decide
  have h_check : check_prime_period_cond 5 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 5 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 5 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 5 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 5 n hp h_flt (exp_seq_eq (5-1) n) H_val

lemma not_dvd_7 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 7 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (7 : ℕ).Prime := by decide
  have h_flt : (2^(7-1)) % 7 = 1 := by decide
  have h_per : exp_seq (7-1) 1 = exp_seq (7-1) 0 := by decide
  have h_check : check_prime_period_cond 7 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 7 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 7 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 7 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 7 n hp h_flt (exp_seq_eq (7-1) n) H_val

lemma not_dvd_11 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 11 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (11 : ℕ).Prime := by decide
  have h_flt : (2^(11-1)) % 11 = 1 := by decide
  have h_per : exp_seq (11-1) 2 = exp_seq (11-1) 0 := by decide
  have h_check : check_prime_period_cond 11 2 (fun _ => false) = true := by decide
  have H_val : val_mod_p 11 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 11 2 (fun _ => false) h_check (n % 2) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 11 2 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 11 n hp h_flt (exp_seq_eq (11-1) n) H_val

lemma not_dvd_13 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 13 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (13 : ℕ).Prime := by decide
  have h_flt : (2^(13-1)) % 13 = 1 := by decide
  have h_per : exp_seq (13-1) 1 = exp_seq (13-1) 0 := by decide
  have h_check : check_prime_period_cond 13 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 13 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 13 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 13 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 13 n hp h_flt (exp_seq_eq (13-1) n) H_val

lemma not_dvd_17 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 17 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (17 : ℕ).Prime := by decide
  have h_flt : (2^(17-1)) % 17 = 1 := by decide
  have h_per : exp_seq (17-1) 1 = exp_seq (17-1) 0 := by decide
  have h_check : check_prime_period_cond 17 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 17 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 17 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 17 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 17 n hp h_flt (exp_seq_eq (17-1) n) H_val

lemma not_dvd_19 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 19 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (19 : ℕ).Prime := by decide
  have h_flt : (2^(19-1)) % 19 = 1 := by decide
  have h_per : exp_seq (19-1) 3 = exp_seq (19-1) 0 := by decide
  have h_check : check_prime_period_cond 19 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 19 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 19 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 19 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 19 n hp h_flt (exp_seq_eq (19-1) n) H_val

lemma not_dvd_23 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 23 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (23 : ℕ).Prime := by decide
  have h_flt : (2^(23-1)) % 23 = 1 := by decide
  have h_per : exp_seq (23-1) 5 = exp_seq (23-1) 0 := by decide
  have h_check : check_prime_period_cond 23 5 (fun _ => false) = true := by decide
  have H_val : val_mod_p 23 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 23 5 (fun _ => false) h_check (n % 5) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 23 5 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 23 n hp h_flt (exp_seq_eq (23-1) n) H_val

lemma not_dvd_29 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 29 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (29 : ℕ).Prime := by decide
  have h_flt : (2^(29-1)) % 29 = 1 := by decide
  have h_per : exp_seq (29-1) 3 = exp_seq (29-1) 0 := by decide
  have h_check : check_prime_period_cond 29 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 29 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 29 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 29 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 29 n hp h_flt (exp_seq_eq (29-1) n) H_val

lemma not_dvd_31 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 31 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (31 : ℕ).Prime := by decide
  have h_flt : (2^(31-1)) % 31 = 1 := by decide
  have h_per : exp_seq (31-1) 2 = exp_seq (31-1) 0 := by decide
  have h_check : check_prime_period_cond 31 2 (fun _ => false) = true := by decide
  have H_val : val_mod_p 31 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 31 2 (fun _ => false) h_check (n % 2) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 31 2 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 31 n hp h_flt (exp_seq_eq (31-1) n) H_val

lemma not_dvd_37 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 37 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (37 : ℕ).Prime := by decide
  have h_flt : (2^(37-1)) % 37 = 1 := by decide
  have h_per : exp_seq (37-1) 3 = exp_seq (37-1) 0 := by decide
  have h_check : check_prime_period_cond 37 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 37 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 37 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 37 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 37 n hp h_flt (exp_seq_eq (37-1) n) H_val

lemma not_dvd_41 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 41 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (41 : ℕ).Prime := by decide
  have h_flt : (2^(41-1)) % 41 = 1 := by decide
  have h_per : exp_seq (41-1) 2 = exp_seq (41-1) 0 := by decide
  have h_check : check_prime_period_cond 41 2 (fun _ => false) = true := by decide
  have H_val : val_mod_p 41 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 41 2 (fun _ => false) h_check (n % 2) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 41 2 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 41 n hp h_flt (exp_seq_eq (41-1) n) H_val

lemma not_dvd_43 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 43 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (43 : ℕ).Prime := by decide
  have h_flt : (2^(43-1)) % 43 = 1 := by decide
  have h_per : exp_seq (43-1) 3 = exp_seq (43-1) 0 := by decide
  have h_check : check_prime_period_cond 43 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 43 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 43 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 43 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 43 n hp h_flt (exp_seq_eq (43-1) n) H_val

lemma not_dvd_47 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 47 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (47 : ℕ).Prime := by decide
  have h_flt : (2^(47-1)) % 47 = 1 := by decide
  have h_per : exp_seq (47-1) 11 = exp_seq (47-1) 0 := by decide
  have h_check : check_prime_period_cond 47 11 (fun _ => false) = true := by decide
  have H_val : val_mod_p 47 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 47 11 (fun _ => false) h_check (n % 11) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 47 11 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 47 n hp h_flt (exp_seq_eq (47-1) n) H_val

lemma not_dvd_53 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 53 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (53 : ℕ).Prime := by decide
  have h_flt : (2^(53-1)) % 53 = 1 := by decide
  have h_per : exp_seq (53-1) 6 = exp_seq (53-1) 0 := by decide
  have h_check : check_prime_period_cond 53 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 53 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 53 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 53 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 53 n hp h_flt (exp_seq_eq (53-1) n) H_val

lemma not_dvd_59 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 59 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (59 : ℕ).Prime := by decide
  have h_flt : (2^(59-1)) % 59 = 1 := by decide
  have h_per : exp_seq (59-1) 14 = exp_seq (59-1) 0 := by decide
  have h_check : check_prime_period_cond 59 14 (fun _ => false) = true := by decide
  have H_val : val_mod_p 59 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 59 14 (fun _ => false) h_check (n % 14) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 59 14 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 59 n hp h_flt (exp_seq_eq (59-1) n) H_val

lemma not_dvd_61 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 61 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (61 : ℕ).Prime := by decide
  have h_flt : (2^(61-1)) % 61 = 1 := by decide
  have h_per : exp_seq (61-1) 2 = exp_seq (61-1) 0 := by decide
  have h_check : check_prime_period_cond 61 2 (fun _ => false) = true := by decide
  have H_val : val_mod_p 61 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 61 2 (fun _ => false) h_check (n % 2) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 61 2 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 61 n hp h_flt (exp_seq_eq (61-1) n) H_val

lemma not_dvd_67 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 67 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (67 : ℕ).Prime := by decide
  have h_flt : (2^(67-1)) % 67 = 1 := by decide
  have h_per : exp_seq (67-1) 5 = exp_seq (67-1) 0 := by decide
  have h_check : check_prime_period_cond 67 5 cond_67 = true := by decide
  have H_val : val_mod_p 67 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 67 5 cond_67 h_check (n % 5) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 67 5 n h_per
    rw [h_mod]
    apply H
    have H2 : ¬ cond_67 (n % 5) = true := by
      intro H3
      exact hC1 (C1_of_mod_5_eq_2 n (cond_67_imp n H3))
    exact Bool.eq_false_iff.mpr H2
  exact not_dvd_of_val_mod_p 67 n hp h_flt (exp_seq_eq (67-1) n) H_val

lemma not_dvd_71 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 71 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (71 : ℕ).Prime := by decide
  have h_flt : (2^(71-1)) % 71 = 1 := by decide
  have h_per : exp_seq (71-1) 6 = exp_seq (71-1) 0 := by decide
  have h_check : check_prime_period_cond 71 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 71 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 71 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 71 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 71 n hp h_flt (exp_seq_eq (71-1) n) H_val

lemma not_dvd_73 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 73 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (73 : ℕ).Prime := by decide
  have h_flt : (2^(73-1)) % 73 = 1 := by decide
  have h_per : exp_seq (73-1) 3 = exp_seq (73-1) 0 := by decide
  have h_check : check_prime_period_cond 73 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 73 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 73 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 73 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 73 n hp h_flt (exp_seq_eq (73-1) n) H_val

lemma not_dvd_79 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 79 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (79 : ℕ).Prime := by decide
  have h_flt : (2^(79-1)) % 79 = 1 := by decide
  have h_per : exp_seq (79-1) 6 = exp_seq (79-1) 0 := by decide
  have h_check : check_prime_period_cond 79 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 79 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 79 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 79 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 79 n hp h_flt (exp_seq_eq (79-1) n) H_val

lemma not_dvd_83 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 83 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (83 : ℕ).Prime := by decide
  have h_flt : (2^(83-1)) % 83 = 1 := by decide
  have h_per : exp_seq (83-1) 10 = exp_seq (83-1) 0 := by decide
  have h_check : check_prime_period_cond 83 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 83 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 83 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 83 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 83 n hp h_flt (exp_seq_eq (83-1) n) H_val

lemma not_dvd_89 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 89 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (89 : ℕ).Prime := by decide
  have h_flt : (2^(89-1)) % 89 = 1 := by decide
  have h_per : exp_seq (89-1) 5 = exp_seq (89-1) 0 := by decide
  have h_check : check_prime_period_cond 89 5 (fun _ => false) = true := by decide
  have H_val : val_mod_p 89 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 89 5 (fun _ => false) h_check (n % 5) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 89 5 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 89 n hp h_flt (exp_seq_eq (89-1) n) H_val

lemma not_dvd_97 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 97 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (97 : ℕ).Prime := by decide
  have h_flt : (2^(97-1)) % 97 = 1 := by decide
  have h_per : exp_seq (97-1) 1 = exp_seq (97-1) 0 := by decide
  have h_check : check_prime_period_cond 97 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 97 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 97 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 97 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 97 n hp h_flt (exp_seq_eq (97-1) n) H_val

lemma not_dvd_101 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 101 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (101 : ℕ).Prime := by decide
  have h_flt : (2^(101-1)) % 101 = 1 := by decide
  have h_per : exp_seq (101-1) 10 = exp_seq (101-1) 0 := by decide
  have h_check : check_prime_period_cond 101 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 101 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 101 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 101 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 101 n hp h_flt (exp_seq_eq (101-1) n) H_val

lemma not_dvd_103 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 103 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (103 : ℕ).Prime := by decide
  have h_flt : (2^(103-1)) % 103 = 1 := by decide
  have h_per : exp_seq (103-1) 4 = exp_seq (103-1) 0 := by decide
  have h_check : check_prime_period_cond 103 4 (fun _ => false) = true := by decide
  have H_val : val_mod_p 103 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 103 4 (fun _ => false) h_check (n % 4) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 103 4 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 103 n hp h_flt (exp_seq_eq (103-1) n) H_val

lemma not_dvd_107 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 107 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (107 : ℕ).Prime := by decide
  have h_flt : (2^(107-1)) % 107 = 1 := by decide
  have h_per : exp_seq (107-1) 26 = exp_seq (107-1) 0 := by decide
  have h_check : check_prime_period_cond 107 26 (fun _ => false) = true := by decide
  have H_val : val_mod_p 107 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 107 26 (fun _ => false) h_check (n % 26) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 107 26 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 107 n hp h_flt (exp_seq_eq (107-1) n) H_val

lemma not_dvd_109 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 109 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (109 : ℕ).Prime := by decide
  have h_flt : (2^(109-1)) % 109 = 1 := by decide
  have h_per : exp_seq (109-1) 9 = exp_seq (109-1) 0 := by decide
  have h_check : check_prime_period_cond 109 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 109 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 109 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 109 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 109 n hp h_flt (exp_seq_eq (109-1) n) H_val

lemma not_dvd_113 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 113 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (113 : ℕ).Prime := by decide
  have h_flt : (2^(113-1)) % 113 = 1 := by decide
  have h_per : exp_seq (113-1) 3 = exp_seq (113-1) 0 := by decide
  have h_check : check_prime_period_cond 113 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 113 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 113 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 113 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 113 n hp h_flt (exp_seq_eq (113-1) n) H_val

lemma not_dvd_127 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 127 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (127 : ℕ).Prime := by decide
  have h_flt : (2^(127-1)) % 127 = 1 := by decide
  have h_per : exp_seq (127-1) 3 = exp_seq (127-1) 0 := by decide
  have h_check : check_prime_period_cond 127 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 127 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 127 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 127 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 127 n hp h_flt (exp_seq_eq (127-1) n) H_val

lemma not_dvd_131 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 131 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (131 : ℕ).Prime := by decide
  have h_flt : (2^(131-1)) % 131 = 1 := by decide
  have h_per : exp_seq (131-1) 6 = exp_seq (131-1) 0 := by decide
  have h_check : check_prime_period_cond 131 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 131 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 131 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 131 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 131 n hp h_flt (exp_seq_eq (131-1) n) H_val

lemma not_dvd_137 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 137 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (137 : ℕ).Prime := by decide
  have h_flt : (2^(137-1)) % 137 = 1 := by decide
  have h_per : exp_seq (137-1) 4 = exp_seq (137-1) 0 := by decide
  have h_check : check_prime_period_cond 137 4 (fun _ => false) = true := by decide
  have H_val : val_mod_p 137 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 137 4 (fun _ => false) h_check (n % 4) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 137 4 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 137 n hp h_flt (exp_seq_eq (137-1) n) H_val

lemma not_dvd_139 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 139 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (139 : ℕ).Prime := by decide
  have h_flt : (2^(139-1)) % 139 = 1 := by decide
  have h_per : exp_seq (139-1) 11 = exp_seq (139-1) 0 := by decide
  have h_check : check_prime_period_cond 139 11 (fun _ => false) = true := by decide
  have H_val : val_mod_p 139 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 139 11 (fun _ => false) h_check (n % 11) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 139 11 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 139 n hp h_flt (exp_seq_eq (139-1) n) H_val

lemma not_dvd_149 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 149 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (149 : ℕ).Prime := by decide
  have h_flt : (2^(149-1)) % 149 = 1 := by decide
  have h_per : exp_seq (149-1) 18 = exp_seq (149-1) 0 := by decide
  have h_check : check_prime_period_cond 149 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 149 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 149 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 149 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 149 n hp h_flt (exp_seq_eq (149-1) n) H_val

lemma not_dvd_151 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 151 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (151 : ℕ).Prime := by decide
  have h_flt : (2^(151-1)) % 151 = 1 := by decide
  have h_per : exp_seq (151-1) 10 = exp_seq (151-1) 0 := by decide
  have h_check : check_prime_period_cond 151 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 151 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 151 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 151 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 151 n hp h_flt (exp_seq_eq (151-1) n) H_val

lemma not_dvd_157 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 157 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (157 : ℕ).Prime := by decide
  have h_flt : (2^(157-1)) % 157 = 1 := by decide
  have h_per : exp_seq (157-1) 6 = exp_seq (157-1) 0 := by decide
  have h_check : check_prime_period_cond 157 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 157 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 157 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 157 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 157 n hp h_flt (exp_seq_eq (157-1) n) H_val

lemma not_dvd_163 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 163 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (163 : ℕ).Prime := by decide
  have h_flt : (2^(163-1)) % 163 = 1 := by decide
  have h_per : exp_seq (163-1) 27 = exp_seq (163-1) 0 := by decide
  have h_check : check_prime_period_cond 163 27 (fun _ => false) = true := by decide
  have H_val : val_mod_p 163 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 163 27 (fun _ => false) h_check (n % 27) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 163 27 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 163 n hp h_flt (exp_seq_eq (163-1) n) H_val

lemma not_dvd_167 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 167 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (167 : ℕ).Prime := by decide
  have h_flt : (2^(167-1)) % 167 = 1 := by decide
  have h_per : exp_seq (167-1) 41 = exp_seq (167-1) 0 := by decide
  have h_check : check_prime_period_cond 167 41 (fun _ => false) = true := by decide
  have H_val : val_mod_p 167 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 167 41 (fun _ => false) h_check (n % 41) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 167 41 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 167 n hp h_flt (exp_seq_eq (167-1) n) H_val

lemma not_dvd_173 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 173 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (173 : ℕ).Prime := by decide
  have h_flt : (2^(173-1)) % 173 = 1 := by decide
  have h_per : exp_seq (173-1) 7 = exp_seq (173-1) 0 := by decide
  have h_check : check_prime_period_cond 173 7 (fun _ => false) = true := by decide
  have H_val : val_mod_p 173 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 173 7 (fun _ => false) h_check (n % 7) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 173 7 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 173 n hp h_flt (exp_seq_eq (173-1) n) H_val

lemma not_dvd_179 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 179 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (179 : ℕ).Prime := by decide
  have h_flt : (2^(179-1)) % 179 = 1 := by decide
  have h_per : exp_seq (179-1) 11 = exp_seq (179-1) 0 := by decide
  have h_check : check_prime_period_cond 179 11 (fun _ => false) = true := by decide
  have H_val : val_mod_p 179 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 179 11 (fun _ => false) h_check (n % 11) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 179 11 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 179 n hp h_flt (exp_seq_eq (179-1) n) H_val

lemma not_dvd_181 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 181 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (181 : ℕ).Prime := by decide
  have h_flt : (2^(181-1)) % 181 = 1 := by decide
  have h_per : exp_seq (181-1) 6 = exp_seq (181-1) 0 := by decide
  have h_check : check_prime_period_cond 181 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 181 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 181 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 181 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 181 n hp h_flt (exp_seq_eq (181-1) n) H_val

lemma not_dvd_191 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 191 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (191 : ℕ).Prime := by decide
  have h_flt : (2^(191-1)) % 191 = 1 := by decide
  have h_per : exp_seq (191-1) 18 = exp_seq (191-1) 0 := by decide
  have h_check : check_prime_period_cond 191 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 191 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 191 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 191 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 191 n hp h_flt (exp_seq_eq (191-1) n) H_val

lemma not_dvd_193 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 193 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (193 : ℕ).Prime := by decide
  have h_flt : (2^(193-1)) % 193 = 1 := by decide
  have h_per : exp_seq (193-1) 1 = exp_seq (193-1) 0 := by decide
  have h_check : check_prime_period_cond 193 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 193 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 193 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 193 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 193 n hp h_flt (exp_seq_eq (193-1) n) H_val

lemma not_dvd_197 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 197 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (197 : ℕ).Prime := by decide
  have h_flt : (2^(197-1)) % 197 = 1 := by decide
  have h_per : exp_seq (197-1) 21 = exp_seq (197-1) 0 := by decide
  have h_check : check_prime_period_cond 197 21 (fun _ => false) = true := by decide
  have H_val : val_mod_p 197 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 197 21 (fun _ => false) h_check (n % 21) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 197 21 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 197 n hp h_flt (exp_seq_eq (197-1) n) H_val

lemma not_dvd_199 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 199 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (199 : ℕ).Prime := by decide
  have h_flt : (2^(199-1)) % 199 = 1 := by decide
  have h_per : exp_seq (199-1) 15 = exp_seq (199-1) 0 := by decide
  have h_check : check_prime_period_cond 199 15 (fun _ => false) = true := by decide
  have H_val : val_mod_p 199 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 199 15 (fun _ => false) h_check (n % 15) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 199 15 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 199 n hp h_flt (exp_seq_eq (199-1) n) H_val

lemma not_dvd_211 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 211 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (211 : ℕ).Prime := by decide
  have h_flt : (2^(211-1)) % 211 = 1 := by decide
  have h_per : exp_seq (211-1) 6 = exp_seq (211-1) 0 := by decide
  have h_check : check_prime_period_cond 211 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 211 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 211 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 211 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 211 n hp h_flt (exp_seq_eq (211-1) n) H_val

lemma not_dvd_223 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 223 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (223 : ℕ).Prime := by decide
  have h_flt : (2^(223-1)) % 223 = 1 := by decide
  have h_per : exp_seq (223-1) 18 = exp_seq (223-1) 0 := by decide
  have h_check : check_prime_period_cond 223 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 223 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 223 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 223 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 223 n hp h_flt (exp_seq_eq (223-1) n) H_val

lemma not_dvd_227 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 227 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (227 : ℕ).Prime := by decide
  have h_flt : (2^(227-1)) % 227 = 1 := by decide
  have h_per : exp_seq (227-1) 14 = exp_seq (227-1) 0 := by decide
  have h_check : check_prime_period_cond 227 14 (fun _ => false) = true := by decide
  have H_val : val_mod_p 227 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 227 14 (fun _ => false) h_check (n % 14) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 227 14 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 227 n hp h_flt (exp_seq_eq (227-1) n) H_val

lemma not_dvd_229 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 229 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (229 : ℕ).Prime := by decide
  have h_flt : (2^(229-1)) % 229 = 1 := by decide
  have h_per : exp_seq (229-1) 9 = exp_seq (229-1) 0 := by decide
  have h_check : check_prime_period_cond 229 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 229 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 229 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 229 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 229 n hp h_flt (exp_seq_eq (229-1) n) H_val

lemma not_dvd_233 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 233 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (233 : ℕ).Prime := by decide
  have h_flt : (2^(233-1)) % 233 = 1 := by decide
  have h_per : exp_seq (233-1) 14 = exp_seq (233-1) 0 := by decide
  have h_check : check_prime_period_cond 233 14 (fun _ => false) = true := by decide
  have H_val : val_mod_p 233 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 233 14 (fun _ => false) h_check (n % 14) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 233 14 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 233 n hp h_flt (exp_seq_eq (233-1) n) H_val

lemma not_dvd_239 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 239 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (239 : ℕ).Prime := by decide
  have h_flt : (2^(239-1)) % 239 = 1 := by decide
  have h_per : exp_seq (239-1) 12 = exp_seq (239-1) 0 := by decide
  have h_check : check_prime_period_cond 239 12 (fun _ => false) = true := by decide
  have H_val : val_mod_p 239 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 239 12 (fun _ => false) h_check (n % 12) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 239 12 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 239 n hp h_flt (exp_seq_eq (239-1) n) H_val

lemma not_dvd_241 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 241 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (241 : ℕ).Prime := by decide
  have h_flt : (2^(241-1)) % 241 = 1 := by decide
  have h_per : exp_seq (241-1) 2 = exp_seq (241-1) 0 := by decide
  have h_check : check_prime_period_cond 241 2 (fun _ => false) = true := by decide
  have H_val : val_mod_p 241 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 241 2 (fun _ => false) h_check (n % 2) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 241 2 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 241 n hp h_flt (exp_seq_eq (241-1) n) H_val

lemma not_dvd_251 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 251 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (251 : ℕ).Prime := by decide
  have h_flt : (2^(251-1)) % 251 = 1 := by decide
  have h_per : exp_seq (251-1) 50 = exp_seq (251-1) 0 := by decide
  have h_check : check_prime_period_cond 251 50 (fun _ => false) = true := by decide
  have H_val : val_mod_p 251 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 251 50 (fun _ => false) h_check (n % 50) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 251 50 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 251 n hp h_flt (exp_seq_eq (251-1) n) H_val

lemma not_dvd_257 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 257 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (257 : ℕ).Prime := by decide
  have h_flt : (2^(257-1)) % 257 = 1 := by decide
  have h_per : exp_seq (257-1) 1 = exp_seq (257-1) 0 := by decide
  have h_check : check_prime_period_cond 257 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 257 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 257 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 257 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 257 n hp h_flt (exp_seq_eq (257-1) n) H_val

lemma not_dvd_263 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 263 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (263 : ℕ).Prime := by decide
  have h_flt : (2^(263-1)) % 263 = 1 := by decide
  have h_per : exp_seq (263-1) 65 = exp_seq (263-1) 0 := by decide
  have h_check : check_prime_period_cond 263 65 (fun _ => false) = true := by decide
  have H_val : val_mod_p 263 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 263 65 (fun _ => false) h_check (n % 65) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 263 65 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 263 n hp h_flt (exp_seq_eq (263-1) n) H_val

lemma not_dvd_269 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 269 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (269 : ℕ).Prime := by decide
  have h_flt : (2^(269-1)) % 269 = 1 := by decide
  have h_per : exp_seq (269-1) 33 = exp_seq (269-1) 0 := by decide
  have h_check : check_prime_period_cond 269 33 (fun _ => false) = true := by decide
  have H_val : val_mod_p 269 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 269 33 (fun _ => false) h_check (n % 33) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 269 33 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 269 n hp h_flt (exp_seq_eq (269-1) n) H_val

lemma not_dvd_271 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 271 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (271 : ℕ).Prime := by decide
  have h_flt : (2^(271-1)) % 271 = 1 := by decide
  have h_per : exp_seq (271-1) 18 = exp_seq (271-1) 0 := by decide
  have h_check : check_prime_period_cond 271 18 cond_271 = true := by decide
  have H_val : val_mod_p 271 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 271 18 cond_271 h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 271 18 n h_per
    rw [h_mod]
    apply H
    have H2 : ¬ cond_271 (n % 18) = true := by
      intro H3
      rcases (C2_or_C1_of_mod_18_eq_11 n (cond_271_imp n H3)) with H_C1 | H_C2
      · exact hC1 H_C1
      · exact hC2 H_C2
    exact Bool.eq_false_iff.mpr H2
  exact not_dvd_of_val_mod_p 271 n hp h_flt (exp_seq_eq (271-1) n) H_val

lemma not_dvd_277 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 277 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (277 : ℕ).Prime := by decide
  have h_flt : (2^(277-1)) % 277 = 1 := by decide
  have h_per : exp_seq (277-1) 11 = exp_seq (277-1) 0 := by decide
  have h_check : check_prime_period_cond 277 11 (fun _ => false) = true := by decide
  have H_val : val_mod_p 277 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 277 11 (fun _ => false) h_check (n % 11) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 277 11 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 277 n hp h_flt (exp_seq_eq (277-1) n) H_val

lemma not_dvd_281 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 281 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (281 : ℕ).Prime := by decide
  have h_flt : (2^(281-1)) % 281 = 1 := by decide
  have h_per : exp_seq (281-1) 6 = exp_seq (281-1) 0 := by decide
  have h_check : check_prime_period_cond 281 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 281 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 281 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 281 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 281 n hp h_flt (exp_seq_eq (281-1) n) H_val

lemma not_dvd_283 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 283 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (283 : ℕ).Prime := by decide
  have h_flt : (2^(283-1)) % 283 = 1 := by decide
  have h_per : exp_seq (283-1) 23 = exp_seq (283-1) 0 := by decide
  have h_check : check_prime_period_cond 283 23 (fun _ => false) = true := by decide
  have H_val : val_mod_p 283 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 283 23 (fun _ => false) h_check (n % 23) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 283 23 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 283 n hp h_flt (exp_seq_eq (283-1) n) H_val

lemma not_dvd_293 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 293 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (293 : ℕ).Prime := by decide
  have h_flt : (2^(293-1)) % 293 = 1 := by decide
  have h_per : exp_seq (293-1) 9 = exp_seq (293-1) 0 := by decide
  have h_check : check_prime_period_cond 293 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 293 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 293 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 293 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 293 n hp h_flt (exp_seq_eq (293-1) n) H_val

lemma not_dvd_307 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 307 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (307 : ℕ).Prime := by decide
  have h_flt : (2^(307-1)) % 307 = 1 := by decide
  have h_per : exp_seq (307-1) 12 = exp_seq (307-1) 0 := by decide
  have h_check : check_prime_period_cond 307 12 (fun _ => false) = true := by decide
  have H_val : val_mod_p 307 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 307 12 (fun _ => false) h_check (n % 12) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 307 12 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 307 n hp h_flt (exp_seq_eq (307-1) n) H_val

lemma not_dvd_311 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 311 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (311 : ℕ).Prime := by decide
  have h_flt : (2^(311-1)) % 311 = 1 := by decide
  have h_per : exp_seq (311-1) 10 = exp_seq (311-1) 0 := by decide
  have h_check : check_prime_period_cond 311 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 311 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 311 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 311 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 311 n hp h_flt (exp_seq_eq (311-1) n) H_val

lemma not_dvd_313 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 313 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (313 : ℕ).Prime := by decide
  have h_flt : (2^(313-1)) % 313 = 1 := by decide
  have h_per : exp_seq (313-1) 6 = exp_seq (313-1) 0 := by decide
  have h_check : check_prime_period_cond 313 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 313 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 313 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 313 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 313 n hp h_flt (exp_seq_eq (313-1) n) H_val

lemma not_dvd_317 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 317 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (317 : ℕ).Prime := by decide
  have h_flt : (2^(317-1)) % 317 = 1 := by decide
  have h_per : exp_seq (317-1) 39 = exp_seq (317-1) 0 := by decide
  have h_check : check_prime_period_cond 317 39 (fun _ => false) = true := by decide
  have H_val : val_mod_p 317 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 317 39 (fun _ => false) h_check (n % 39) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 317 39 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 317 n hp h_flt (exp_seq_eq (317-1) n) H_val

lemma not_dvd_331 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 331 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (331 : ℕ).Prime := by decide
  have h_flt : (2^(331-1)) % 331 = 1 := by decide
  have h_per : exp_seq (331-1) 10 = exp_seq (331-1) 0 := by decide
  have h_check : check_prime_period_cond 331 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 331 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 331 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 331 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 331 n hp h_flt (exp_seq_eq (331-1) n) H_val

lemma not_dvd_337 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 337 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (337 : ℕ).Prime := by decide
  have h_flt : (2^(337-1)) % 337 = 1 := by decide
  have h_per : exp_seq (337-1) 3 = exp_seq (337-1) 0 := by decide
  have h_check : check_prime_period_cond 337 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 337 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 337 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 337 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 337 n hp h_flt (exp_seq_eq (337-1) n) H_val

lemma not_dvd_347 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 347 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (347 : ℕ).Prime := by decide
  have h_flt : (2^(347-1)) % 347 = 1 := by decide
  have h_per : exp_seq (347-1) 86 = exp_seq (347-1) 0 := by decide
  have h_check : check_prime_period_cond 347 86 (fun _ => false) = true := by decide
  have H_val : val_mod_p 347 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 347 86 (fun _ => false) h_check (n % 86) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 347 86 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 347 n hp h_flt (exp_seq_eq (347-1) n) H_val

lemma not_dvd_349 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 349 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (349 : ℕ).Prime := by decide
  have h_flt : (2^(349-1)) % 349 = 1 := by decide
  have h_per : exp_seq (349-1) 14 = exp_seq (349-1) 0 := by decide
  have h_check : check_prime_period_cond 349 14 (fun _ => false) = true := by decide
  have H_val : val_mod_p 349 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 349 14 (fun _ => false) h_check (n % 14) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 349 14 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 349 n hp h_flt (exp_seq_eq (349-1) n) H_val

lemma not_dvd_353 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 353 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (353 : ℕ).Prime := by decide
  have h_flt : (2^(353-1)) % 353 = 1 := by decide
  have h_per : exp_seq (353-1) 5 = exp_seq (353-1) 0 := by decide
  have h_check : check_prime_period_cond 353 5 (fun _ => false) = true := by decide
  have H_val : val_mod_p 353 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 353 5 (fun _ => false) h_check (n % 5) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 353 5 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 353 n hp h_flt (exp_seq_eq (353-1) n) H_val

lemma not_dvd_359 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 359 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (359 : ℕ).Prime := by decide
  have h_flt : (2^(359-1)) % 359 = 1 := by decide
  have h_per : exp_seq (359-1) 89 = exp_seq (359-1) 0 := by decide
  have h_check : check_prime_period_cond 359 89 (fun _ => false) = true := by decide
  have H_val : val_mod_p 359 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 359 89 (fun _ => false) h_check (n % 89) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 359 89 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 359 n hp h_flt (exp_seq_eq (359-1) n) H_val

lemma not_dvd_367 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 367 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (367 : ℕ).Prime := by decide
  have h_flt : (2^(367-1)) % 367 = 1 := by decide
  have h_per : exp_seq (367-1) 30 = exp_seq (367-1) 0 := by decide
  have h_check : check_prime_period_cond 367 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 367 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 367 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 367 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 367 n hp h_flt (exp_seq_eq (367-1) n) H_val

lemma not_dvd_373 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 373 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (373 : ℕ).Prime := by decide
  have h_flt : (2^(373-1)) % 373 = 1 := by decide
  have h_per : exp_seq (373-1) 5 = exp_seq (373-1) 0 := by decide
  have h_check : check_prime_period_cond 373 5 (fun _ => false) = true := by decide
  have H_val : val_mod_p 373 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 373 5 (fun _ => false) h_check (n % 5) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 373 5 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 373 n hp h_flt (exp_seq_eq (373-1) n) H_val

lemma not_dvd_379 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 379 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (379 : ℕ).Prime := by decide
  have h_flt : (2^(379-1)) % 379 = 1 := by decide
  have h_per : exp_seq (379-1) 9 = exp_seq (379-1) 0 := by decide
  have h_check : check_prime_period_cond 379 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 379 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 379 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 379 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 379 n hp h_flt (exp_seq_eq (379-1) n) H_val

lemma not_dvd_383 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 383 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (383 : ℕ).Prime := by decide
  have h_flt : (2^(383-1)) % 383 = 1 := by decide
  have h_per : exp_seq (383-1) 95 = exp_seq (383-1) 0 := by decide
  have h_check : check_prime_period_cond 383 95 (fun _ => false) = true := by decide
  have H_val : val_mod_p 383 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 383 95 (fun _ => false) h_check (n % 95) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 383 95 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 383 n hp h_flt (exp_seq_eq (383-1) n) H_val

lemma not_dvd_389 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 389 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (389 : ℕ).Prime := by decide
  have h_flt : (2^(389-1)) % 389 = 1 := by decide
  have h_per : exp_seq (389-1) 24 = exp_seq (389-1) 0 := by decide
  have h_check : check_prime_period_cond 389 24 (fun _ => false) = true := by decide
  have H_val : val_mod_p 389 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 389 24 (fun _ => false) h_check (n % 24) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 389 24 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 389 n hp h_flt (exp_seq_eq (389-1) n) H_val

lemma not_dvd_397 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 397 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (397 : ℕ).Prime := by decide
  have h_flt : (2^(397-1)) % 397 = 1 := by decide
  have h_per : exp_seq (397-1) 15 = exp_seq (397-1) 0 := by decide
  have h_check : check_prime_period_cond 397 15 (fun _ => false) = true := by decide
  have H_val : val_mod_p 397 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 397 15 (fun _ => false) h_check (n % 15) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 397 15 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 397 n hp h_flt (exp_seq_eq (397-1) n) H_val

lemma not_dvd_401 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 401 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (401 : ℕ).Prime := by decide
  have h_flt : (2^(401-1)) % 401 = 1 := by decide
  have h_per : exp_seq (401-1) 10 = exp_seq (401-1) 0 := by decide
  have h_check : check_prime_period_cond 401 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 401 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 401 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 401 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 401 n hp h_flt (exp_seq_eq (401-1) n) H_val

lemma not_dvd_409 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 409 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (409 : ℕ).Prime := by decide
  have h_flt : (2^(409-1)) % 409 = 1 := by decide
  have h_per : exp_seq (409-1) 4 = exp_seq (409-1) 0 := by decide
  have h_check : check_prime_period_cond 409 4 (fun _ => false) = true := by decide
  have H_val : val_mod_p 409 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 409 4 (fun _ => false) h_check (n % 4) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 409 4 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 409 n hp h_flt (exp_seq_eq (409-1) n) H_val

lemma not_dvd_419 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 419 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (419 : ℕ).Prime := by decide
  have h_flt : (2^(419-1)) % 419 = 1 := by decide
  have h_per : exp_seq (419-1) 45 = exp_seq (419-1) 0 := by decide
  have h_check : check_prime_period_cond 419 45 (fun _ => false) = true := by decide
  have H_val : val_mod_p 419 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 419 45 (fun _ => false) h_check (n % 45) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 419 45 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 419 n hp h_flt (exp_seq_eq (419-1) n) H_val

lemma not_dvd_421 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 421 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (421 : ℕ).Prime := by decide
  have h_flt : (2^(421-1)) % 421 = 1 := by decide
  have h_per : exp_seq (421-1) 6 = exp_seq (421-1) 0 := by decide
  have h_check : check_prime_period_cond 421 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 421 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 421 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 421 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 421 n hp h_flt (exp_seq_eq (421-1) n) H_val

lemma not_dvd_431 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 431 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (431 : ℕ).Prime := by decide
  have h_flt : (2^(431-1)) % 431 = 1 := by decide
  have h_per : exp_seq (431-1) 14 = exp_seq (431-1) 0 := by decide
  have h_check : check_prime_period_cond 431 14 (fun _ => false) = true := by decide
  have H_val : val_mod_p 431 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 431 14 (fun _ => false) h_check (n % 14) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 431 14 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 431 n hp h_flt (exp_seq_eq (431-1) n) H_val

lemma not_dvd_433 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 433 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (433 : ℕ).Prime := by decide
  have h_flt : (2^(433-1)) % 433 = 1 := by decide
  have h_per : exp_seq (433-1) 9 = exp_seq (433-1) 0 := by decide
  have h_check : check_prime_period_cond 433 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 433 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 433 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 433 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 433 n hp h_flt (exp_seq_eq (433-1) n) H_val

lemma not_dvd_439 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 439 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (439 : ℕ).Prime := by decide
  have h_flt : (2^(439-1)) % 439 = 1 := by decide
  have h_per : exp_seq (439-1) 9 = exp_seq (439-1) 0 := by decide
  have h_check : check_prime_period_cond 439 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 439 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 439 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 439 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 439 n hp h_flt (exp_seq_eq (439-1) n) H_val

lemma not_dvd_443 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 443 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (443 : ℕ).Prime := by decide
  have h_flt : (2^(443-1)) % 443 = 1 := by decide
  have h_per : exp_seq (443-1) 12 = exp_seq (443-1) 0 := by decide
  have h_check : check_prime_period_cond 443 12 (fun _ => false) = true := by decide
  have H_val : val_mod_p 443 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 443 12 (fun _ => false) h_check (n % 12) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 443 12 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 443 n hp h_flt (exp_seq_eq (443-1) n) H_val

lemma not_dvd_449 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 449 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (449 : ℕ).Prime := by decide
  have h_flt : (2^(449-1)) % 449 = 1 := by decide
  have h_per : exp_seq (449-1) 3 = exp_seq (449-1) 0 := by decide
  have h_check : check_prime_period_cond 449 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 449 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 449 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 449 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 449 n hp h_flt (exp_seq_eq (449-1) n) H_val

lemma not_dvd_457 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 457 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (457 : ℕ).Prime := by decide
  have h_flt : (2^(457-1)) % 457 = 1 := by decide
  have h_per : exp_seq (457-1) 9 = exp_seq (457-1) 0 := by decide
  have h_check : check_prime_period_cond 457 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 457 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 457 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 457 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 457 n hp h_flt (exp_seq_eq (457-1) n) H_val

lemma not_dvd_461 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 461 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (461 : ℕ).Prime := by decide
  have h_flt : (2^(461-1)) % 461 = 1 := by decide
  have h_per : exp_seq (461-1) 22 = exp_seq (461-1) 0 := by decide
  have h_check : check_prime_period_cond 461 22 (fun _ => false) = true := by decide
  have H_val : val_mod_p 461 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 461 22 (fun _ => false) h_check (n % 22) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 461 22 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 461 n hp h_flt (exp_seq_eq (461-1) n) H_val

lemma not_dvd_463 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 463 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (463 : ℕ).Prime := by decide
  have h_flt : (2^(463-1)) % 463 = 1 := by decide
  have h_per : exp_seq (463-1) 15 = exp_seq (463-1) 0 := by decide
  have h_check : check_prime_period_cond 463 15 (fun _ => false) = true := by decide
  have H_val : val_mod_p 463 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 463 15 (fun _ => false) h_check (n % 15) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 463 15 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 463 n hp h_flt (exp_seq_eq (463-1) n) H_val

lemma not_dvd_467 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 467 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (467 : ℕ).Prime := by decide
  have h_flt : (2^(467-1)) % 467 = 1 := by decide
  have h_per : exp_seq (467-1) 1 = exp_seq (467-1) 0 := by decide
  have h_check : check_prime_period_cond 467 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 467 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 467 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 467 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 467 n hp h_flt (exp_seq_eq (467-1) n) H_val

lemma not_dvd_479 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 479 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (479 : ℕ).Prime := by decide
  have h_flt : (2^(479-1)) % 479 = 1 := by decide
  have h_per : exp_seq (479-1) 119 = exp_seq (479-1) 0 := by decide
  have h_check : check_prime_period_cond 479 119 (fun _ => false) = true := by decide
  have H_val : val_mod_p 479 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 479 119 (fun _ => false) h_check (n % 119) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 479 119 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 479 n hp h_flt (exp_seq_eq (479-1) n) H_val

lemma not_dvd_487 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 487 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (487 : ℕ).Prime := by decide
  have h_flt : (2^(487-1)) % 487 = 1 := by decide
  have h_per : exp_seq (487-1) 81 = exp_seq (487-1) 0 := by decide
  have h_check : check_prime_period_cond 487 81 (fun _ => false) = true := by decide
  have H_val : val_mod_p 487 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 487 81 (fun _ => false) h_check (n % 81) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 487 81 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 487 n hp h_flt (exp_seq_eq (487-1) n) H_val

lemma not_dvd_491 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 491 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (491 : ℕ).Prime := by decide
  have h_flt : (2^(491-1)) % 491 = 1 := by decide
  have h_per : exp_seq (491-1) 42 = exp_seq (491-1) 0 := by decide
  have h_check : check_prime_period_cond 491 42 (fun _ => false) = true := by decide
  have H_val : val_mod_p 491 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 491 42 (fun _ => false) h_check (n % 42) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 491 42 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 491 n hp h_flt (exp_seq_eq (491-1) n) H_val

lemma not_dvd_499 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 499 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (499 : ℕ).Prime := by decide
  have h_flt : (2^(499-1)) % 499 = 1 := by decide
  have h_per : exp_seq (499-1) 41 = exp_seq (499-1) 0 := by decide
  have h_check : check_prime_period_cond 499 41 (fun _ => false) = true := by decide
  have H_val : val_mod_p 499 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 499 41 (fun _ => false) h_check (n % 41) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 499 41 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 499 n hp h_flt (exp_seq_eq (499-1) n) H_val

lemma not_dvd_503 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 503 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (503 : ℕ).Prime := by decide
  have h_flt : (2^(503-1)) % 503 = 1 := by decide
  have h_per : exp_seq (503-1) 25 = exp_seq (503-1) 0 := by decide
  have h_check : check_prime_period_cond 503 25 (fun _ => false) = true := by decide
  have H_val : val_mod_p 503 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 503 25 (fun _ => false) h_check (n % 25) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 503 25 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 503 n hp h_flt (exp_seq_eq (503-1) n) H_val

lemma not_dvd_509 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 509 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (509 : ℕ).Prime := by decide
  have h_flt : (2^(509-1)) % 509 = 1 := by decide
  have h_per : exp_seq (509-1) 7 = exp_seq (509-1) 0 := by decide
  have h_check : check_prime_period_cond 509 7 (fun _ => false) = true := by decide
  have H_val : val_mod_p 509 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 509 7 (fun _ => false) h_check (n % 7) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 509 7 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 509 n hp h_flt (exp_seq_eq (509-1) n) H_val

lemma not_dvd_521 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 521 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (521 : ℕ).Prime := by decide
  have h_flt : (2^(521-1)) % 521 = 1 := by decide
  have h_per : exp_seq (521-1) 6 = exp_seq (521-1) 0 := by decide
  have h_check : check_prime_period_cond 521 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 521 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 521 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 521 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 521 n hp h_flt (exp_seq_eq (521-1) n) H_val

lemma not_dvd_523 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 523 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (523 : ℕ).Prime := by decide
  have h_flt : (2^(523-1)) % 523 = 1 := by decide
  have h_per : exp_seq (523-1) 42 = exp_seq (523-1) 0 := by decide
  have h_check : check_prime_period_cond 523 42 cond_523 = true := by decide
  have H_val : val_mod_p 523 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 523 42 cond_523 h_check (n % 42) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 523 42 n h_per
    rw [h_mod]
    apply H
    have H2 : ¬ cond_523 (n % 42) = true := by
      intro H3
      rcases (C3_or_C1_of_mod_42_eq_26 n (cond_523_imp n H3)) with H_C1 | H_C3
      · exact hC1 H_C1
      · exact hC3 H_C3
    exact Bool.eq_false_iff.mpr H2
  exact not_dvd_of_val_mod_p 523 n hp h_flt (exp_seq_eq (523-1) n) H_val

lemma not_dvd_541 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 541 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (541 : ℕ).Prime := by decide
  have h_flt : (2^(541-1)) % 541 = 1 := by decide
  have h_per : exp_seq (541-1) 18 = exp_seq (541-1) 0 := by decide
  have h_check : check_prime_period_cond 541 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 541 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 541 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 541 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 541 n hp h_flt (exp_seq_eq (541-1) n) H_val

lemma not_dvd_547 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 547 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (547 : ℕ).Prime := by decide
  have h_flt : (2^(547-1)) % 547 = 1 := by decide
  have h_per : exp_seq (547-1) 6 = exp_seq (547-1) 0 := by decide
  have h_check : check_prime_period_cond 547 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 547 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 547 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 547 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 547 n hp h_flt (exp_seq_eq (547-1) n) H_val

lemma not_dvd_557 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 557 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (557 : ℕ).Prime := by decide
  have h_flt : (2^(557-1)) % 557 = 1 := by decide
  have h_per : exp_seq (557-1) 69 = exp_seq (557-1) 0 := by decide
  have h_check : check_prime_period_cond 557 69 (fun _ => false) = true := by decide
  have H_val : val_mod_p 557 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 557 69 (fun _ => false) h_check (n % 69) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 557 69 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 557 n hp h_flt (exp_seq_eq (557-1) n) H_val

lemma not_dvd_563 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 563 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (563 : ℕ).Prime := by decide
  have h_flt : (2^(563-1)) % 563 = 1 := by decide
  have h_per : exp_seq (563-1) 35 = exp_seq (563-1) 0 := by decide
  have h_check : check_prime_period_cond 563 35 (fun _ => false) = true := by decide
  have H_val : val_mod_p 563 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 563 35 (fun _ => false) h_check (n % 35) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 563 35 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 563 n hp h_flt (exp_seq_eq (563-1) n) H_val

lemma not_dvd_569 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 569 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (569 : ℕ).Prime := by decide
  have h_flt : (2^(569-1)) % 569 = 1 := by decide
  have h_per : exp_seq (569-1) 35 = exp_seq (569-1) 0 := by decide
  have h_check : check_prime_period_cond 569 35 (fun _ => false) = true := by decide
  have H_val : val_mod_p 569 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 569 35 (fun _ => false) h_check (n % 35) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 569 35 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 569 n hp h_flt (exp_seq_eq (569-1) n) H_val

lemma not_dvd_571 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 571 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (571 : ℕ).Prime := by decide
  have h_flt : (2^(571-1)) % 571 = 1 := by decide
  have h_per : exp_seq (571-1) 18 = exp_seq (571-1) 0 := by decide
  have h_check : check_prime_period_cond 571 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 571 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 571 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 571 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 571 n hp h_flt (exp_seq_eq (571-1) n) H_val

lemma not_dvd_577 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 577 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (577 : ℕ).Prime := by decide
  have h_flt : (2^(577-1)) % 577 = 1 := by decide
  have h_per : exp_seq (577-1) 3 = exp_seq (577-1) 0 := by decide
  have h_check : check_prime_period_cond 577 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 577 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 577 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 577 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 577 n hp h_flt (exp_seq_eq (577-1) n) H_val

lemma not_dvd_587 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 587 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (587 : ℕ).Prime := by decide
  have h_flt : (2^(587-1)) % 587 = 1 := by decide
  have h_per : exp_seq (587-1) 146 = exp_seq (587-1) 0 := by decide
  have h_check : check_prime_period_cond 587 146 (fun _ => false) = true := by decide
  have H_val : val_mod_p 587 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 587 146 (fun _ => false) h_check (n % 146) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 587 146 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 587 n hp h_flt (exp_seq_eq (587-1) n) H_val

lemma not_dvd_593 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 593 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (593 : ℕ).Prime := by decide
  have h_flt : (2^(593-1)) % 593 = 1 := by decide
  have h_per : exp_seq (593-1) 18 = exp_seq (593-1) 0 := by decide
  have h_check : check_prime_period_cond 593 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 593 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 593 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 593 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 593 n hp h_flt (exp_seq_eq (593-1) n) H_val

lemma not_dvd_599 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 599 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (599 : ℕ).Prime := by decide
  have h_flt : (2^(599-1)) % 599 = 1 := by decide
  have h_per : exp_seq (599-1) 66 = exp_seq (599-1) 0 := by decide
  have h_check : check_prime_period_cond 599 66 (fun _ => false) = true := by decide
  have H_val : val_mod_p 599 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 599 66 (fun _ => false) h_check (n % 66) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 599 66 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 599 n hp h_flt (exp_seq_eq (599-1) n) H_val

lemma not_dvd_601 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 601 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (601 : ℕ).Prime := by decide
  have h_flt : (2^(601-1)) % 601 = 1 := by decide
  have h_per : exp_seq (601-1) 10 = exp_seq (601-1) 0 := by decide
  have h_check : check_prime_period_cond 601 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 601 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 601 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 601 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 601 n hp h_flt (exp_seq_eq (601-1) n) H_val

lemma not_dvd_607 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 607 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (607 : ℕ).Prime := by decide
  have h_flt : (2^(607-1)) % 607 = 1 := by decide
  have h_per : exp_seq (607-1) 50 = exp_seq (607-1) 0 := by decide
  have h_check : check_prime_period_cond 607 50 (fun _ => false) = true := by decide
  have H_val : val_mod_p 607 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 607 50 (fun _ => false) h_check (n % 50) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 607 50 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 607 n hp h_flt (exp_seq_eq (607-1) n) H_val

lemma not_dvd_613 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 613 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (613 : ℕ).Prime := by decide
  have h_flt : (2^(613-1)) % 613 = 1 := by decide
  have h_per : exp_seq (613-1) 12 = exp_seq (613-1) 0 := by decide
  have h_check : check_prime_period_cond 613 12 (fun _ => false) = true := by decide
  have H_val : val_mod_p 613 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 613 12 (fun _ => false) h_check (n % 12) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 613 12 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 613 n hp h_flt (exp_seq_eq (613-1) n) H_val

lemma not_dvd_617 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 617 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (617 : ℕ).Prime := by decide
  have h_flt : (2^(617-1)) % 617 = 1 := by decide
  have h_per : exp_seq (617-1) 15 = exp_seq (617-1) 0 := by decide
  have h_check : check_prime_period_cond 617 15 (fun _ => false) = true := by decide
  have H_val : val_mod_p 617 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 617 15 (fun _ => false) h_check (n % 15) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 617 15 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 617 n hp h_flt (exp_seq_eq (617-1) n) H_val

lemma not_dvd_619 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 619 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (619 : ℕ).Prime := by decide
  have h_flt : (2^(619-1)) % 619 = 1 := by decide
  have h_per : exp_seq (619-1) 51 = exp_seq (619-1) 0 := by decide
  have h_check : check_prime_period_cond 619 51 (fun _ => false) = true := by decide
  have H_val : val_mod_p 619 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 619 51 (fun _ => false) h_check (n % 51) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 619 51 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 619 n hp h_flt (exp_seq_eq (619-1) n) H_val

lemma not_dvd_631 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 631 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (631 : ℕ).Prime := by decide
  have h_flt : (2^(631-1)) % 631 = 1 := by decide
  have h_per : exp_seq (631-1) 6 = exp_seq (631-1) 0 := by decide
  have h_check : check_prime_period_cond 631 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 631 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 631 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 631 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 631 n hp h_flt (exp_seq_eq (631-1) n) H_val

lemma not_dvd_641 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 641 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (641 : ℕ).Prime := by decide
  have h_flt : (2^(641-1)) % 641 = 1 := by decide
  have h_per : exp_seq (641-1) 2 = exp_seq (641-1) 0 := by decide
  have h_check : check_prime_period_cond 641 2 (fun _ => false) = true := by decide
  have H_val : val_mod_p 641 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 641 2 (fun _ => false) h_check (n % 2) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 641 2 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 641 n hp h_flt (exp_seq_eq (641-1) n) H_val

lemma not_dvd_643 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 643 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (643 : ℕ).Prime := by decide
  have h_flt : (2^(643-1)) % 643 = 1 := by decide
  have h_per : exp_seq (643-1) 53 = exp_seq (643-1) 0 := by decide
  have h_check : check_prime_period_cond 643 53 (fun _ => false) = true := by decide
  have H_val : val_mod_p 643 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 643 53 (fun _ => false) h_check (n % 53) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 643 53 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 643 n hp h_flt (exp_seq_eq (643-1) n) H_val

lemma not_dvd_647 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 647 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (647 : ℕ).Prime := by decide
  have h_flt : (2^(647-1)) % 647 = 1 := by decide
  have h_per : exp_seq (647-1) 36 = exp_seq (647-1) 0 := by decide
  have h_check : check_prime_period_cond 647 36 (fun _ => false) = true := by decide
  have H_val : val_mod_p 647 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 647 36 (fun _ => false) h_check (n % 36) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 647 36 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 647 n hp h_flt (exp_seq_eq (647-1) n) H_val

lemma not_dvd_653 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 653 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (653 : ℕ).Prime := by decide
  have h_flt : (2^(653-1)) % 653 = 1 := by decide
  have h_per : exp_seq (653-1) 81 = exp_seq (653-1) 0 := by decide
  have h_check : check_prime_period_cond 653 81 (fun _ => false) = true := by decide
  have H_val : val_mod_p 653 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 653 81 (fun _ => false) h_check (n % 81) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 653 81 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 653 n hp h_flt (exp_seq_eq (653-1) n) H_val

lemma not_dvd_659 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 659 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (659 : ℕ).Prime := by decide
  have h_flt : (2^(659-1)) % 659 = 1 := by decide
  have h_per : exp_seq (659-1) 69 = exp_seq (659-1) 0 := by decide
  have h_check : check_prime_period_cond 659 69 (fun _ => false) = true := by decide
  have H_val : val_mod_p 659 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 659 69 (fun _ => false) h_check (n % 69) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 659 69 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 659 n hp h_flt (exp_seq_eq (659-1) n) H_val

lemma not_dvd_661 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 661 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (661 : ℕ).Prime := by decide
  have h_flt : (2^(661-1)) % 661 = 1 := by decide
  have h_per : exp_seq (661-1) 10 = exp_seq (661-1) 0 := by decide
  have h_check : check_prime_period_cond 661 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 661 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 661 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 661 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 661 n hp h_flt (exp_seq_eq (661-1) n) H_val

lemma not_dvd_673 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 673 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (673 : ℕ).Prime := by decide
  have h_flt : (2^(673-1)) % 673 = 1 := by decide
  have h_per : exp_seq (673-1) 3 = exp_seq (673-1) 0 := by decide
  have h_check : check_prime_period_cond 673 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 673 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 673 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 673 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 673 n hp h_flt (exp_seq_eq (673-1) n) H_val

lemma not_dvd_677 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 677 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (677 : ℕ).Prime := by decide
  have h_flt : (2^(677-1)) % 677 = 1 := by decide
  have h_per : exp_seq (677-1) 78 = exp_seq (677-1) 0 := by decide
  have h_check : check_prime_period_cond 677 78 (fun _ => false) = true := by decide
  have H_val : val_mod_p 677 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 677 78 (fun _ => false) h_check (n % 78) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 677 78 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 677 n hp h_flt (exp_seq_eq (677-1) n) H_val

lemma not_dvd_683 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 683 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (683 : ℕ).Prime := by decide
  have h_flt : (2^(683-1)) % 683 = 1 := by decide
  have h_per : exp_seq (683-1) 5 = exp_seq (683-1) 0 := by decide
  have h_check : check_prime_period_cond 683 5 (fun _ => false) = true := by decide
  have H_val : val_mod_p 683 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 683 5 (fun _ => false) h_check (n % 5) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 683 5 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 683 n hp h_flt (exp_seq_eq (683-1) n) H_val

lemma not_dvd_691 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 691 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (691 : ℕ).Prime := by decide
  have h_flt : (2^(691-1)) % 691 = 1 := by decide
  have h_per : exp_seq (691-1) 22 = exp_seq (691-1) 0 := by decide
  have h_check : check_prime_period_cond 691 22 (fun _ => false) = true := by decide
  have H_val : val_mod_p 691 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 691 22 (fun _ => false) h_check (n % 22) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 691 22 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 691 n hp h_flt (exp_seq_eq (691-1) n) H_val

lemma not_dvd_701 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 701 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (701 : ℕ).Prime := by decide
  have h_flt : (2^(701-1)) % 701 = 1 := by decide
  have h_per : exp_seq (701-1) 30 = exp_seq (701-1) 0 := by decide
  have h_check : check_prime_period_cond 701 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 701 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 701 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 701 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 701 n hp h_flt (exp_seq_eq (701-1) n) H_val

lemma not_dvd_709 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 709 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (709 : ℕ).Prime := by decide
  have h_flt : (2^(709-1)) % 709 = 1 := by decide
  have h_per : exp_seq (709-1) 1 = exp_seq (709-1) 0 := by decide
  have h_check : check_prime_period_cond 709 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 709 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 709 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 709 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 709 n hp h_flt (exp_seq_eq (709-1) n) H_val

lemma not_dvd_719 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 719 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (719 : ℕ).Prime := by decide
  have h_flt : (2^(719-1)) % 719 = 1 := by decide
  have h_per : exp_seq (719-1) 179 = exp_seq (719-1) 0 := by decide
  have h_check : check_prime_period_cond 719 179 (fun _ => false) = true := by decide
  have H_val : val_mod_p 719 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 719 179 (fun _ => false) h_check (n % 179) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 719 179 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 719 n hp h_flt (exp_seq_eq (719-1) n) H_val

lemma not_dvd_727 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 727 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (727 : ℕ).Prime := by decide
  have h_flt : (2^(727-1)) % 727 = 1 := by decide
  have h_per : exp_seq (727-1) 55 = exp_seq (727-1) 0 := by decide
  have h_check : check_prime_period_cond 727 55 (fun _ => false) = true := by decide
  have H_val : val_mod_p 727 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 727 55 (fun _ => false) h_check (n % 55) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 727 55 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 727 n hp h_flt (exp_seq_eq (727-1) n) H_val

lemma not_dvd_733 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 733 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (733 : ℕ).Prime := by decide
  have h_flt : (2^(733-1)) % 733 = 1 := by decide
  have h_per : exp_seq (733-1) 30 = exp_seq (733-1) 0 := by decide
  have h_check : check_prime_period_cond 733 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 733 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 733 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 733 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 733 n hp h_flt (exp_seq_eq (733-1) n) H_val

lemma not_dvd_739 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 739 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (739 : ℕ).Prime := by decide
  have h_flt : (2^(739-1)) % 739 = 1 := by decide
  have h_per : exp_seq (739-1) 30 = exp_seq (739-1) 0 := by decide
  have h_check : check_prime_period_cond 739 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 739 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 739 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 739 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 739 n hp h_flt (exp_seq_eq (739-1) n) H_val

lemma not_dvd_743 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 743 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (743 : ℕ).Prime := by decide
  have h_flt : (2^(743-1)) % 743 = 1 := by decide
  have h_per : exp_seq (743-1) 78 = exp_seq (743-1) 0 := by decide
  have h_check : check_prime_period_cond 743 78 (fun _ => false) = true := by decide
  have H_val : val_mod_p 743 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 743 78 (fun _ => false) h_check (n % 78) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 743 78 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 743 n hp h_flt (exp_seq_eq (743-1) n) H_val

lemma not_dvd_751 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 751 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (751 : ℕ).Prime := by decide
  have h_flt : (2^(751-1)) % 751 = 1 := by decide
  have h_per : exp_seq (751-1) 50 = exp_seq (751-1) 0 := by decide
  have h_check : check_prime_period_cond 751 50 (fun _ => false) = true := by decide
  have H_val : val_mod_p 751 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 751 50 (fun _ => false) h_check (n % 50) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 751 50 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 751 n hp h_flt (exp_seq_eq (751-1) n) H_val

lemma not_dvd_757 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 757 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (757 : ℕ).Prime := by decide
  have h_flt : (2^(757-1)) % 757 = 1 := by decide
  have h_per : exp_seq (757-1) 9 = exp_seq (757-1) 0 := by decide
  have h_check : check_prime_period_cond 757 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 757 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 757 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 757 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 757 n hp h_flt (exp_seq_eq (757-1) n) H_val

lemma not_dvd_761 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 761 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (761 : ℕ).Prime := by decide
  have h_flt : (2^(761-1)) % 761 = 1 := by decide
  have h_per : exp_seq (761-1) 18 = exp_seq (761-1) 0 := by decide
  have h_check : check_prime_period_cond 761 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 761 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 761 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 761 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 761 n hp h_flt (exp_seq_eq (761-1) n) H_val

lemma not_dvd_769 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 769 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (769 : ℕ).Prime := by decide
  have h_flt : (2^(769-1)) % 769 = 1 := by decide
  have h_per : exp_seq (769-1) 1 = exp_seq (769-1) 0 := by decide
  have h_check : check_prime_period_cond 769 1 (fun _ => false) = true := by decide
  have H_val : val_mod_p 769 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 769 1 (fun _ => false) h_check (n % 1) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 769 1 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 769 n hp h_flt (exp_seq_eq (769-1) n) H_val

lemma not_dvd_773 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 773 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (773 : ℕ).Prime := by decide
  have h_flt : (2^(773-1)) % 773 = 1 := by decide
  have h_per : exp_seq (773-1) 48 = exp_seq (773-1) 0 := by decide
  have h_check : check_prime_period_cond 773 48 (fun _ => false) = true := by decide
  have H_val : val_mod_p 773 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 773 48 (fun _ => false) h_check (n % 48) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 773 48 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 773 n hp h_flt (exp_seq_eq (773-1) n) H_val

lemma not_dvd_787 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 787 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (787 : ℕ).Prime := by decide
  have h_flt : (2^(787-1)) % 787 = 1 := by decide
  have h_per : exp_seq (787-1) 65 = exp_seq (787-1) 0 := by decide
  have h_check : check_prime_period_cond 787 65 (fun _ => false) = true := by decide
  have H_val : val_mod_p 787 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 787 65 (fun _ => false) h_check (n % 65) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 787 65 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 787 n hp h_flt (exp_seq_eq (787-1) n) H_val

lemma not_dvd_797 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 797 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (797 : ℕ).Prime := by decide
  have h_flt : (2^(797-1)) % 797 = 1 := by decide
  have h_per : exp_seq (797-1) 99 = exp_seq (797-1) 0 := by decide
  have h_check : check_prime_period_cond 797 99 (fun _ => false) = true := by decide
  have H_val : val_mod_p 797 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 797 99 (fun _ => false) h_check (n % 99) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 797 99 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 797 n hp h_flt (exp_seq_eq (797-1) n) H_val

lemma not_dvd_809 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 809 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (809 : ℕ).Prime := by decide
  have h_flt : (2^(809-1)) % 809 = 1 := by decide
  have h_per : exp_seq (809-1) 50 = exp_seq (809-1) 0 := by decide
  have h_check : check_prime_period_cond 809 50 (fun _ => false) = true := by decide
  have H_val : val_mod_p 809 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 809 50 (fun _ => false) h_check (n % 50) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 809 50 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 809 n hp h_flt (exp_seq_eq (809-1) n) H_val

lemma not_dvd_811 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 811 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (811 : ℕ).Prime := by decide
  have h_flt : (2^(811-1)) % 811 = 1 := by decide
  have h_per : exp_seq (811-1) 54 = exp_seq (811-1) 0 := by decide
  have h_check : check_prime_period_cond 811 54 (fun _ => false) = true := by decide
  have H_val : val_mod_p 811 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 811 54 (fun _ => false) h_check (n % 54) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 811 54 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 811 n hp h_flt (exp_seq_eq (811-1) n) H_val

lemma not_dvd_821 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 821 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (821 : ℕ).Prime := by decide
  have h_flt : (2^(821-1)) % 821 = 1 := by decide
  have h_per : exp_seq (821-1) 10 = exp_seq (821-1) 0 := by decide
  have h_check : check_prime_period_cond 821 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 821 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 821 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 821 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 821 n hp h_flt (exp_seq_eq (821-1) n) H_val

lemma not_dvd_823 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 823 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (823 : ℕ).Prime := by decide
  have h_flt : (2^(823-1)) % 823 = 1 := by decide
  have h_per : exp_seq (823-1) 34 = exp_seq (823-1) 0 := by decide
  have h_check : check_prime_period_cond 823 34 (fun _ => false) = true := by decide
  have H_val : val_mod_p 823 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 823 34 (fun _ => false) h_check (n % 34) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 823 34 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 823 n hp h_flt (exp_seq_eq (823-1) n) H_val

lemma not_dvd_827 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 827 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (827 : ℕ).Prime := by decide
  have h_flt : (2^(827-1)) % 827 = 1 := by decide
  have h_per : exp_seq (827-1) 3 = exp_seq (827-1) 0 := by decide
  have h_check : check_prime_period_cond 827 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 827 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 827 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 827 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 827 n hp h_flt (exp_seq_eq (827-1) n) H_val

lemma not_dvd_829 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 829 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (829 : ℕ).Prime := by decide
  have h_flt : (2^(829-1)) % 829 = 1 := by decide
  have h_per : exp_seq (829-1) 33 = exp_seq (829-1) 0 := by decide
  have h_check : check_prime_period_cond 829 33 (fun _ => false) = true := by decide
  have H_val : val_mod_p 829 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 829 33 (fun _ => false) h_check (n % 33) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 829 33 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 829 n hp h_flt (exp_seq_eq (829-1) n) H_val

lemma not_dvd_839 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 839 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (839 : ℕ).Prime := by decide
  have h_flt : (2^(839-1)) % 839 = 1 := by decide
  have h_per : exp_seq (839-1) 209 = exp_seq (839-1) 0 := by decide
  have h_check : check_prime_period_cond 839 209 (fun _ => false) = true := by decide
  have H_val : val_mod_p 839 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 839 209 (fun _ => false) h_check (n % 209) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 839 209 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 839 n hp h_flt (exp_seq_eq (839-1) n) H_val

lemma not_dvd_853 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 853 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (853 : ℕ).Prime := by decide
  have h_flt : (2^(853-1)) % 853 = 1 := by decide
  have h_per : exp_seq (853-1) 35 = exp_seq (853-1) 0 := by decide
  have h_check : check_prime_period_cond 853 35 (fun _ => false) = true := by decide
  have H_val : val_mod_p 853 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 853 35 (fun _ => false) h_check (n % 35) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 853 35 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 853 n hp h_flt (exp_seq_eq (853-1) n) H_val

lemma not_dvd_857 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 857 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (857 : ℕ).Prime := by decide
  have h_flt : (2^(857-1)) % 857 = 1 := by decide
  have h_per : exp_seq (857-1) 53 = exp_seq (857-1) 0 := by decide
  have h_check : check_prime_period_cond 857 53 (fun _ => false) = true := by decide
  have H_val : val_mod_p 857 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 857 53 (fun _ => false) h_check (n % 53) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 857 53 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 857 n hp h_flt (exp_seq_eq (857-1) n) H_val

lemma not_dvd_859 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 859 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (859 : ℕ).Prime := by decide
  have h_flt : (2^(859-1)) % 859 = 1 := by decide
  have h_per : exp_seq (859-1) 30 = exp_seq (859-1) 0 := by decide
  have h_check : check_prime_period_cond 859 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 859 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 859 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 859 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 859 n hp h_flt (exp_seq_eq (859-1) n) H_val

lemma not_dvd_863 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 863 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (863 : ℕ).Prime := by decide
  have h_flt : (2^(863-1)) % 863 = 1 := by decide
  have h_per : exp_seq (863-1) 43 = exp_seq (863-1) 0 := by decide
  have h_check : check_prime_period_cond 863 43 (fun _ => false) = true := by decide
  have H_val : val_mod_p 863 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 863 43 (fun _ => false) h_check (n % 43) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 863 43 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 863 n hp h_flt (exp_seq_eq (863-1) n) H_val

lemma not_dvd_877 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 877 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (877 : ℕ).Prime := by decide
  have h_flt : (2^(877-1)) % 877 = 1 := by decide
  have h_per : exp_seq (877-1) 9 = exp_seq (877-1) 0 := by decide
  have h_check : check_prime_period_cond 877 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 877 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 877 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 877 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 877 n hp h_flt (exp_seq_eq (877-1) n) H_val

lemma not_dvd_881 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 881 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (881 : ℕ).Prime := by decide
  have h_flt : (2^(881-1)) % 881 = 1 := by decide
  have h_per : exp_seq (881-1) 10 = exp_seq (881-1) 0 := by decide
  have h_check : check_prime_period_cond 881 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 881 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 881 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 881 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 881 n hp h_flt (exp_seq_eq (881-1) n) H_val

lemma not_dvd_883 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 883 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (883 : ℕ).Prime := by decide
  have h_flt : (2^(883-1)) % 883 = 1 := by decide
  have h_per : exp_seq (883-1) 21 = exp_seq (883-1) 0 := by decide
  have h_check : check_prime_period_cond 883 21 (fun _ => false) = true := by decide
  have H_val : val_mod_p 883 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 883 21 (fun _ => false) h_check (n % 21) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 883 21 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 883 n hp h_flt (exp_seq_eq (883-1) n) H_val

lemma not_dvd_887 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 887 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (887 : ℕ).Prime := by decide
  have h_flt : (2^(887-1)) % 887 = 1 := by decide
  have h_per : exp_seq (887-1) 221 = exp_seq (887-1) 0 := by decide
  have h_check : check_prime_period_cond 887 221 (fun _ => false) = true := by decide
  have H_val : val_mod_p 887 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 887 221 (fun _ => false) h_check (n % 221) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 887 221 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 887 n hp h_flt (exp_seq_eq (887-1) n) H_val

lemma not_dvd_907 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 907 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (907 : ℕ).Prime := by decide
  have h_flt : (2^(907-1)) % 907 = 1 := by decide
  have h_per : exp_seq (907-1) 15 = exp_seq (907-1) 0 := by decide
  have h_check : check_prime_period_cond 907 15 (fun _ => false) = true := by decide
  have H_val : val_mod_p 907 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 907 15 (fun _ => false) h_check (n % 15) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 907 15 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 907 n hp h_flt (exp_seq_eq (907-1) n) H_val

lemma not_dvd_911 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 911 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (911 : ℕ).Prime := by decide
  have h_flt : (2^(911-1)) % 911 = 1 := by decide
  have h_per : exp_seq (911-1) 6 = exp_seq (911-1) 0 := by decide
  have h_check : check_prime_period_cond 911 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 911 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 911 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 911 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 911 n hp h_flt (exp_seq_eq (911-1) n) H_val

lemma not_dvd_919 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 919 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (919 : ℕ).Prime := by decide
  have h_flt : (2^(919-1)) % 919 = 1 := by decide
  have h_per : exp_seq (919-1) 36 = exp_seq (919-1) 0 := by decide
  have h_check : check_prime_period_cond 919 36 (fun _ => false) = true := by decide
  have H_val : val_mod_p 919 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 919 36 (fun _ => false) h_check (n % 36) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 919 36 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 919 n hp h_flt (exp_seq_eq (919-1) n) H_val

lemma not_dvd_929 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 929 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (929 : ℕ).Prime := by decide
  have h_flt : (2^(929-1)) % 929 = 1 := by decide
  have h_per : exp_seq (929-1) 14 = exp_seq (929-1) 0 := by decide
  have h_check : check_prime_period_cond 929 14 (fun _ => false) = true := by decide
  have H_val : val_mod_p 929 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 929 14 (fun _ => false) h_check (n % 14) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 929 14 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 929 n hp h_flt (exp_seq_eq (929-1) n) H_val

lemma not_dvd_937 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 937 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (937 : ℕ).Prime := by decide
  have h_flt : (2^(937-1)) % 937 = 1 := by decide
  have h_per : exp_seq (937-1) 6 = exp_seq (937-1) 0 := by decide
  have h_check : check_prime_period_cond 937 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 937 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 937 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 937 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 937 n hp h_flt (exp_seq_eq (937-1) n) H_val

lemma not_dvd_941 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 941 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (941 : ℕ).Prime := by decide
  have h_flt : (2^(941-1)) % 941 = 1 := by decide
  have h_per : exp_seq (941-1) 46 = exp_seq (941-1) 0 := by decide
  have h_check : check_prime_period_cond 941 46 (fun _ => false) = true := by decide
  have H_val : val_mod_p 941 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 941 46 (fun _ => false) h_check (n % 46) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 941 46 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 941 n hp h_flt (exp_seq_eq (941-1) n) H_val

lemma not_dvd_947 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 947 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (947 : ℕ).Prime := by decide
  have h_flt : (2^(947-1)) % 947 = 1 := by decide
  have h_per : exp_seq (947-1) 35 = exp_seq (947-1) 0 := by decide
  have h_check : check_prime_period_cond 947 35 (fun _ => false) = true := by decide
  have H_val : val_mod_p 947 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 947 35 (fun _ => false) h_check (n % 35) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 947 35 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 947 n hp h_flt (exp_seq_eq (947-1) n) H_val

lemma not_dvd_953 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 953 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (953 : ℕ).Prime := by decide
  have h_flt : (2^(953-1)) % 953 = 1 := by decide
  have h_per : exp_seq (953-1) 12 = exp_seq (953-1) 0 := by decide
  have h_check : check_prime_period_cond 953 12 (fun _ => false) = true := by decide
  have H_val : val_mod_p 953 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 953 12 (fun _ => false) h_check (n % 12) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 953 12 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 953 n hp h_flt (exp_seq_eq (953-1) n) H_val

lemma not_dvd_967 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 967 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (967 : ℕ).Prime := by decide
  have h_flt : (2^(967-1)) % 967 = 1 := by decide
  have h_per : exp_seq (967-1) 33 = exp_seq (967-1) 0 := by decide
  have h_check : check_prime_period_cond 967 33 (fun _ => false) = true := by decide
  have H_val : val_mod_p 967 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 967 33 (fun _ => false) h_check (n % 33) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 967 33 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 967 n hp h_flt (exp_seq_eq (967-1) n) H_val

lemma not_dvd_971 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 971 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (971 : ℕ).Prime := by decide
  have h_flt : (2^(971-1)) % 971 = 1 := by decide
  have h_per : exp_seq (971-1) 24 = exp_seq (971-1) 0 := by decide
  have h_check : check_prime_period_cond 971 24 (fun _ => false) = true := by decide
  have H_val : val_mod_p 971 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 971 24 (fun _ => false) h_check (n % 24) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 971 24 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 971 n hp h_flt (exp_seq_eq (971-1) n) H_val

lemma not_dvd_977 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 977 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (977 : ℕ).Prime := by decide
  have h_flt : (2^(977-1)) % 977 = 1 := by decide
  have h_per : exp_seq (977-1) 30 = exp_seq (977-1) 0 := by decide
  have h_check : check_prime_period_cond 977 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 977 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 977 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 977 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 977 n hp h_flt (exp_seq_eq (977-1) n) H_val

lemma not_dvd_983 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 983 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (983 : ℕ).Prime := by decide
  have h_flt : (2^(983-1)) % 983 = 1 := by decide
  have h_per : exp_seq (983-1) 245 = exp_seq (983-1) 0 := by decide
  have h_check : check_prime_period_cond 983 245 (fun _ => false) = true := by decide
  have H_val : val_mod_p 983 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 983 245 (fun _ => false) h_check (n % 245) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 983 245 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 983 n hp h_flt (exp_seq_eq (983-1) n) H_val

lemma not_dvd_991 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 991 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (991 : ℕ).Prime := by decide
  have h_flt : (2^(991-1)) % 991 = 1 := by decide
  have h_per : exp_seq (991-1) 30 = exp_seq (991-1) 0 := by decide
  have h_check : check_prime_period_cond 991 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 991 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 991 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 991 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 991 n hp h_flt (exp_seq_eq (991-1) n) H_val

lemma not_dvd_997 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 997 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (997 : ℕ).Prime := by decide
  have h_flt : (2^(997-1)) % 997 = 1 := by decide
  have h_per : exp_seq (997-1) 41 = exp_seq (997-1) 0 := by decide
  have h_check : check_prime_period_cond 997 41 (fun _ => false) = true := by decide
  have H_val : val_mod_p 997 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 997 41 (fun _ => false) h_check (n % 41) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 997 41 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 997 n hp h_flt (exp_seq_eq (997-1) n) H_val

lemma not_dvd_1009 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1009 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1009 : ℕ).Prime := by decide
  have h_flt : (2^(1009-1)) % 1009 = 1 := by decide
  have h_per : exp_seq (1009-1) 3 = exp_seq (1009-1) 0 := by decide
  have h_check : check_prime_period_cond 1009 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1009 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1009 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1009 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1009 n hp h_flt (exp_seq_eq (1009-1) n) H_val

lemma not_dvd_1013 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1013 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1013 : ℕ).Prime := by decide
  have h_flt : (2^(1013-1)) % 1013 = 1 := by decide
  have h_per : exp_seq (1013-1) 55 = exp_seq (1013-1) 0 := by decide
  have h_check : check_prime_period_cond 1013 55 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1013 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1013 55 (fun _ => false) h_check (n % 55) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1013 55 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1013 n hp h_flt (exp_seq_eq (1013-1) n) H_val

lemma not_dvd_1019 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1019 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1019 : ℕ).Prime := by decide
  have h_flt : (2^(1019-1)) % 1019 = 1 := by decide
  have h_per : exp_seq (1019-1) 254 = exp_seq (1019-1) 0 := by decide
  have h_check : check_prime_period_cond 1019 254 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1019 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1019 254 (fun _ => false) h_check (n % 254) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1019 254 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1019 n hp h_flt (exp_seq_eq (1019-1) n) H_val

lemma not_dvd_1021 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1021 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1021 : ℕ).Prime := by decide
  have h_flt : (2^(1021-1)) % 1021 = 1 := by decide
  have h_per : exp_seq (1021-1) 4 = exp_seq (1021-1) 0 := by decide
  have h_check : check_prime_period_cond 1021 4 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1021 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1021 4 (fun _ => false) h_check (n % 4) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1021 4 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1021 n hp h_flt (exp_seq_eq (1021-1) n) H_val

lemma not_dvd_1031 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1031 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1031 : ℕ).Prime := by decide
  have h_flt : (2^(1031-1)) % 1031 = 1 := by decide
  have h_per : exp_seq (1031-1) 102 = exp_seq (1031-1) 0 := by decide
  have h_check : check_prime_period_cond 1031 102 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1031 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1031 102 (fun _ => false) h_check (n % 102) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1031 102 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1031 n hp h_flt (exp_seq_eq (1031-1) n) H_val

lemma not_dvd_1033 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1033 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1033 : ℕ).Prime := by decide
  have h_flt : (2^(1033-1)) % 1033 = 1 := by decide
  have h_per : exp_seq (1033-1) 7 = exp_seq (1033-1) 0 := by decide
  have h_check : check_prime_period_cond 1033 7 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1033 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1033 7 (fun _ => false) h_check (n % 7) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1033 7 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1033 n hp h_flt (exp_seq_eq (1033-1) n) H_val

lemma not_dvd_1039 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1039 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1039 : ℕ).Prime := by decide
  have h_flt : (2^(1039-1)) % 1039 = 1 := by decide
  have h_per : exp_seq (1039-1) 86 = exp_seq (1039-1) 0 := by decide
  have h_check : check_prime_period_cond 1039 86 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1039 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1039 86 (fun _ => false) h_check (n % 86) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1039 86 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1039 n hp h_flt (exp_seq_eq (1039-1) n) H_val

lemma not_dvd_1049 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1049 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1049 : ℕ).Prime := by decide
  have h_flt : (2^(1049-1)) % 1049 = 1 := by decide
  have h_per : exp_seq (1049-1) 65 = exp_seq (1049-1) 0 := by decide
  have h_check : check_prime_period_cond 1049 65 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1049 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1049 65 (fun _ => false) h_check (n % 65) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1049 65 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1049 n hp h_flt (exp_seq_eq (1049-1) n) H_val

lemma not_dvd_1051 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1051 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1051 : ℕ).Prime := by decide
  have h_flt : (2^(1051-1)) % 1051 = 1 := by decide
  have h_per : exp_seq (1051-1) 30 = exp_seq (1051-1) 0 := by decide
  have h_check : check_prime_period_cond 1051 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1051 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1051 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1051 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1051 n hp h_flt (exp_seq_eq (1051-1) n) H_val

lemma not_dvd_1061 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1061 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1061 : ℕ).Prime := by decide
  have h_flt : (2^(1061-1)) % 1061 = 1 := by decide
  have h_per : exp_seq (1061-1) 26 = exp_seq (1061-1) 0 := by decide
  have h_check : check_prime_period_cond 1061 26 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1061 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1061 26 (fun _ => false) h_check (n % 26) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1061 26 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1061 n hp h_flt (exp_seq_eq (1061-1) n) H_val

lemma not_dvd_1063 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1063 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1063 : ℕ).Prime := by decide
  have h_flt : (2^(1063-1)) % 1063 = 1 := by decide
  have h_per : exp_seq (1063-1) 3 = exp_seq (1063-1) 0 := by decide
  have h_check : check_prime_period_cond 1063 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1063 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1063 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1063 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1063 n hp h_flt (exp_seq_eq (1063-1) n) H_val

lemma not_dvd_1069 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1069 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1069 : ℕ).Prime := by decide
  have h_flt : (2^(1069-1)) % 1069 = 1 := by decide
  have h_per : exp_seq (1069-1) 11 = exp_seq (1069-1) 0 := by decide
  have h_check : check_prime_period_cond 1069 11 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1069 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1069 11 (fun _ => false) h_check (n % 11) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1069 11 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1069 n hp h_flt (exp_seq_eq (1069-1) n) H_val

lemma not_dvd_1087 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1087 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1087 : ℕ).Prime := by decide
  have h_flt : (2^(1087-1)) % 1087 = 1 := by decide
  have h_per : exp_seq (1087-1) 90 = exp_seq (1087-1) 0 := by decide
  have h_check : check_prime_period_cond 1087 90 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1087 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1087 90 (fun _ => false) h_check (n % 90) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1087 90 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1087 n hp h_flt (exp_seq_eq (1087-1) n) H_val

lemma not_dvd_1091 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1091 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1091 : ℕ).Prime := by decide
  have h_flt : (2^(1091-1)) % 1091 = 1 := by decide
  have h_per : exp_seq (1091-1) 18 = exp_seq (1091-1) 0 := by decide
  have h_check : check_prime_period_cond 1091 18 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1091 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1091 18 (fun _ => false) h_check (n % 18) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1091 18 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1091 n hp h_flt (exp_seq_eq (1091-1) n) H_val

lemma not_dvd_1093 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1093 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1093 : ℕ).Prime := by decide
  have h_flt : (2^(1093-1)) % 1093 = 1 := by decide
  have h_per : exp_seq (1093-1) 6 = exp_seq (1093-1) 0 := by decide
  have h_check : check_prime_period_cond 1093 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1093 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1093 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1093 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1093 n hp h_flt (exp_seq_eq (1093-1) n) H_val

lemma not_dvd_1097 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1097 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1097 : ℕ).Prime := by decide
  have h_flt : (2^(1097-1)) % 1097 = 1 := by decide
  have h_per : exp_seq (1097-1) 34 = exp_seq (1097-1) 0 := by decide
  have h_check : check_prime_period_cond 1097 34 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1097 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1097 34 (fun _ => false) h_check (n % 34) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1097 34 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1097 n hp h_flt (exp_seq_eq (1097-1) n) H_val

lemma not_dvd_1103 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1103 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1103 : ℕ).Prime := by decide
  have h_flt : (2^(1103-1)) % 1103 = 1 := by decide
  have h_per : exp_seq (1103-1) 126 = exp_seq (1103-1) 0 := by decide
  have h_check : check_prime_period_cond 1103 126 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1103 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1103 126 (fun _ => false) h_check (n % 126) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1103 126 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1103 n hp h_flt (exp_seq_eq (1103-1) n) H_val

lemma not_dvd_1109 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1109 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1109 : ℕ).Prime := by decide
  have h_flt : (2^(1109-1)) % 1109 = 1 := by decide
  have h_per : exp_seq (1109-1) 46 = exp_seq (1109-1) 0 := by decide
  have h_check : check_prime_period_cond 1109 46 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1109 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1109 46 (fun _ => false) h_check (n % 46) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1109 46 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1109 n hp h_flt (exp_seq_eq (1109-1) n) H_val

lemma not_dvd_1117 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1117 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1117 : ℕ).Prime := by decide
  have h_flt : (2^(1117-1)) % 1117 = 1 := by decide
  have h_per : exp_seq (1117-1) 15 = exp_seq (1117-1) 0 := by decide
  have h_check : check_prime_period_cond 1117 15 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1117 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1117 15 (fun _ => false) h_check (n % 15) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1117 15 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1117 n hp h_flt (exp_seq_eq (1117-1) n) H_val

lemma not_dvd_1123 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1123 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1123 : ℕ).Prime := by decide
  have h_flt : (2^(1123-1)) % 1123 = 1 := by decide
  have h_per : exp_seq (1123-1) 20 = exp_seq (1123-1) 0 := by decide
  have h_check : check_prime_period_cond 1123 20 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1123 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1123 20 (fun _ => false) h_check (n % 20) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1123 20 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1123 n hp h_flt (exp_seq_eq (1123-1) n) H_val

lemma not_dvd_1129 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1129 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1129 : ℕ).Prime := by decide
  have h_flt : (2^(1129-1)) % 1129 = 1 := by decide
  have h_per : exp_seq (1129-1) 23 = exp_seq (1129-1) 0 := by decide
  have h_check : check_prime_period_cond 1129 23 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1129 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1129 23 (fun _ => false) h_check (n % 23) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1129 23 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1129 n hp h_flt (exp_seq_eq (1129-1) n) H_val

lemma not_dvd_1151 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1151 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1151 : ℕ).Prime := by decide
  have h_flt : (2^(1151-1)) % 1151 = 1 := by decide
  have h_per : exp_seq (1151-1) 110 = exp_seq (1151-1) 0 := by decide
  have h_check : check_prime_period_cond 1151 110 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1151 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1151 110 (fun _ => false) h_check (n % 110) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1151 110 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1151 n hp h_flt (exp_seq_eq (1151-1) n) H_val

lemma not_dvd_1153 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1153 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1153 : ℕ).Prime := by decide
  have h_flt : (2^(1153-1)) % 1153 = 1 := by decide
  have h_per : exp_seq (1153-1) 3 = exp_seq (1153-1) 0 := by decide
  have h_check : check_prime_period_cond 1153 3 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1153 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1153 3 (fun _ => false) h_check (n % 3) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1153 3 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1153 n hp h_flt (exp_seq_eq (1153-1) n) H_val

lemma not_dvd_1163 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1163 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1163 : ℕ).Prime := by decide
  have h_flt : (2^(1163-1)) % 1163 = 1 := by decide
  have h_per : exp_seq (1163-1) 123 = exp_seq (1163-1) 0 := by decide
  have h_check : check_prime_period_cond 1163 123 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1163 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1163 123 (fun _ => false) h_check (n % 123) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1163 123 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1163 n hp h_flt (exp_seq_eq (1163-1) n) H_val

lemma not_dvd_1171 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1171 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1171 : ℕ).Prime := by decide
  have h_flt : (2^(1171-1)) % 1171 = 1 := by decide
  have h_per : exp_seq (1171-1) 6 = exp_seq (1171-1) 0 := by decide
  have h_check : check_prime_period_cond 1171 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1171 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1171 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1171 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1171 n hp h_flt (exp_seq_eq (1171-1) n) H_val

lemma not_dvd_1181 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1181 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1181 : ℕ).Prime := by decide
  have h_flt : (2^(1181-1)) % 1181 = 1 := by decide
  have h_per : exp_seq (1181-1) 2 = exp_seq (1181-1) 0 := by decide
  have h_check : check_prime_period_cond 1181 2 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1181 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1181 2 (fun _ => false) h_check (n % 2) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1181 2 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1181 n hp h_flt (exp_seq_eq (1181-1) n) H_val

lemma not_dvd_1187 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1187 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1187 : ℕ).Prime := by decide
  have h_flt : (2^(1187-1)) % 1187 = 1 := by decide
  have h_per : exp_seq (1187-1) 74 = exp_seq (1187-1) 0 := by decide
  have h_check : check_prime_period_cond 1187 74 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1187 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1187 74 (fun _ => false) h_check (n % 74) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1187 74 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1187 n hp h_flt (exp_seq_eq (1187-1) n) H_val

lemma not_dvd_1193 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1193 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1193 : ℕ).Prime := by decide
  have h_flt : (2^(1193-1)) % 1193 = 1 := by decide
  have h_per : exp_seq (1193-1) 74 = exp_seq (1193-1) 0 := by decide
  have h_check : check_prime_period_cond 1193 74 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1193 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1193 74 (fun _ => false) h_check (n % 74) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1193 74 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1193 n hp h_flt (exp_seq_eq (1193-1) n) H_val

lemma not_dvd_1201 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1201 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1201 : ℕ).Prime := by decide
  have h_flt : (2^(1201-1)) % 1201 = 1 := by decide
  have h_per : exp_seq (1201-1) 10 = exp_seq (1201-1) 0 := by decide
  have h_check : check_prime_period_cond 1201 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1201 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1201 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1201 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1201 n hp h_flt (exp_seq_eq (1201-1) n) H_val

lemma not_dvd_1213 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1213 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1213 : ℕ).Prime := by decide
  have h_flt : (2^(1213-1)) % 1213 = 1 := by decide
  have h_per : exp_seq (1213-1) 50 = exp_seq (1213-1) 0 := by decide
  have h_check : check_prime_period_cond 1213 50 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1213 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1213 50 (fun _ => false) h_check (n % 50) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1213 50 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1213 n hp h_flt (exp_seq_eq (1213-1) n) H_val

lemma not_dvd_1217 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1217 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1217 : ℕ).Prime := by decide
  have h_flt : (2^(1217-1)) % 1217 = 1 := by decide
  have h_per : exp_seq (1217-1) 9 = exp_seq (1217-1) 0 := by decide
  have h_check : check_prime_period_cond 1217 9 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1217 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1217 9 (fun _ => false) h_check (n % 9) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1217 9 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1217 n hp h_flt (exp_seq_eq (1217-1) n) H_val

lemma not_dvd_1223 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1223 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1223 : ℕ).Prime := by decide
  have h_flt : (2^(1223-1)) % 1223 = 1 := by decide
  have h_per : exp_seq (1223-1) 138 = exp_seq (1223-1) 0 := by decide
  have h_check : check_prime_period_cond 1223 138 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1223 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1223 138 (fun _ => false) h_check (n % 138) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1223 138 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1223 n hp h_flt (exp_seq_eq (1223-1) n) H_val

lemma not_dvd_1229 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1229 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1229 : ℕ).Prime := by decide
  have h_flt : (2^(1229-1)) % 1229 = 1 := by decide
  have h_per : exp_seq (1229-1) 51 = exp_seq (1229-1) 0 := by decide
  have h_check : check_prime_period_cond 1229 51 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1229 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1229 51 (fun _ => false) h_check (n % 51) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1229 51 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1229 n hp h_flt (exp_seq_eq (1229-1) n) H_val

lemma not_dvd_1231 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1231 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1231 : ℕ).Prime := by decide
  have h_flt : (2^(1231-1)) % 1231 = 1 := by decide
  have h_per : exp_seq (1231-1) 10 = exp_seq (1231-1) 0 := by decide
  have h_check : check_prime_period_cond 1231 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1231 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1231 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1231 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1231 n hp h_flt (exp_seq_eq (1231-1) n) H_val

lemma not_dvd_1237 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1237 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1237 : ℕ).Prime := by decide
  have h_flt : (2^(1237-1)) % 1237 = 1 := by decide
  have h_per : exp_seq (1237-1) 51 = exp_seq (1237-1) 0 := by decide
  have h_check : check_prime_period_cond 1237 51 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1237 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1237 51 (fun _ => false) h_check (n % 51) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1237 51 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1237 n hp h_flt (exp_seq_eq (1237-1) n) H_val

lemma not_dvd_1249 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1249 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1249 : ℕ).Prime := by decide
  have h_flt : (2^(1249-1)) % 1249 = 1 := by decide
  have h_per : exp_seq (1249-1) 6 = exp_seq (1249-1) 0 := by decide
  have h_check : check_prime_period_cond 1249 6 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1249 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1249 6 (fun _ => false) h_check (n % 6) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1249 6 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1249 n hp h_flt (exp_seq_eq (1249-1) n) H_val

lemma not_dvd_1259 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1259 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1259 : ℕ).Prime := by decide
  have h_flt : (2^(1259-1)) % 1259 = 1 := by decide
  have h_per : exp_seq (1259-1) 36 = exp_seq (1259-1) 0 := by decide
  have h_check : check_prime_period_cond 1259 36 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1259 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1259 36 (fun _ => false) h_check (n % 36) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1259 36 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1259 n hp h_flt (exp_seq_eq (1259-1) n) H_val

lemma not_dvd_1277 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1277 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1277 : ℕ).Prime := by decide
  have h_flt : (2^(1277-1)) % 1277 = 1 := by decide
  have h_per : exp_seq (1277-1) 70 = exp_seq (1277-1) 0 := by decide
  have h_check : check_prime_period_cond 1277 70 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1277 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1277 70 (fun _ => false) h_check (n % 70) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1277 70 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1277 n hp h_flt (exp_seq_eq (1277-1) n) H_val

lemma not_dvd_1279 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1279 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1279 : ℕ).Prime := by decide
  have h_flt : (2^(1279-1)) % 1279 = 1 := by decide
  have h_per : exp_seq (1279-1) 105 = exp_seq (1279-1) 0 := by decide
  have h_check : check_prime_period_cond 1279 105 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1279 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1279 105 (fun _ => false) h_check (n % 105) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1279 105 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1279 n hp h_flt (exp_seq_eq (1279-1) n) H_val

lemma not_dvd_1283 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1283 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1283 : ℕ).Prime := by decide
  have h_flt : (2^(1283-1)) % 1283 = 1 := by decide
  have h_per : exp_seq (1283-1) 32 = exp_seq (1283-1) 0 := by decide
  have h_check : check_prime_period_cond 1283 32 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1283 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1283 32 (fun _ => false) h_check (n % 32) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1283 32 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1283 n hp h_flt (exp_seq_eq (1283-1) n) H_val

lemma not_dvd_1289 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1289 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1289 : ℕ).Prime := by decide
  have h_flt : (2^(1289-1)) % 1289 = 1 := by decide
  have h_per : exp_seq (1289-1) 33 = exp_seq (1289-1) 0 := by decide
  have h_check : check_prime_period_cond 1289 33 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1289 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1289 33 (fun _ => false) h_check (n % 33) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1289 33 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1289 n hp h_flt (exp_seq_eq (1289-1) n) H_val

lemma not_dvd_1291 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1291 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1291 : ℕ).Prime := by decide
  have h_flt : (2^(1291-1)) % 1291 = 1 := by decide
  have h_per : exp_seq (1291-1) 14 = exp_seq (1291-1) 0 := by decide
  have h_check : check_prime_period_cond 1291 14 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1291 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1291 14 (fun _ => false) h_check (n % 14) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1291 14 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1291 n hp h_flt (exp_seq_eq (1291-1) n) H_val

lemma not_dvd_1297 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1297 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1297 : ℕ).Prime := by decide
  have h_flt : (2^(1297-1)) % 1297 = 1 := by decide
  have h_per : exp_seq (1297-1) 27 = exp_seq (1297-1) 0 := by decide
  have h_check : check_prime_period_cond 1297 27 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1297 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1297 27 (fun _ => false) h_check (n % 27) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1297 27 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1297 n hp h_flt (exp_seq_eq (1297-1) n) H_val

lemma not_dvd_1301 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1301 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1301 : ℕ).Prime := by decide
  have h_flt : (2^(1301-1)) % 1301 = 1 := by decide
  have h_per : exp_seq (1301-1) 30 = exp_seq (1301-1) 0 := by decide
  have h_check : check_prime_period_cond 1301 30 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1301 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1301 30 (fun _ => false) h_check (n % 30) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1301 30 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1301 n hp h_flt (exp_seq_eq (1301-1) n) H_val

lemma not_dvd_1303 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1303 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1303 : ℕ).Prime := by decide
  have h_flt : (2^(1303-1)) % 1303 = 1 := by decide
  have h_per : exp_seq (1303-1) 15 = exp_seq (1303-1) 0 := by decide
  have h_check : check_prime_period_cond 1303 15 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1303 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1303 15 (fun _ => false) h_check (n % 15) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1303 15 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1303 n hp h_flt (exp_seq_eq (1303-1) n) H_val

lemma not_dvd_1307 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1307 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1307 : ℕ).Prime := by decide
  have h_flt : (2^(1307-1)) % 1307 = 1 := by decide
  have h_per : exp_seq (1307-1) 326 = exp_seq (1307-1) 0 := by decide
  have h_check : check_prime_period_cond 1307 326 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1307 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1307 326 (fun _ => false) h_check (n % 326) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1307 326 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1307 n hp h_flt (exp_seq_eq (1307-1) n) H_val

lemma not_dvd_1319 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1319 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1319 : ℕ).Prime := by decide
  have h_flt : (2^(1319-1)) % 1319 = 1 := by decide
  have h_per : exp_seq (1319-1) 329 = exp_seq (1319-1) 0 := by decide
  have h_check : check_prime_period_cond 1319 329 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1319 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1319 329 (fun _ => false) h_check (n % 329) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1319 329 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1319 n hp h_flt (exp_seq_eq (1319-1) n) H_val

lemma not_dvd_1321 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1321 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1321 : ℕ).Prime := by decide
  have h_flt : (2^(1321-1)) % 1321 = 1 := by decide
  have h_per : exp_seq (1321-1) 10 = exp_seq (1321-1) 0 := by decide
  have h_check : check_prime_period_cond 1321 10 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1321 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1321 10 (fun _ => false) h_check (n % 10) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1321 10 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1321 n hp h_flt (exp_seq_eq (1321-1) n) H_val

lemma not_dvd_1327 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1327 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1327 : ℕ).Prime := by decide
  have h_flt : (2^(1327-1)) % 1327 = 1 := by decide
  have h_per : exp_seq (1327-1) 12 = exp_seq (1327-1) 0 := by decide
  have h_check : check_prime_period_cond 1327 12 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1327 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1327 12 (fun _ => false) h_check (n % 12) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1327 12 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1327 n hp h_flt (exp_seq_eq (1327-1) n) H_val

lemma not_dvd_1361 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1361 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1361 : ℕ).Prime := by decide
  have h_flt : (2^(1361-1)) % 1361 = 1 := by decide
  have h_per : exp_seq (1361-1) 4 = exp_seq (1361-1) 0 := by decide
  have h_check : check_prime_period_cond 1361 4 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1361 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1361 4 (fun _ => false) h_check (n % 4) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1361 4 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1361 n hp h_flt (exp_seq_eq (1361-1) n) H_val

lemma not_dvd_1367 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1367 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1367 : ℕ).Prime := by decide
  have h_flt : (2^(1367-1)) % 1367 = 1 := by decide
  have h_per : exp_seq (1367-1) 11 = exp_seq (1367-1) 0 := by decide
  have h_check : check_prime_period_cond 1367 11 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1367 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1367 11 (fun _ => false) h_check (n % 11) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1367 11 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1367 n hp h_flt (exp_seq_eq (1367-1) n) H_val

lemma not_dvd_1373 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1373 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1373 : ℕ).Prime := by decide
  have h_flt : (2^(1373-1)) % 1373 = 1 := by decide
  have h_per : exp_seq (1373-1) 147 = exp_seq (1373-1) 0 := by decide
  have h_check : check_prime_period_cond 1373 147 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1373 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1373 147 (fun _ => false) h_check (n % 147) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1373 147 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1373 n hp h_flt (exp_seq_eq (1373-1) n) H_val

lemma not_dvd_1381 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 1381 ∣ (2^(2^(58*n+26)+2) + 3) := by
  have hp : (1381 : ℕ).Prime := by decide
  have h_flt : (2^(1381-1)) % 1381 = 1 := by decide
  have h_per : exp_seq (1381-1) 22 = exp_seq (1381-1) 0 := by decide
  have h_check : check_prime_period_cond 1381 22 (fun _ => false) = true := by decide
  have H_val : val_mod_p 1381 n ≠ 0 := by
    have H := val_mod_p_not_zero_of_cond 1381 22 (fun _ => false) h_check (n % 22) (Nat.mod_lt _ (by decide))
    have h_mod := val_mod_p_mod 1381 22 n h_per
    rw [h_mod]
    apply H
    rfl
  exact not_dvd_of_val_mod_p 1381 n hp h_flt (exp_seq_eq (1381-1) n) H_val

