import Submission.Spec
open Nat

theorem test_proof : ¬ (∃ (a d : ℕ),
    2 ≤ a ∧ 1 ≤ d ∧ d ≤ 2025 ∧
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd1, hd2, H⟩
  have hd_mem : d ∈ (List.range 2026).drop 1 := by
    rw [List.mem_drop, List.mem_range]
    exact ⟨hd1, by omega⟩
  have hd_bad := List.all_eq_true.mp all_d_bad d hd_mem
  unfold d_is_bad at hd_bad
  revert hd_bad
  have h_pair := rfl : get_valid_pair d = get_valid_pair d
  generalize h_pair' : get_valid_pair d = pair
  rcases pair with ⟨p, q⟩
  intro hd_bad
  -- now we just have hd_bad as a bunch of &&
  repeat rw [Bool.and_eq_true] at hd_bad
  rcases hd_bad with ⟨⟨⟨⟨hpq_le, hpq_ne⟩, hpq_check⟩, hp_prime⟩, hq_prime⟩
  have h_pq_gt_0 : p * q > 0 := by
    have : p.Prime := my_is_prime_eq_prime p hp_prime
    have : q.Prime := my_is_prime_eq_prime q hq_prime
    have : p > 0 := Nat.Prime.pos ‹p.Prime›
    have : q > 0 := Nat.Prime.pos ‹q.Prime›
    omega
  have ⟨i, hi_lt, ⟨hip, hiq⟩⟩ := check_pair_lifts p q d a h_pq_gt_0 hpq_check
  have h_pq_le_150 : p * q ≤ 150 := Nat.ble_eq_true_eq_le.mp hpq_le
  have hi_150 : i < 150 := by omega
  have H_i := H ⟨i, hi_150⟩
  have H_cond : A381159_condition (a + i * d) := H_i
  have haid : a + i * d ≥ 2 := by omega
  have h_p_prime : p.Prime := my_is_prime_eq_prime p hp_prime
  have h_q_prime : q.Prime := my_is_prime_eq_prime q hq_prime
  have h_p_dvd : p ∣ a + i * d := Nat.dvd_of_mod_eq_zero hip
  have h_q_dvd : q ∣ a + i * d := Nat.dvd_of_mod_eq_zero hiq
  have h_p_in : p ∈ (a + i * d).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨h_p_prime, h_p_dvd, by omega⟩
  have h_q_in : q ∈ (a + i * d).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨h_q_prime, h_q_dvd, by omega⟩
  unfold A381159_condition at H_cond
  have h_p_im : (p % 10) ∈ (a + i * d).primeFactors.image (fun x => x % 10) := by
    rw [Finset.mem_image]
    use p
    exact ⟨h_p_in, rfl⟩
  have h_q_im : (q % 10) ∈ (a + i * d).primeFactors.image (fun x => x % 10) := by
    rw [Finset.mem_image]
    use q
    exact ⟨h_q_in, rfl⟩
  have h_eq : p % 10 = q % 10 := by
    -- card <= 1 implies any two elements are equal
    have h_card := H_cond
    -- mathlib card_le_one
    sorry
