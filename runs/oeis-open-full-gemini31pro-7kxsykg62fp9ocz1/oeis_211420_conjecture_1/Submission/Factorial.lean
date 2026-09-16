import Submission.DivIneq
import Mathlib

open Nat

lemma padicValNat_dvd_of_le {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → padicValNat p d ≤ padicValNat p n) : d ∣ n := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd n d).mpr
  intro p k hp hk
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_dvd_iff_le hd] at hk
  rw [padicValNat_dvd_iff_le hn]
  exact le_trans hk (h p hp)

lemma a_dvd (n : ℕ) : (4 * n).factorial * (3 * n).factorial * (2 * n).factorial ∣ (8 * n).factorial * n.factorial := by
  apply padicValNat_dvd_of_le
  · exact mul_ne_zero (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (factorial_ne_zero _)
  · exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
  · intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_pos : 0 < p := hp.pos
    rw [padicValNat.mul (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (factorial_ne_zero _)]
    rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]
    rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]
    
    let b := 8 * n + 1
    have hb8 : Nat.log p (8 * n) < b := by
      calc Nat.log p (8 * n) ≤ 8 * n := Nat.log_le_self p (8 * n)
      _ < 8 * n + 1 := by omega
    have hb4 : Nat.log p (4 * n) < b := by
      calc Nat.log p (4 * n) ≤ 4 * n := Nat.log_le_self p (4 * n)
      _ < 8 * n + 1 := by omega
    have hb3 : Nat.log p (3 * n) < b := by
      calc Nat.log p (3 * n) ≤ 3 * n := Nat.log_le_self p (3 * n)
      _ < 8 * n + 1 := by omega
    have hb2 : Nat.log p (2 * n) < b := by
      calc Nat.log p (2 * n) ≤ 2 * n := Nat.log_le_self p (2 * n)
      _ < 8 * n + 1 := by omega
    have hb1 : Nat.log p n < b := by
      calc Nat.log p n ≤ n := Nat.log_le_self p n
      _ < 8 * n + 1 := by omega

    rw [padicValNat_factorial hb8]
    rw [padicValNat_factorial hb4]
    rw [padicValNat_factorial hb3]
    rw [padicValNat_factorial hb2]
    rw [padicValNat_factorial hb1]

    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    
    apply Finset.sum_le_sum
    intro i _
    have hpi_pos : 0 < p ^ i := by positivity
    have H := div_ineq_nat n 0 (p^i) hpi_pos (by omega)
    have eq1 : 4 * n - 0 = 4 * n := by omega
    have eq2 : 8 * n - 2 * 0 = 8 * n := by omega
    have eq3 : 8 * 0 = 0 := by omega
    rw [eq1, eq2, eq3] at H
    have eq4 : 0 / p ^ i = 0 := Nat.zero_div _
    rw [eq4] at H
    omega

lemma V_dvd (n r : ℕ) (hr : r ≤ 4 * n) :
    (4 * n - r).factorial * (3 * n).factorial * (2 * n).factorial ∣ (8 * n - 2 * r).factorial * (8 * r).factorial * n.factorial := by
  apply padicValNat_dvd_of_le
  · exact mul_ne_zero (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (factorial_ne_zero _)
  · exact mul_ne_zero (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (factorial_ne_zero _)
  · intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_pos : 0 < p := hp.pos
    rw [padicValNat.mul (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (factorial_ne_zero _)]
    rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]
    rw [padicValNat.mul (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (factorial_ne_zero _)]
    rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]

    let b := max (8 * n) (8 * r) + 1
    have hb_8n_2r : Nat.log p (8 * n - 2 * r) < b := by
      calc Nat.log p (8 * n - 2 * r) ≤ 8 * n - 2 * r := Nat.log_le_self p _
      _ ≤ 8 * n := by omega
      _ ≤ max (8 * n) (8 * r) := le_max_left _ _
      _ < b := by omega
    have hb_8r : Nat.log p (8 * r) < b := by
      calc Nat.log p (8 * r) ≤ 8 * r := Nat.log_le_self p _
      _ ≤ max (8 * n) (8 * r) := le_max_right _ _
      _ < b := by omega
    have hb_n : Nat.log p n < b := by
      calc Nat.log p n ≤ n := Nat.log_le_self p _
      _ ≤ 8 * n := by omega
      _ ≤ max (8 * n) (8 * r) := le_max_left _ _
      _ < b := by omega
    have hb_4n_r : Nat.log p (4 * n - r) < b := by
      calc Nat.log p (4 * n - r) ≤ 4 * n - r := Nat.log_le_self p _
      _ ≤ 8 * n := by omega
      _ ≤ max (8 * n) (8 * r) := le_max_left _ _
      _ < b := by omega
    have hb_3n : Nat.log p (3 * n) < b := by
      calc Nat.log p (3 * n) ≤ 3 * n := Nat.log_le_self p _
      _ ≤ 8 * n := by omega
      _ ≤ max (8 * n) (8 * r) := le_max_left _ _
      _ < b := by omega
    have hb_2n : Nat.log p (2 * n) < b := by
      calc Nat.log p (2 * n) ≤ 2 * n := Nat.log_le_self p _
      _ ≤ 8 * n := by omega
      _ ≤ max (8 * n) (8 * r) := le_max_left _ _
      _ < b := by omega

    rw [padicValNat_factorial hb_8n_2r]
    rw [padicValNat_factorial hb_8r]
    rw [padicValNat_factorial hb_n]
    rw [padicValNat_factorial hb_4n_r]
    rw [padicValNat_factorial hb_3n]
    rw [padicValNat_factorial hb_2n]

    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    
    apply Finset.sum_le_sum
    intro i _
    have hpi_pos : 0 < p ^ i := by positivity
    exact div_ineq_nat n r (p^i) hpi_pos hr

