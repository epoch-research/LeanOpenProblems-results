import Mathlib

open Nat Int Finset

/-- The auxiliary integer sequence $F(n) = n! \sum_{k=2}^n \frac{(-1)^k}{k}$, corresponding to OEIS A024168. -/
def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

lemma F_aux_of_ge_two {n : ℕ} (hn : n ≥ 2) :
  F_aux n = Finset.sum (Icc 2 n) (fun k : ℕ => ((n.factorial : ℤ) / (k : ℤ)) * (if k % 2 = 0 then 1 else -1)) := by
  unfold F_aux
  have : ¬ n < 2 := by omega
  simp [this]

lemma sum_split (m : ℕ) (hm : m ≥ 1) (f : ℕ → ℤ) :
  Finset.sum (Icc 2 (m + 1)) f = Finset.sum (Icc 2 m) f + f (m + 1) := by
  have : 2 ≤ m + 1 := by omega
  rw [Finset.sum_Icc_succ_top this]

lemma fact_div (m : ℕ) : (((m + 1).factorial : ℤ) / ((m + 1 : ℕ) : ℤ)) = (m.factorial : ℤ) := by
  have h1 : ((m + 1).factorial : ℤ) = ((m + 1 : ℕ) : ℤ) * (m.factorial : ℤ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [h1]
  have h2 : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  rw [Int.mul_ediv_cancel_left _ h2]

lemma int_div_assoc (a : ℤ) {b c : ℤ} (h : b ∣ c) : (a * c) / b = a * (c / b) := by
  rw [Int.mul_ediv_assoc a h]

lemma k_dvd_fact {k m : ℕ} (hk1 : 0 < k) (hk2 : k ≤ m) : (k : ℤ) ∣ (m.factorial : ℤ) := by
  exact Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hk1 hk2)

lemma F_aux_recurrence (m : ℕ) (hm : m ≥ 1) :
  F_aux (m + 1) = (m + 1) * F_aux m + (if (m + 1) % 2 = 0 then 1 else -1) * (m.factorial : ℤ) := by
  by_cases h2 : m ≥ 2
  · rw [F_aux_of_ge_two (by omega)]
    rw [sum_split m hm]
    rw [F_aux_of_ge_two h2]
    rw [fact_div]
    have h_sum : Finset.sum (Icc 2 m) (fun k : ℕ => (((m + 1).factorial : ℤ) / (k : ℤ)) * (if k % 2 = 0 then 1 else -1)) =
                 (m + 1 : ℤ) * Finset.sum (Icc 2 m) (fun k : ℕ => ((m.factorial : ℤ) / (k : ℤ)) * (if k % 2 = 0 then 1 else -1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk1 : 0 < k := by omega
      have hk2 : k ≤ m := by omega
      have hdvd : (k : ℤ) ∣ (m.factorial : ℤ) := k_dvd_fact hk1 hk2
      have h_fact : ((m + 1).factorial : ℤ) = (m + 1 : ℤ) * (m.factorial : ℤ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [h_fact]
      rw [int_div_assoc (m + 1 : ℤ) hdvd]
      ring
    rw [h_sum]
    ring
  · have hm1 : m = 1 := by omega
    subst hm1
    rfl

lemma padicValNat_add_of_lt_int (p : ℕ) [hp : Fact (Nat.Prime p)] {a b : ℤ} (ha : a ≠ 0)
  (hlt : padicValNat p a.natAbs < padicValNat p b.natAbs) :
  padicValNat p (a + b).natAbs = padicValNat p a.natAbs := by
  let u := padicValNat p a.natAbs
  let v := padicValNat p b.natAbs
  have hab_nz : a + b ≠ 0 := by
    intro hc
    have h_eq : a = -b := by omega
    have h_abs_eq : a.natAbs = b.natAbs := by
      rw [h_eq, Int.natAbs_neg]
    rw [h_abs_eq] at hlt
    omega
  have hab_nat_nz : (a + b).natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr hab_nz
  have h_dvd_u : p ^ u ∣ (a + b).natAbs := by
    have h_equiv : p ^ u ∣ (a + b).natAbs ↔ (p : ℤ) ^ u ∣ a + b := by
      have h_abs : ((p : ℤ) ^ u).natAbs = p ^ u := by
        rw [← Int.natCast_pow, Int.natAbs_natCast]
      rw [← h_abs]
      exact Int.natAbs_dvd_natAbs
    rw [h_equiv]
    have h_a : (p : ℤ) ^ u ∣ a := by
      have h_equiv_a : (p : ℤ) ^ u ∣ a ↔ p ^ u ∣ a.natAbs := by
        have h_abs : ((p : ℤ) ^ u).natAbs = p ^ u := by
          rw [← Int.natCast_pow, Int.natAbs_natCast]
        rw [← h_abs]
        exact Int.natAbs_dvd_natAbs.symm
      rw [h_equiv_a]
      exact pow_padicValNat_dvd
    have h_b : (p : ℤ) ^ u ∣ b := by
      have h_equiv_b : (p : ℤ) ^ u ∣ b ↔ p ^ u ∣ b.natAbs := by
        have h_abs : ((p : ℤ) ^ u).natAbs = p ^ u := by
          rw [← Int.natCast_pow, Int.natAbs_natCast]
        rw [← h_abs]
        exact Int.natAbs_dvd_natAbs.symm
      rw [h_equiv_b]
      have : u ≤ v := by omega
      have h_pv : p ^ v ∣ b.natAbs := pow_padicValNat_dvd
      have h_puv : p ^ u ∣ p ^ v := Nat.pow_dvd_pow p this
      exact dvd_trans h_puv h_pv
    exact dvd_add h_a h_b
  have h_not_dvd_succ : ¬ p ^ (u + 1) ∣ (a + b).natAbs := by
    intro h
    have h_b_succ : (p : ℤ) ^ (u + 1) ∣ b := by
      have h_equiv_b : (p : ℤ) ^ (u + 1) ∣ b ↔ p ^ (u + 1) ∣ b.natAbs := by
        have h_abs : ((p : ℤ) ^ (u + 1)).natAbs = p ^ (u + 1) := by
          rw [← Int.natCast_pow, Int.natAbs_natCast]
        rw [← h_abs]
        exact Int.natAbs_dvd_natAbs.symm
      rw [h_equiv_b]
      have : u + 1 ≤ v := hlt
      have h_pv : p ^ v ∣ b.natAbs := pow_padicValNat_dvd
      have h_puv : p ^ (u + 1) ∣ p ^ v := Nat.pow_dvd_pow p this
      exact dvd_trans h_puv h_pv
    have h_a_succ : (p : ℤ) ^ (u + 1) ∣ a := by
      have h_equiv : p ^ (u + 1) ∣ (a + b).natAbs ↔ (p : ℤ) ^ (u + 1) ∣ a + b := by
        have h_abs : ((p : ℤ) ^ (u + 1)).natAbs = p ^ (u + 1) := by
          rw [← Int.natCast_pow, Int.natAbs_natCast]
        rw [← h_abs]
        exact Int.natAbs_dvd_natAbs
      rw [h_equiv] at h
      rcases h with ⟨x, hx⟩
      rcases h_b_succ with ⟨y, hy⟩
      use x - y
      calc a = (a + b) - b := by omega
      _ = (p : ℤ) ^ (u + 1) * x - (p : ℤ) ^ (u + 1) * y := by rw [hx, hy]
      _ = (p : ℤ) ^ (u + 1) * (x - y) := by ring
    have h_not : ¬ p ^ (u + 1) ∣ a.natAbs := by
      intro hc
      rw [padicValNat_dvd_iff] at hc
      rcases hc with h1 | h2
      · exact Int.natAbs_ne_zero.mpr ha h1
      · omega
    have h_equiv_a : (p : ℤ) ^ (u + 1) ∣ a ↔ p ^ (u + 1) ∣ a.natAbs := by
      have h_abs : ((p : ℤ) ^ (u + 1)).natAbs = p ^ (u + 1) := by
        rw [← Int.natCast_pow, Int.natAbs_natCast]
      rw [← h_abs]
      exact Int.natAbs_dvd_natAbs.symm
    rw [h_equiv_a] at h_a_succ
    exact h_not h_a_succ
  rw [padicValNat_dvd_iff] at h_dvd_u
  rcases h_dvd_u with h1 | h2
  · exact False.elim (hab_nat_nz h1)
  · rw [padicValNat_dvd_iff] at h_not_dvd_succ
    push_neg at h_not_dvd_succ
    rcases h_not_dvd_succ with ⟨_, h4⟩
    omega

lemma log_lt_factorial_valuation (m : ℕ) (hm : m ≥ 4) : Nat.log 2 m < padicValNat 2 (Nat.factorial m) := by
  revert hm
  apply Nat.le_induction
  · -- Base case
    have h1 : Nat.log 2 4 = 2 := rfl
    have h2 : Nat.factorial 4 = 24 := rfl
    have h_dvd3 : 2 ^ 3 ∣ 24 := by decide
    rw [padicValNat_dvd_iff] at h_dvd3
    have h_not_dvd4 : ¬ 2 ^ 4 ∣ 24 := by decide
    rw [padicValNat_dvd_iff] at h_not_dvd4
    have h3 : padicValNat 2 24 = 3 := by omega
    rw [h1, h2, h3]
    decide
  · -- Inductive step
    intro k hk ih
    have h_log_le : Nat.log 2 (k + 1) ≤ Nat.log 2 k + 1 := by
      have h_lt : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by decide) k
      have h_le_pow : k + 1 ≤ 2 ^ (Nat.log 2 k + 1) := by omega
      have h_lt_pow : k + 1 < 2 ^ (Nat.log 2 k + 2) := by
        have : 2 ^ (Nat.log 2 k + 1) < 2 ^ (Nat.log 2 k + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
        omega
      have h_equiv : Nat.log 2 k + 2 ≤ Nat.log 2 (k + 1) ↔ 2 ^ (Nat.log 2 k + 2) ≤ k + 1 := by
        exact Nat.le_log_iff_pow_le (by decide) (by omega)
      have h_not : ¬ 2 ^ (Nat.log 2 k + 2) ≤ k + 1 := by omega
      rw [← h_equiv] at h_not
      omega
    by_cases hk_even : (k + 1) % 2 = 0
    · -- k + 1 is even
      have h_val_ge1 : padicValNat 2 (k + 1) ≥ 1 := by
        have h_dvd : 2 ^ 1 ∣ k + 1 := by
          simp only [pow_one]
          exact Nat.dvd_of_mod_eq_zero hk_even
        rw [padicValNat_dvd_iff] at h_dvd
        rcases h_dvd with hc | h_ge
        · omega
        · exact h_ge
      have h_fact_succ : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
        rw [Nat.factorial_succ]
      have h_val_succ : padicValNat 2 (Nat.factorial (k + 1)) = padicValNat 2 (k + 1) + padicValNat 2 (Nat.factorial k) := by
        rw [h_fact_succ]
        exact padicValNat.mul (by omega) (by exact Nat.factorial_ne_zero k)
      omega
    · -- k + 1 is odd, so Nat.log 2 (k + 1) = Nat.log 2 k
      have h_log_eq : Nat.log 2 (k + 1) = Nat.log 2 k := by
        have h_le : Nat.log 2 k ≤ Nat.log 2 (k + 1) := Nat.log_mono (by decide) (by decide) (by omega)
        have h_lt_or_eq : Nat.log 2 k < Nat.log 2 (k + 1) ∨ Nat.log 2 k = Nat.log 2 (k + 1) := by omega
        rcases h_lt_or_eq with h_lt | h_eq
        · -- log 2 k < log 2 (k + 1) => log 2 k + 1 <= log 2 (k + 1)
          have h_pow_le : 2 ^ (Nat.log 2 k + 1) ≤ k + 1 := by
            have h_pow_mono : 2 ^ (Nat.log 2 k + 1) ≤ 2 ^ (Nat.log 2 (k + 1)) := Nat.pow_le_pow_right (n := 2) (by decide) h_lt
            have h_le2 : 2 ^ Nat.log 2 (k + 1) ≤ k + 1 := @Nat.pow_log_le_self 2 (k + 1) (by omega)
            exact le_trans h_pow_mono h_le2
          have h_lt_k : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by decide) k
          have h_eq_pow : k + 1 = 2 ^ (Nat.log 2 k + 1) := by omega
          have hk_even_contra : (k + 1) % 2 = 0 := by
            rw [h_eq_pow]
            have h_pow_succ : 2 ^ (Nat.log 2 k + 1) = 2 * 2 ^ (Nat.log 2 k) := by ring
            rw [h_pow_succ]
            exact Nat.mul_mod_right 2 _
          exact False.elim (hk_even hk_even_contra)
        · exact h_eq.symm
      have h_fact_succ : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
        rw [Nat.factorial_succ]
      have h_val_succ : padicValNat 2 (Nat.factorial (k + 1)) = padicValNat 2 (k + 1) + padicValNat 2 (Nat.factorial k) := by
        rw [h_fact_succ]
        exact padicValNat.mul (by omega) (by exact Nat.factorial_ne_zero k)
      omega

lemma F_aux_v2_formula (n : ℕ) (hn : n ≥ 2) :
  padicValNat 2 (F_aux n).natAbs + Nat.log 2 n = padicValNat 2 (Nat.factorial n) := by
  revert hn
  apply Nat.le_induction
  · -- Base case n = 2
    have h_f2 : F_aux 2 = 1 := by
      rw [F_aux_of_ge_two (by omega)]
      rfl
    have h_log2 : Nat.log 2 2 = 1 := rfl
    have h_f2_abs : (F_aux 2).natAbs = 1 := by rw [h_f2]; rfl
    have h_val2 : padicValNat 2 1 = 0 := by
      have h_dvd : ¬ 2 ^ 1 ∣ 1 := by decide
      rw [padicValNat_dvd_iff] at h_dvd
      omega
    have h_fact2 : Nat.factorial 2 = 2 := rfl
    have h_val_fact2 : padicValNat 2 2 = 1 := by
      have h_dvd1 : 2 ^ 1 ∣ 2 := by decide
      have h_dvd2 : ¬ 2 ^ 2 ∣ 2 := by decide
      rw [padicValNat_dvd_iff] at h_dvd1 h_dvd2
      omega
    rw [h_log2, h_f2_abs, h_val2, h_fact2, h_val_fact2]
  · -- Inductive step
    intro k hk ih
    have hk_nz : k ≠ 0 := by omega
    have h_fk_nz : F_aux k ≠ 0 := by
      have : k = 2 ∨ k = 3 ∨ k ≥ 4 := by omega
      rcases this with rfl | rfl | hk4
      · -- k = 2
        have : F_aux 2 = 1 := by
          rw [F_aux_of_ge_two (by omega)]
          rfl
        omega
      · -- k = 3
        have : F_aux 3 = 1 := by
          rw [F_aux_of_ge_two (by omega)]
          rfl
        omega
      · -- k >= 4
        intro hc
        have h_abs : (F_aux k).natAbs = 0 := by rw [hc]; rfl
        have h_val : padicValNat 2 (F_aux k).natAbs = 0 := by rw [h_abs]; rfl
        have h_eq : Nat.log 2 k = padicValNat 2 (Nat.factorial k) := by omega
        have h_lt : Nat.log 2 k < padicValNat 2 (Nat.factorial k) := log_lt_factorial_valuation k hk4
        omega
    have h_a_nz : (k + 1 : ℤ) * F_aux k ≠ 0 := by
      apply mul_ne_zero
      · omega
      · exact h_fk_nz
    have h_log_ne : padicValNat 2 (k + 1) ≠ Nat.log 2 k := by
      exact (Nat.log_ne_padicValNat_succ hk_nz).symm
    have h_log_lt_or_gt : padicValNat 2 (k + 1) < Nat.log 2 k ∨ padicValNat 2 (k + 1) > Nat.log 2 k := by omega
    let v := padicValNat 2 (F_aux k).natAbs
    let L := Nat.log 2 k
    let e := padicValNat 2 (k + 1)
    let V_fact := padicValNat 2 (Nat.factorial k)
    have h_rec : F_aux (k + 1) = (k + 1 : ℤ) * F_aux k + (if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) := by
      exact F_aux_recurrence k (by omega)
    have h_b_abs : (((if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) : ℤ).natAbs) = Nat.factorial k := by
      rw [Int.natAbs_mul]
      split_ifs with h_if
      · simp
      · simp
    rcases h_log_lt_or_gt with h_lt_L | h_gt
    · -- e < L
      have h_log_eq : Nat.log 2 (k + 1) = L := by
        have h_le : Nat.log 2 k ≤ Nat.log 2 (k + 1) := Nat.log_mono (by decide) (by decide) (by omega)
        have h_lt_or_eq : Nat.log 2 k < Nat.log 2 (k + 1) ∨ Nat.log 2 k = Nat.log 2 (k + 1) := by omega
        rcases h_lt_or_eq with h_lt_pow | h_eq
        · -- log 2 k < log 2 (k + 1) => log 2 k + 1 <= log 2 (k + 1)
          have h_pow_le : 2 ^ (L + 1) ≤ k + 1 := by
            have h_pow_mono : 2 ^ (L + 1) ≤ 2 ^ (Nat.log 2 (k + 1)) := Nat.pow_le_pow_right (n := 2) (by decide) h_lt_pow
            have h_le2 : 2 ^ Nat.log 2 (k + 1) ≤ k + 1 := @Nat.pow_log_le_self 2 (k + 1) (by omega)
            exact le_trans h_pow_mono h_le2
          have h_lt_k : k < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (b := 2) (by decide) k
          have h_eq_pow : k + 1 = 2 ^ (L + 1) := by omega
          have hk_even_contra : (k + 1) % 2 = 0 := by
            rw [h_eq_pow]
            have h_pow_succ : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
            rw [h_pow_succ]
            exact Nat.mul_mod_right 2 _
          have h_val_ge : padicValNat 2 (k + 1) = L + 1 := by
            rw [h_eq_pow]
            exact padicValNat.prime_pow (p := 2) (L + 1)
          omega
        · exact h_eq.symm
      have h_a_abs : (((k + 1 : ℤ) * F_aux k).natAbs) = (k + 1) * (F_aux k).natAbs := by
        rw [Int.natAbs_mul]
        have : (k + 1 : ℤ).natAbs = k + 1 := rfl
        rw [this]
      have h_val_a : padicValNat 2 ((k + 1 : ℤ) * F_aux k).natAbs = e + v := by
        rw [h_a_abs]
        exact padicValNat.mul (by omega) (by exact Int.natAbs_ne_zero.mpr h_fk_nz)
      have h_val_b : padicValNat 2 ((if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) : ℤ).natAbs = V_fact := by
        rw [h_b_abs]
      have h_lt_v : e + v < V_fact := by omega
      have h_add := @padicValNat_add_of_lt_int 2 _ ((k + 1 : ℤ) * F_aux k) ((if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) : ℤ) h_a_nz (by rw [h_val_a, h_val_b]; exact h_lt_v)
      have h_val_succ : padicValNat 2 (F_aux (k + 1)).natAbs = e + v := by
        rw [h_rec, h_add, h_val_a]
      have h_fact_succ : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
        rw [Nat.factorial_succ]
      have h_val_fact_succ : padicValNat 2 (Nat.factorial (k + 1)) = e + V_fact := by
        rw [h_fact_succ]
        exact padicValNat.mul (by omega) (by exact Nat.factorial_ne_zero k)
      omega
    · -- e > L
      have h_log_eq : Nat.log 2 (k + 1) = e := by
        have h_pow_le : 2 ^ e ≤ k + 1 := Nat.le_of_dvd (by omega) (pow_padicValNat_dvd (p := 2) (n := k + 1))
        have h_lt_pow : k < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (b := 2) (by decide) k
        have h_eq_pow : k + 1 = 2 ^ e := by
          have : e ≥ L + 1 := by omega
          have h_pow_mono : 2 ^ (L + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (n := 2) (by decide) this
          omega
        rw [h_eq_pow]
        exact Nat.log_pow (by decide) e
      have h_a_abs : (((k + 1 : ℤ) * F_aux k).natAbs) = (k + 1) * (F_aux k).natAbs := by
        rw [Int.natAbs_mul]
        have : (k + 1 : ℤ).natAbs = k + 1 := rfl
        rw [this]
      have h_val_a : padicValNat 2 ((k + 1 : ℤ) * F_aux k).natAbs = e + v := by
        rw [h_a_abs]
        exact padicValNat.mul (by omega) (by exact Int.natAbs_ne_zero.mpr h_fk_nz)
      have h_val_b : padicValNat 2 ((if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) : ℤ).natAbs = V_fact := by
        rw [h_b_abs]
      have h_gt_v : e + v > V_fact := by omega
      have h_b_nz : ((if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) : ℤ) ≠ 0 := by
        rw [← Int.natAbs_ne_zero, h_b_abs]
        exact Nat.factorial_ne_zero k
      have h_add := @padicValNat_add_of_lt_int 2 _ ((if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) : ℤ) ((k + 1 : ℤ) * F_aux k) h_b_nz (by rw [h_val_a, h_val_b]; exact h_gt_v)
      have h_rec_comm : F_aux (k + 1) = ((if (k + 1) % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial k) : ℤ) + ((k + 1 : ℤ) * F_aux k) := by
        rw [h_rec]
        ring
      have h_val_succ : padicValNat 2 (F_aux (k + 1)).natAbs = V_fact := by
        rw [h_rec_comm, h_add, h_val_b]
      have h_fact_succ : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
        rw [Nat.factorial_succ]
      have h_val_fact_succ : padicValNat 2 (Nat.factorial (k + 1)) = e + V_fact := by
        rw [h_fact_succ]
        exact padicValNat.mul (by omega) (by exact Nat.factorial_ne_zero k)
      omega
