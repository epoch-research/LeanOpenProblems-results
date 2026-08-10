import FormalConjectures.Util.ProblemImports

open Nat BigOperators

lemma padicValNat_prod_apply {α : Type*} {p : ℕ} (pp : p.Prime)
    {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
    padicValNat p (S.prod g) = S.sum fun x => padicValNat p (g x) := by
  rw [← factorization_def _ pp]
  have h1 : (S.prod g).factorization p = S.sum fun x => (g x).factorization p := factorization_prod_apply hS
  rw [h1]
  congr 1
  ext x
  rw [factorization_def _ pp]

lemma dvd_of_padicValNat_le {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → padicValNat p d ≤ padicValNat p n) : d ∣ n := by
  rw [← factorization_prime_le_iff_dvd hd hn]
  intro p hp
  rw [factorization_def _ hp, factorization_def _ hp]
  exact h p hp

lemma rhs_ne_zero (n : ℕ) (_hn : n > 2) :
  2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
  have h1 : 2 ^ (n - 2) ≠ 0 := by positivity
  have h2 : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : k ≥ 1 := hk.1
    have h2k : 2 ^ k ≥ 2 := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
      exact this
    omega
  exact mul_ne_zero h1 h2

lemma case_p_two (n : ℕ) (hn : n > 2) :
  padicValNat 2 (n - 1).factorial ≤ padicValNat 2 (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
  have hd2 : n - 1 ≥ 2 := by omega
  have hd0 : n - 1 ≠ 0 := by omega
  have h_fact_ne : (n - 1).factorial ≠ 0 := factorial_ne_zero (n - 1)
  have hp_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_lt : (2 - 1) * padicValNat 2 (n - 1).factorial < n - 1 := by
    exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero 2 hd0
  have h_le : padicValNat 2 (n - 1).factorial ≤ n - 2 := by
    omega
  have h_mul : padicValNat 2 (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) =
      padicValNat 2 (2 ^ (n - 2)) + padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
    apply padicValNat.mul
    · positivity
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : k ≥ 1 := hk.1
      have h2k : 2 ^ k ≥ 2 := by
        have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
        exact this
      omega
  rw [h_mul]
  have h_pow : padicValNat 2 (2 ^ (n - 2)) = n - 2 := by
    exact padicValNat.prime_pow (n - 2)
  rw [h_pow]
  omega

lemma test_h2_ne_1 (p : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 1 := by
  have hp_ge_3 : p ≥ 3 := by
    have : p > 1 := pp.one_lt
    omega
  have : Fact (1 < p) := ⟨by omega⟩
  intro h
  have h_val : (2 : ZMod p).val = (1 : ZMod p).val := congr_arg ZMod.val h
  rw [ZMod.val_ofNat, ZMod.val_one] at h_val
  have h2p : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
  rw [h2p] at h_val
  omega

lemma orderOf_two_pos (n : ℕ) (hn : n > 2) (hp : Nat.Prime n) :
  0 < orderOf (2 : ZMod n) := by
  have : Fact (Nat.Prime n) := ⟨hp⟩
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have h_div : n ∣ 2 := by
      exact (ZMod.natCast_eq_zero_iff 2 n).mp h
    have : n ≤ 2 := Nat.le_of_dvd (by decide) h_div
    omega
  have h_pow := ZMod.pow_card_sub_one_eq_one h2
  have h_fin : IsOfFinOrder (2 : ZMod n) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n - 1, by omega, h_pow⟩
  exact h_fin.orderOf_pos

lemma order_ge_two (p : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) : orderOf (2 : ZMod p) ≥ 2 := by
  have hp_gt : p > 2 := by
    have : p > 1 := pp.one_lt
    omega
  have h21 : (2 : ZMod p) ≠ 1 := test_h2_ne_1 p pp hp2
  by_contra h_lt
  have h_ord : orderOf (2 : ZMod p) = 1 := by
    have h_pos := orderOf_two_pos p hp_gt pp
    omega
  have h_eq : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp h_ord
  exact h21 h_eq

lemma orderOf_two_dvd (n : ℕ) (hn : n > 2) (hp : Nat.Prime n) :
  orderOf (2 : ZMod n) ∣ n - 1 := by
  have : Fact (Nat.Prime n) := ⟨hp⟩
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have h_div : n ∣ 2 := by
      exact (ZMod.natCast_eq_zero_iff 2 n).mp h
    have : n ≤ 2 := Nat.le_of_dvd (by decide) h_div
    omega
  have h_pow := ZMod.pow_card_sub_one_eq_one h2
  exact orderOf_dvd_of_pow_eq_one h_pow

lemma order_le_p_sub_one (p : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) :
  orderOf (2 : ZMod p) ≤ p - 1 := by
  have hp_gt : p > 2 := by
    have : p > 1 := pp.one_lt
    omega
  have h_dvd := orderOf_two_dvd p hp_gt pp
  apply Nat.le_of_dvd (by omega) h_dvd

lemma padicVal_factorial_le_div_order (p d : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) (hd : d ≠ 0) :
  padicValNat p d.factorial ≤ (d - 1) / orderOf (2 : ZMod p) := by
  have hp_fact : Fact p.Prime := ⟨pp⟩
  have h_lt : (p - 1) * padicValNat p d.factorial < d :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hd
  have h_le : (p - 1) * padicValNat p d.factorial ≤ d - 1 := by omega
  have h_ord_le := order_le_p_sub_one p pp hp2
  have h_mul_le : orderOf (2 : ZMod p) * padicValNat p d.factorial ≤ (p - 1) * padicValNat p d.factorial :=
    Nat.mul_le_mul_right (padicValNat p d.factorial) h_ord_le
  have h_trans : orderOf (2 : ZMod p) * padicValNat p d.factorial ≤ d - 1 :=
    le_trans h_mul_le h_le
  have h_ord_pos : orderOf (2 : ZMod p) > 0 := by
    have hp_gt : p > 2 := by
      have : p > 1 := pp.one_lt
      omega
    exact orderOf_two_pos p hp_gt pp
  have h_trans2 : padicValNat p d.factorial * orderOf (2 : ZMod p) ≤ d - 1 := by
    rw [mul_comm]
    exact h_trans
  exact (Nat.le_div_iff_mul_le h_ord_pos).mpr h_trans2

lemma div_lemma_dvd (d o : ℕ) (ho : o ≥ 2) (hd : d ≥ 1) (h_dvd : o ∣ d) :
  d / o = (d - 1) / o + 1 := by
  rcases h_dvd with ⟨q, rfl⟩
  have hq : q ≥ 1 := by
    by_contra hc
    have : q = 0 := by omega
    subst this
    omega
  rw [Nat.mul_div_cancel_left _ (by omega)]
  have h_eq : o * q - 1 = (o - 1) + o * (q - 1) := by
    have h_prod : o * q = o * (q - 1) + o := by
      have hq1 : q = (q - 1) + 1 := by omega
      calc o * q = o * ((q - 1) + 1) := congr_arg (fun x => o * x) hq1
      _ = o * (q - 1) + o * 1 := mul_add o (q - 1) 1
      _ = o * (q - 1) + o := by rw [mul_one]
    rw [h_prod]
    omega
  rw [h_eq]
  rw [Nat.add_mul_div_left _ _ (by omega)]
  have : (o - 1) / o = 0 := Nat.div_eq_of_lt (by omega)
  rw [this]
  omega

lemma div_lemma_not_dvd (d o : ℕ) (ho : o ≥ 2) (hd : d ≥ 1) (h_not : ¬ o ∣ d) :
  d / o = (d - 1) / o := by
  have h_eq : d = o * (d / o) + (d % o) := (Nat.div_add_mod d o).symm
  have h_mod_lt : d % o < o := Nat.mod_lt d (by omega)
  have h_mod_ne_zero : d % o ≠ 0 := by
    intro h
    have : o ∣ d := Nat.dvd_of_mod_eq_zero h
    exact h_not this
  have h_mod_ge_1 : d % o ≥ 1 := by omega
  have h_sub : d - 1 = (d % o - 1) + o * (d / o) := by omega
  rw [h_sub]
  rw [Nat.add_mul_div_left _ _ (by omega)]
  have h_div_zero : (d % o - 1) / o = 0 := Nat.div_eq_of_lt (by omega)
  rw [h_div_zero, zero_add]

lemma div_target_lemma (d o : ℕ) : (d + 1 - 1) / o = d / o := by
  have : d + 1 - 1 = d := by omega
  rw [this]

lemma sum_padicVal_ge_div_order (p d : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) :
  (Finset.Ico 1 d).sum (fun k => padicValNat p (2 ^ k - 1)) ≥ (d - 1) / orderOf (2 : ZMod p) := by
  have ho_ge_2 := order_ge_two p pp hp2
  induction d with
  | zero =>
    -- d = 0
    simp
  | succ d ih =>
    by_cases hd0 : d = 0
    · subst hd0
      simp
    · have hd1 : d ≥ 1 := by omega
      rw [Finset.sum_Ico_succ_top hd1]
      have h_non_zero : 2 ^ d - 1 ≠ 0 := by
        have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (show 2 > 0 by decide) hd1
        omega
      have h_target := div_target_lemma d (orderOf (2 : ZMod p))
      by_cases h_dvd : orderOf (2 : ZMod p) ∣ d
      · rw [h_target]
        rw [div_lemma_dvd d _ ho_ge_2 hd1 h_dvd]
        have hp_dvd : p ∣ 2 ^ d - 1 := by
          have h_pow : (2 : ZMod p) ^ d = 1 := by
            rcases h_dvd with ⟨k, rfl⟩
            rw [pow_mul, pow_orderOf_eq_one, one_pow]
          have h_cast : ((2 ^ d : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
            rw [Nat.cast_pow, Nat.cast_two, Nat.cast_one]
            exact h_pow
          rw [ZMod.natCast_eq_natCast_iff' (2 ^ d) 1 p] at h_cast
          have h1p : 1 % p = 1 := by
            apply Nat.mod_eq_of_lt
            have : p > 1 := pp.one_lt
            omega
          rw [h1p] at h_cast
          have h_div_mod := Nat.div_add_mod (2 ^ d) p
          have : 2 ^ d - 1 = p * (2 ^ d / p) := by omega
          rw [this]
          exact dvd_mul_right p (2 ^ d / p)
        have hp_fact : Fact p.Prime := ⟨pp⟩
        have h_padic_ge : padicValNat p (2 ^ d - 1) ≥ 1 :=
          one_le_padicValNat_of_dvd h_non_zero hp_dvd
        omega
      · rw [h_target]
        rw [div_lemma_not_dvd d _ ho_ge_2 hd1 h_dvd]
        omega

lemma a_exact_divisibility (n : ℕ) (hn : n > 2) :
  (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  have hd0 : n - 1 ≠ 0 := by omega
  have h_fact_ne : (n - 1).factorial ≠ 0 := factorial_ne_zero (n - 1)
  have h_rhs_ne := rhs_ne_zero n hn
  apply dvd_of_padicValNat_le h_fact_ne h_rhs_ne
  intro p pp
  rcases eq_or_ne p 2 with rfl | hp2
  · exact case_p_two n hn
  · -- p is odd prime
    have : Fact p.Prime := ⟨pp⟩
    have hp_two_pow : padicValNat p (2 ^ (n - 2)) = 0 := by
      have hp_not_dvd_2 : ¬ p ∣ 2 := by
        intro h
        have : p ≤ 2 := Nat.le_of_dvd (by decide) h
        have : p > 1 := pp.one_lt
        omega
      have hp_not_dvd_pow : ¬ p ∣ 2 ^ (n - 2) := by
        rw [(Nat.Prime.prime pp).dvd_pow_iff_dvd (by omega)]
        exact hp_not_dvd_2
      exact padicValNat.eq_zero_of_not_dvd hp_not_dvd_pow
    have h_prod_ne : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : k ≥ 1 := hk.1
      have h2k : 2 ^ k ≥ 2 := by
        have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (show 2 > 0 by decide) hk1
        omega
      omega
    have h_mul : padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) =
        padicValNat p (2 ^ (n - 2)) + padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
      apply padicValNat.mul
      · positivity
      · exact h_prod_ne
    rw [h_mul, hp_two_pow, zero_add]
    rw [padicValNat_prod_apply pp]
    · have h_le1 := padicVal_factorial_le_div_order p (n - 1) pp hp2 hd0
      have h_le2 := sum_padicVal_ge_div_order p (n - 1) pp hp2
      have h_sub_eq : n - 1 - 1 = n - 2 := by omega
      rw [h_sub_eq] at h_le1 h_le2
      exact le_trans h_le1 h_le2
    · intro x hx
      rw [Finset.mem_Ico] at hx
      have h_non_zero : 2 ^ x - 1 ≠ 0 := by
        have : 2 ^ 1 ≤ 2 ^ x := Nat.pow_le_pow_right (show 2 > 0 by decide) hx.1
        omega
      exact h_non_zero

noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

theorem a_exact (n : ℕ) (hn : n > 2) :
  a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  have hd0 : n - 1 ≠ 0 := by omega
  unfold a
  split_ifs with h_zero
  · exfalso
    exact hd0 h_zero
  · dsimp only
    have h_sub : (n - 1).pred = n - 2 := by omega
    rw [h_sub]
    have h_div : (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) :=
      a_exact_divisibility n hn
    have h_fact_ne : (n - 1).factorial ≠ 0 := factorial_ne_zero (n - 1)
    exact Nat.div_mul_cancel h_div
