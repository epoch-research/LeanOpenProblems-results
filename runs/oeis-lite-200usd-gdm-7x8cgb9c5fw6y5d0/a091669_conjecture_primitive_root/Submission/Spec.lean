import FormalConjectures.Util.ProblemImports

open Nat BigOperators

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

lemma a_of_gt_two (n : ℕ) (hn : n > 2) :
    a (n - 1) = ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) / (n - 1).factorial := by
  have h1 : n - 1 ≠ 0 := by omega
  unfold a
  split_ifs with h
  · contradiction
  · dsimp
    have h_sub : n - 1 - 1 = n - 2 := by omega
    rw [h_sub]

theorem prime_case (n : ℕ) (hn : n > 2) (hp : Nat.Prime n) (hnp : ¬ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) :
    n ∣ (2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  have h_tot : Nat.totient n = n - 1 := Nat.totient_prime hp
  rw [h_tot] at hnp
  rw [IsPrimitiveRoot.iff_orderOf] at hnp
  have h2_ne : (2 : ZMod n) ≠ 0 := by
    intro hc
    have h_div : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp hc
    have h_le := Nat.le_of_dvd (by decide) h_div
    omega
  haveI : Fact n.Prime := ⟨hp⟩
  have hdvd : orderOf (2 : ZMod n) ∣ n - 1 := ZMod.orderOf_dvd_card_sub_one h2_ne
  set d := orderOf (2 : ZMod n)
  have h_unit : IsUnit (2 : ZMod n) := isUnit_iff_ne_zero.mpr h2_ne
  have h_val : (h_unit.unit : ZMod n) = 2 := IsUnit.unit_spec h_unit
  have h_order : d = orderOf h_unit.unit := by
    change orderOf (2 : ZMod n) = orderOf h_unit.unit
    have h1 : orderOf (2 : ZMod n) = orderOf (h_unit.unit : ZMod n) := by
      rw [h_val]
    rw [h1, orderOf_units]
  have hd_pos : 0 < d := by
    rw [h_order]
    exact orderOf_pos h_unit.unit
  have h_sub : n - 1 > 0 := by omega
  have h_le := Nat.le_of_dvd h_sub hdvd
  have hd_lt : d < n - 1 := by omega
  have hd_mem : d ∈ Finset.Ico 1 (n - 1) := by
    rw [Finset.mem_Ico]
    exact ⟨hd_pos, hd_lt⟩
  have h_dvd_prod : 2 ^ d - 1 ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) hd_mem
  have h_pow : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
  have h_pow_nat : ((2 ^ d : ℕ) : ZMod n) = 1 := by
    have h_cast : (2 : ZMod n) ^ d = ((2 ^ d : ℕ) : ZMod n) := by norm_cast
    rw [← h_cast]
    exact h_pow
  have h_sub_zero : ((2 ^ d - 1 : ℕ) : ZMod n) = 0 := by
    have h_ge : 2 ^ d ≥ 1 := by
      have : 2 ^ d ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hd_pos
      omega
    have h_sub_cast : ((2 ^ d - 1 : ℕ) : ZMod n) = ((2 ^ d : ℕ) : ZMod n) - 1 := by
      rw [Nat.cast_sub h_ge, Nat.cast_one]
    rw [h_sub_cast, h_pow_nat, sub_self]
  have h_div_n : n ∣ 2 ^ d - 1 := (ZMod.natCast_eq_zero_iff (2 ^ d - 1) n).mp h_sub_zero
  have h_div_prod : n ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := dvd_trans h_div_n h_dvd_prod
  exact dvd_mul_of_dvd_right h_div_prod (2 ^ (n - 2))

lemma d_ge_two (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≥ 3) (d : ℕ) (hd : d = orderOf (2 : ZMod p)) :
  d ≥ 2 := by
  by_contra! h_lt
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp hc
    have hle := Nat.le_of_dvd (by decide) hdvd
    omega
  have h_unit : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr h2_ne
  have h_val : (h_unit.unit : ZMod p) = 2 := IsUnit.unit_spec h_unit
  have h_order : d = orderOf h_unit.unit := by
    rw [hd]
    have h1 : orderOf (2 : ZMod p) = orderOf (h_unit.unit : ZMod p) := by
      rw [h_val]
    rw [h1, orderOf_units]
  have hd_pos : 0 < d := by
    rw [h_order]
    exact orderOf_pos h_unit.unit
  have hd_eq : d = 1 := by omega
  have h_pow : (2 : ZMod p) ^ d = 1 := by
    rw [hd]
    exact pow_orderOf_eq_one (2 : ZMod p)
  have h_pow' : (2 : ZMod p) = 1 := by rwa [hd_eq, pow_one] at h_pow
  have h_eq_zero : (1 : ZMod p) = 0 := by
    calc (1 : ZMod p) = 2 - 1 := by norm_num
    _ = 1 - 1 := by rw [h_pow']
    _ = 0 := by norm_num
  have h_div : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by exact_mod_cast h_eq_zero)
  have : p ≤ 1 := Nat.le_of_dvd (by decide) h_div
  omega

lemma sum_padic_induction (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≥ 3) (d : ℕ) (hd : d = orderOf (2 : ZMod p)) (n : ℕ) (hn : n ≥ 2) :
  (n - 1) / d ≤ ∑ k ∈ Finset.Ico 1 n, padicValNat p (2 ^ k - 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hd2 : d ≥ 2 := d_ge_two p hp3 d hd
    have h_div : 1 / d = 0 := Nat.div_eq_of_lt (by omega)
    rw [h_div]
    omega
  | succ k hk ih =>
    have hd2 : d ≥ 2 := d_ge_two p hp3 d hd
    have hd_pos : d > 0 := by omega
    have h_mem : k ∉ Finset.Ico 1 k := by
      rw [Finset.mem_Ico]
      omega
    have h_insert : Finset.Ico 1 (k + 1) = insert k (Finset.Ico 1 k) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [h_insert, Finset.sum_insert h_mem]
    have h_target : (k + 1 - 1) / d = k / d := by
      have : k + 1 - 1 = k := by omega
      rw [this]
    rw [h_target]
    by_cases hd_div : d ∣ k
    · rcases hd_div with ⟨m, rfl⟩
      have hm_pos : m ≥ 1 := by
        by_contra! hc
        interval_cases m
        · have : d * 0 = 0 := by ring
          omega
      obtain ⟨d', hd_eq⟩ := Nat.exists_eq_add_of_le hd2
      have hd_val : d = d' + 2 := by rw [add_comm] at hd_eq; exact hd_eq
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have h_eq : ((d' + 2) * (m' + 1)) / (d' + 2) = ((d' + 2) * (m' + 1) - 1) / (d' + 2) + 1 := by
        rw [Nat.mul_div_cancel_left (m' + 1) (by omega)]
        have h_mul : (d' + 2) * (m' + 1) = (d' + 2) * m' + (d' + 2) := by ring
        rw [h_mul]
        set Y := (d' + 2) * m' with hY
        have h_sub : Y + (d' + 2) - 1 = (d' + 1) + Y := by omega
        rw [h_sub, hY]
        rw [mul_comm]
        rw [Nat.add_mul_div_right (d' + 1) m' (by omega)]
        have h_lt : d' + 1 < d' + 2 := by omega
        rw [Nat.div_eq_of_lt h_lt]
        omega
      have hd_eq_val : d = d' + 2 := hd_val
      have h_pow_order : (2 : ZMod p) ^ (d' + 2) = 1 := by
        rw [← hd_eq_val, hd]
        exact pow_orderOf_eq_one (2 : ZMod p)
      rw [hd_eq_val]
      rw [h_eq]
      have hp_div : p ∣ 2 ^ ((d' + 2) * (m' + 1)) - 1 := by
        have h_pow : (2 : ZMod p) ^ ((d' + 2) * (m' + 1)) = 1 := by
          rw [pow_mul, h_pow_order, one_pow]
        have h_pow_nat : ((2 ^ ((d' + 2) * (m' + 1)) : ℕ) : ZMod p) = 1 := by
          have h_cast : (2 : ZMod p) ^ ((d' + 2) * (m' + 1)) = ((2 ^ ((d' + 2) * (m' + 1)) : ℕ) : ZMod p) := by norm_cast
          rwa [← h_cast]
        have h_sub_zero : ((2 ^ ((d' + 2) * (m' + 1)) - 1 : ℕ) : ZMod p) = 0 := by
          have h_ge_pos : (d' + 2) * (m' + 1) > 0 := Nat.mul_pos (by omega) (by omega)
          have h_ge : 2 ^ ((d' + 2) * (m' + 1)) ≥ 1 := by
            have : (d' + 2) * (m' + 1) ≥ 1 := h_ge_pos
            have h_pow_ge : 2 ^ ((d' + 2) * (m' + 1)) ≥ 2 ^ 1 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) this
            omega
          rw [Nat.cast_sub h_ge, Nat.cast_one, h_pow_nat, sub_self]
        exact (ZMod.natCast_eq_zero_iff (2 ^ ((d' + 2) * (m' + 1)) - 1) p).mp (by exact_mod_cast h_sub_zero)
      have h_val_pos : padicValNat p (2 ^ ((d' + 2) * (m' + 1)) - 1) ≥ 1 := by
        apply one_le_padicValNat_of_dvd
        · intro hc
          have h_ge : 2 ^ ((d' + 2) * (m' + 1)) ≥ 4 := by
            have h_eq : (d' + 2) * (m' + 1) = (d' + 2) * m' + (d' + 2) := by ring
            have : (d' + 2) * (m' + 1) ≥ 2 := by omega
            exact Nat.pow_le_pow_right (show 1 ≤ 2 by decide) this
          generalize hZ : 2 ^ ((d' + 2) * (m' + 1)) = Z at h_ge hc
          obtain ⟨Z', hd_eq'⟩ := Nat.exists_eq_add_of_le h_ge
          have rfl : Z = Z' + 4 := by rw [add_comm] at hd_eq'; exact hd_eq'
          omega
        · exact hp_div
      have h_sum_ih : ((d' + 2) * (m' + 1) - 1) / (d' + 2) ≤ ∑ x ∈ Finset.Ico 1 ((d' + 2) * (m' + 1)), padicValNat p (2 ^ x - 1) := by
        rw [← hd_eq_val]
        omega
      have h_val_pos_nonneg : padicValNat p (2 ^ ((d' + 2) * (m' + 1)) - 1) ≥ 0 := Nat.zero_le _
      linarith [h_val_pos, h_sum_ih, h_val_pos_nonneg]
    · have hd_mod : k % d ≠ 0 := by
        intro hc
        have : d ∣ k := Nat.dvd_of_mod_eq_zero hc
        contradiction
      obtain ⟨r', hr'⟩ : ∃ r', k % d = r' + 1 := Nat.exists_eq_succ_of_ne_zero hd_mod
      have h_eq : k / d = (k - 1) / d := by
        have h_add := Nat.div_add_mod k d
        rw [mul_comm] at h_add
        have h_add' : k = (k / d) * d + k % d := h_add.symm
        set X := (k / d) * d with hX
        have h_sub : k - 1 = r' + X := by
          rw [h_add', hr']
          omega
        rw [h_sub, h_add', hr']
        rw [hX]
        rw [add_comm ((k / d) * d) (r' + 1)]
        rw [Nat.add_mul_div_right (r' + 1) (k / d) hd_pos]
        rw [Nat.add_mul_div_right r' (k / d) hd_pos]
        have h_mod_lt := Nat.mod_lt k hd_pos
        have h_lt1 : r' + 1 < d := by omega
        have h_lt2 : r' < d := by omega
        rw [Nat.div_eq_of_lt h_lt1, Nat.div_eq_of_lt h_lt2]
      rw [h_eq]
      have h_sum_ih : (k - 1) / d ≤ ∑ x ∈ Finset.Ico 1 k, padicValNat p (2 ^ x - 1) := ih
      have h_val_pos_nonneg : padicValNat p (2 ^ k - 1) ≥ 0 := Nat.zero_le _
      linarith [h_sum_ih, h_val_pos_nonneg]

lemma padicValNat_prod {α : Type*} [DecidableEq α] (p : ℕ) [hp : Fact p.Prime] (s : Finset α) (f : α → ℕ) (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa_ne : f a ≠ 0 := hf _ (Finset.mem_insert_self _ _)
    have h_prod_ne : ∏ x ∈ s, f x ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro x hx
      exact hf x (Finset.mem_insert_of_mem hx)
    rw [padicValNat.mul hfa_ne h_prod_ne]
    have ih_applied : padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
      apply ih
      intro x hx
      exact hf x (Finset.mem_insert_of_mem hx)
    rw [ih_applied]

lemma padicValNat_two_factorial_le (n : ℕ) (hn : n > 2) :
    padicValNat 2 (n - 1).factorial ≤ n - 2 := by
  have h_ne : n - 1 ≠ 0 := by omega
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_lt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 2 h_ne
  have h_sub : 2 - 1 = 1 := rfl
  rw [h_sub, one_mul] at h_lt
  omega

lemma factorial_dvd_num (n : ℕ) (hn : n > 2) :
    (n - 1).factorial ∣ (2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  set Num := (2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) with hNum
  set d_fact := (n - 1).factorial with hd_fact
  have hd_ne : d_fact ≠ 0 := by rw [hd_fact]; exact factorial_ne_zero (n - 1)
  have h_num_ne : Num ≠ 0 := by
    rw [hNum]
    apply mul_ne_zero
    · exact pow_ne_zero _ (by decide)
    · apply Finset.prod_ne_zero_iff.mpr
      intro x hx
      rw [Finset.mem_Ico] at hx
      have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
      omega
  have h_le : ∀ p : ℕ, p.Prime → d_fact.factorization p ≤ Num.factorization p := by
    intro p hp_prime
    rw [Nat.factorization_def d_fact hp_prime, Nat.factorization_def Num hp_prime]
    haveI hp : Fact p.Prime := ⟨hp_prime⟩
    by_cases hp2 : p = 2
    · subst hp2
      have h2_val : padicValNat 2 d_fact ≤ n - 2 := by
        rw [hd_fact]
        exact padicValNat_two_factorial_le n hn
      have hNum_val : n - 2 ≤ padicValNat 2 Num := by
        rw [hNum]
        have h_prod_ne : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro x hx
          rw [Finset.mem_Ico] at hx
          have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
          omega
        rw [padicValNat.mul (pow_ne_zero _ (by decide)) h_prod_ne]
        have h_pow_val : padicValNat 2 (2 ^ (n - 2)) = n - 2 := by
          exact padicValNat.prime_pow (p := 2) (n - 2)
        rw [h_pow_val]
        omega
      omega
    · have hp3 : p ≥ 3 := by
        have : p ≠ 0 := hp_prime.ne_zero
        have : p ≠ 1 := hp_prime.ne_one
        omega
      have h2_ne : (2 : ZMod p) ≠ 0 := by
        intro hc
        have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc
        have hle := Nat.le_of_dvd (by decide) hdvd
        omega
      set d := orderOf (2 : ZMod p) with hd_def
      have hd_dvd : d ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2_ne
      have hd_le : d ≤ p - 1 := Nat.le_of_dvd (by omega) hd_dvd
      have hd_pos : d > 0 := by
        have h_unit : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr h2_ne
        have h_val : (h_unit.unit : ZMod p) = 2 := IsUnit.unit_spec h_unit
        have h_order : d = orderOf h_unit.unit := by
          rw [hd_def]
          have h1 : orderOf (2 : ZMod p) = orderOf (h_unit.unit : ZMod p) := by
            rw [h_val]
          rw [h1, orderOf_units]
        rw [h_order]
        exact orderOf_pos h_unit.unit
      have h_lt : (p - 1) * padicValNat p (n - 1).factorial < n - 1 := by
        have h_ne : n - 1 ≠ 0 := by omega
        exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero p h_ne
      have h_mul_le : d * padicValNat p (n - 1).factorial ≤ (p - 1) * padicValNat p (n - 1).factorial := by
        exact Nat.mul_le_mul_right (padicValNat p (n - 1).factorial) hd_le
      have h_d_mul_lt : d * padicValNat p (n - 1).factorial < n - 1 := by omega
      have h_d_mul_le : d * padicValNat p (n - 1).factorial ≤ n - 2 := by omega
      have h_fact_le : padicValNat p d_fact ≤ (n - 2) / d := by
        rw [hd_fact]
        rw [mul_comm] at h_d_mul_le
        rwa [Nat.le_div_iff_mul_le hd_pos]
      have h_induction : (n - 2) / d ≤ padicValNat p Num := by
        rw [hNum]
        have h_not_dvd : ¬ p ∣ 2 ^ (n - 2) := by
          intro hc
          have hp2 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp_prime hc
          have h_le := Nat.le_of_dvd (by decide) hp2
          omega
        have h_pow_zero : padicValNat p (2 ^ (n - 2)) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
        have h_prod_ne : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro x hx
          rw [Finset.mem_Ico] at hx
          have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
          omega
        rw [padicValNat.mul (pow_ne_zero _ (by decide)) h_prod_ne]
        rw [h_pow_zero, zero_add]
        have h_prod_val : padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = ∑ k ∈ Finset.Ico 1 (n - 1), padicValNat p (2 ^ k - 1) := by
          apply padicValNat_prod
          intro x hx
          rw [Finset.mem_Ico] at hx
          have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
          omega
        rw [h_prod_val]
        exact sum_padic_induction p hp3 d hd_def (n - 1) (by omega)
      omega
  rw [← Nat.factorization_le_iff_dvd hd_ne h_num_ne]
  intro p
  by_cases hp_prime : p.Prime
  · exact h_le p hp_prime
  · have h_zero : d_fact.factorization p = 0 := Nat.factorization_eq_zero_of_not_prime d_fact hp_prime
    rw [h_zero]
    exact Nat.zero_le _

theorem odd_prime_or_power_of_two (n : ℕ) (hn : n > 2) :
    (∃ p, p.Prime ∧ p ∣ n ∧ p ≥ 3) ∨ (∃ r, n = 2 ^ r ∧ r ≥ 2) := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨r, rfl⟩ | ⟨p, hp, hdvd, hodd⟩
  · right
    use r
    refine ⟨rfl, ?_⟩
    by_contra! h_lt
    interval_cases r
    · omega
    · omega
  · left
    use p
    refine ⟨hp, hdvd, ?_⟩
    have hp_ne_two : p ≠ 2 := by
      intro hc
      subst hc
      have : ¬ Odd 2 := by decide
      contradiction
    have hp_two_le : 2 ≤ p := hp.two_le
    omega

lemma digits_sum_two_pow_sub_one (r : ℕ) :
    (Nat.digits 2 (2 ^ r - 1)).sum = r := by
  induction r with
  | zero =>
    simp
  | succ r ih =>
    have h_ge : 2 ^ r ≥ 1 := by
      have : 2 ^ r ≥ 2 ^ 0 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) (Nat.zero_le _)
      exact this
    have h_pow : 2 ^ (r + 1) - 1 = 1 + 2 * (2 ^ r - 1) := by
      have h1 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
      rw [h1]
      set Y := 2 ^ r
      omega
    rw [h_pow]
    have h_digits : Nat.digits 2 (1 + 2 * (2 ^ r - 1)) = 1 :: Nat.digits 2 (2 ^ r - 1) := by
      apply Nat.digits_add 2 (by decide) 1 (2 ^ r - 1) (by decide) (by left; decide)
    rw [h_digits]
    simp [ih]
    omega

lemma padicValNat_two_factorial_eq_two_pow (r : ℕ) (hr : r ≥ 2) :
    padicValNat 2 (2 ^ r - 1).factorial = 2 ^ r - 1 - r := by
  have h_ne : 2 ^ r - 1 ≠ 0 := by
    have : 2 ^ r ≥ 2 ^ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hr
    omega
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_val := sub_one_mul_padicValNat_factorial (p := 2) (2 ^ r - 1)
  have h_sub : 2 - 1 = 1 := rfl
  rw [h_sub, one_mul] at h_val
  rw [h_val]
  rw [digits_sum_two_pow_sub_one r]

lemma padicVal_two_prod_eq_zero (n : ℕ) (hn : n > 2) :
    padicValNat 2 ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = 0 := by
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_prod : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro x hx
    rw [Finset.mem_Ico] at hx
    have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
    omega
  rw [padicValNat_prod 2 (Finset.Ico 1 (n - 1)) (fun k => 2 ^ k - 1)]
  · have h_zero : ∑ x ∈ Finset.Ico 1 (n - 1), padicValNat 2 (2 ^ x - 1) = ∑ x ∈ Finset.Ico 1 (n - 1), 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_Ico] at hx
      have h_odd : ¬ 2 ∣ 2 ^ x - 1 := by
        intro hc
        have h_ge : 2 ^ (x - 1) ≥ 1 := by
          have : 2 ^ (x - 1) ≥ 2 ^ 0 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) (Nat.zero_le _)
          exact this
        have : 2 ^ x - 1 = 2 * (2 ^ (x - 1) - 1) + 1 := by
          have h_pow_split : 2 ^ x = 2 * 2 ^ (x - 1) := by
            have hx_eq : x = (x - 1) + 1 := by omega
            nth_rw 1 [hx_eq]
            rw [pow_succ', mul_comm]
          rw [h_pow_split]
          set Y := 2 ^ (x - 1)
          omega
        omega
      exact padicValNat.eq_zero_of_not_dvd h_odd
    rw [h_zero, Finset.sum_const, smul_zero]
  · intro x hx
    rw [Finset.mem_Ico] at hx
    have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
    omega

theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro h
  by_cases hp : Nat.Prime n
  · refine ⟨hp, ?_⟩
    by_cases h_pr : IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)
    · exact h_pr
    · exfalso
      have h_div_num : n ∣ (2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := prime_case n hn hp h_pr
      have h_num_eq : (2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) = a (n - 1) * (n - 1).factorial := by
        have h_dvd := factorial_dvd_num n hn
        have h_eq := a_of_gt_two n hn
        rw [h_eq]
        exact (Nat.div_mul_cancel h_dvd).symm
      have h_div_mul : n ∣ a (n - 1) * (n - 1).factorial := by rwa [← h_num_eq]
      have h_coprime : n.Coprime (n - 1).factorial := hp.coprime_factorial_of_lt (by omega)
      have h_div_a : n ∣ a (n - 1) := h_coprime.dvd_of_dvd_mul_right h_div_mul
      have hdvd : n ∣ 2 ^ (n - 2) := (Nat.dvd_add_iff_right h_div_a).mpr h
      have hp2 : n ∣ 2 := hp.dvd_of_dvd_pow hdvd
      have h_le := Nat.le_of_dvd (by decide) hp2
      omega
  · exfalso
    rcases odd_prime_or_power_of_two n hn with ⟨p, hp_prime, hp_dvd_n, hp3⟩ | ⟨r, hn_eq, hr2⟩
    · haveI hp_fact : Fact p.Prime := ⟨hp_prime⟩
      have h_num_eq : (2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) = a (n - 1) * (n - 1).factorial := by
        have h_dvd := factorial_dvd_num n hn
        have h_eq := a_of_gt_two n hn
        rw [h_eq]
        exact (Nat.div_mul_cancel h_dvd).symm
      have h_val_eq : padicValNat p (a (n - 1) * (n - 1).factorial) = padicValNat p ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
        rw [← h_num_eq]
      have h_fact_ne : (n - 1).factorial ≠ 0 := factorial_ne_zero _
      have h_a_ne : a (n - 1) ≠ 0 := by
        intro hc
        have h_zero : a (n - 1) * (n - 1).factorial = 0 := by rw [hc, zero_mul]
        rw [← h_num_eq] at h_zero
        have h_num_ne : (2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
          apply mul_ne_zero
          · exact pow_ne_zero _ (by decide)
          · apply Finset.prod_ne_zero_iff.mpr
            intro x hx
            rw [Finset.mem_Ico] at hx
            have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
            omega
        exact h_num_ne h_zero
      rw [padicValNat.mul h_a_ne h_fact_ne] at h_val_eq
      have hm : ∃ m, n = m * p ∧ m ≥ 2 := by
        obtain ⟨m, hm_eq⟩ := hp_dvd_n
        use m
        have hm_eq' : n = m * p := by rw [hm_eq, mul_comm]
        refine ⟨hm_eq', ?_⟩
        by_contra! h_lt
        interval_cases m
        · rw [mul_zero] at hm_eq; omega
        · rw [mul_one] at hm_eq; subst hm_eq; contradiction
      rcases hm with ⟨m, rfl, hm2⟩
      have h_div : (m * p - 1) / p = m - 1 := by
        have h_mul : m * p - 1 = (m - 1) * p + (p - 1) := by
          have h1 : m * p = (m - 1) * p + p := by
            have : m = (m - 1) + 1 := by omega
            nth_rw 1 [this]
            ring
          omega
        rw [h_mul]
        rw [add_comm]
        rw [Nat.add_mul_div_right (p - 1) (m - 1) (by omega)]
        have : p - 1 < p := by omega
        rw [Nat.div_eq_of_lt this, zero_add]
      have h2_ne : (2 : ZMod p) ≠ 0 := by
        intro hc
        have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc
        have hle := Nat.le_of_dvd (by decide) hdvd
        omega
      set d := orderOf (2 : ZMod p) with hd_def
      have hd_dvd : d ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2_ne
      have hd_le : d ≤ p - 1 := Nat.le_of_dvd (by omega) hd_dvd
      have hd_pos : d > 0 := by
        have h_unit : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr h2_ne
        have h_val : (h_unit.unit : ZMod p) = 2 := IsUnit.unit_spec h_unit
        have h_order : d = orderOf h_unit.unit := by
          rw [hd_def]
          have h1 : orderOf (2 : ZMod p) = orderOf (h_unit.unit : ZMod p) := by
            rw [h_val]
          rw [h1, orderOf_units]
        rw [h_order]
        exact orderOf_pos h_unit.unit
      have h_lt : (p - 1) * padicValNat p (m - 1).factorial < m - 1 := by
        have : m - 1 ≠ 0 := by omega
        exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero p this
      have h_mul_le : d * padicValNat p (m - 1).factorial ≤ (p - 1) * padicValNat p (m - 1).factorial := by
        exact Nat.mul_le_mul_right (padicValNat p (m - 1).factorial) hd_le
      have h_d_mul_lt : d * padicValNat p (m - 1).factorial < m - 1 := by omega
      have h_d_mul_le : d * padicValNat p (m - 1).factorial ≤ m - 2 := by omega
      have h_d_sum_le : d * (padicValNat p (m * p - 1).factorial + 1) ≤ m * p - 2 := by
        rw [← padicValNat_mul_div_factorial (m * p - 1), h_div, padicValNat_factorial_mul (m - 1)]
        have h_expand : d * (padicValNat p (m - 1).factorial + (m - 1) + 1) = d * m + d * padicValNat p (m - 1).factorial := by
          have : padicValNat p (m - 1).factorial + (m - 1) + 1 = m + padicValNat p (m - 1).factorial := by omega
          rw [this, mul_add]
        rw [h_expand]
        have h_le1 : d * m ≤ (p - 1) * m := Nat.mul_le_mul_right m hd_le
        set X := d * m with hX
        set Y := d * padicValNat p (m - 1).factorial with hY
        set Z := (p - 1) * m with hZ
        have h_Z_val : Z + m = m * p := by
          rw [hZ]
          have h_p : p = (p - 1) + 1 := by omega
          nth_rw 2 [h_p]
          ring
        omega
      have h_fact_le : padicValNat p (m * p - 1).factorial + 1 ≤ (m * p - 2) / d := by
        rw [Nat.le_div_iff_mul_le hd_pos]
        rwa [mul_comm] at h_d_sum_le
      have h_induction : (m * p - 2) / d ≤ padicValNat p ((2 ^ (m * p - 2)) * (Finset.Ico 1 (m * p - 1)).prod (fun k => 2 ^ k - 1)) := by
        set Num := (2 ^ (m * p - 2)) * (Finset.Ico 1 (m * p - 1)).prod (fun k => 2 ^ k - 1)
        have h_not_dvd : ¬ p ∣ 2 ^ (m * p - 2) := by
          intro hc
          have hp2 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp_prime hc
          have h_le := Nat.le_of_dvd (by decide) hp2
          omega
        have h_pow_zero : padicValNat p (2 ^ (m * p - 2)) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
        have h_prod_ne : (Finset.Ico 1 (m * p - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro x hx
          rw [Finset.mem_Ico] at hx
          have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
          omega
        rw [padicValNat.mul (pow_ne_zero _ (by decide)) h_prod_ne]
        rw [h_pow_zero, zero_add]
        have h_prod_val : padicValNat p ((Finset.Ico 1 (m * p - 1)).prod (fun k => 2 ^ k - 1)) = ∑ k ∈ Finset.Ico 1 (m * p - 1), padicValNat p (2 ^ k - 1) := by
          apply padicValNat_prod
          intro x hx
          rw [Finset.mem_Ico] at hx
          have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
          omega
        rw [h_prod_val]
        exact sum_padic_induction p hp3 d hd_def (m * p - 1) (by omega)
      have h_lt_val : padicValNat p (m * p - 1).factorial < padicValNat p ((2 ^ (m * p - 2)) * (Finset.Ico 1 (m * p - 1)).prod (fun k => 2 ^ k - 1)) := by omega
      have h_a_pos : padicValNat p (a (m * p - 1)) ≥ 1 := by omega
      have h_div_p : p ∣ a (m * p - 1) := by
        have h_pos_ne_zero : padicValNat p (a (m * p - 1)) ≠ 0 := by omega
        rwa [← dvd_iff_padicValNat_ne_zero h_a_ne] at h_pos_ne_zero
      have h_div_sum : p ∣ a (m * p - 1) + 2 ^ (m * p - 2) := dvd_trans hp_dvd_n h
      have h_div_pow : p ∣ 2 ^ (m * p - 2) := (Nat.dvd_add_iff_right h_div_p).mpr h_div_sum
      have hp2 : p ∣ 2 := hp_prime.dvd_of_dvd_pow h_div_pow
      have hle := Nat.le_of_dvd (by decide) hp2
      omega
    · subst hn_eq
      have h_ge : 2 ^ r ≥ r + 2 := by
        clear hp hn h
        induction r, hr2 using Nat.le_induction with
        | base => decide
        | succ k hk ih =>
          have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
          rw [this]
          omega
      have h_num_eq : (2 ^ (2 ^ r - 2)) * (Finset.Ico 1 (2 ^ r - 1)).prod (fun k => 2 ^ k - 1) = a (2 ^ r - 1) * (2 ^ r - 1).factorial := by
        have h_dvd := factorial_dvd_num (2 ^ r) hn
        have h_eq := a_of_gt_two (2 ^ r) hn
        rw [h_eq]
        exact (Nat.div_mul_cancel h_dvd).symm
      have h_num_val : padicValNat 2 ((2 ^ (2 ^ r - 2)) * (Finset.Ico 1 (2 ^ r - 1)).prod (fun k => 2 ^ k - 1)) = 2 ^ r - 2 := by
        have h_prod_ne : (Finset.Ico 1 (2 ^ r - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro x hx
          rw [Finset.mem_Ico] at hx
          have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
          omega
        have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [padicValNat.mul (pow_ne_zero _ (by decide)) h_prod_ne]
        rw [padicValNat.prime_pow (p := 2) (2 ^ r - 2)]
        rw [padicVal_two_prod_eq_zero (2 ^ r) hn]
        omega
      have h_fact_val : padicValNat 2 (2 ^ r - 1).factorial = 2 ^ r - 1 - r := padicValNat_two_factorial_eq_two_pow r hr2
      have h_val_eq : padicValNat 2 (a (2 ^ r - 1) * (2 ^ r - 1).factorial) = 2 ^ r - 2 := by
        rw [← h_num_eq, h_num_val]
      have h_a_ne : a (2 ^ r - 1) ≠ 0 := by
        intro hc
        have h_zero : a (2 ^ r - 1) * (2 ^ r - 1).factorial = 0 := by rw [hc, zero_mul]
        rw [← h_num_eq] at h_zero
        have h_num_ne : (2 ^ (2 ^ r - 2)) * (Finset.Ico 1 (2 ^ r - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
          apply mul_ne_zero
          · exact pow_ne_zero _ (by decide)
          · apply Finset.prod_ne_zero_iff.mpr
            intro x hx
            rw [Finset.mem_Ico] at hx
            have : 2 ^ x ≥ 2 := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hx.1
            omega
        exact h_num_ne h_zero
      have h_fact_ne : (2 ^ r - 1).factorial ≠ 0 := factorial_ne_zero _
      have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [padicValNat.mul h_a_ne h_fact_ne] at h_val_eq
      have h_a_val : padicValNat 2 (a (2 ^ r - 1)) = r - 1 := by omega
      have hdvd_a : 2 ^ (r - 1) ∣ a (2 ^ r - 1) := by
        have h_pow_dvd : 2 ^ padicValNat 2 (a (2 ^ r - 1)) ∣ a (2 ^ r - 1) := pow_padicValNat_dvd
        rw [h_a_val] at h_pow_dvd
        exact h_pow_dvd
      obtain ⟨u, hu_eq⟩ := hdvd_a
      have h_u_odd : ¬ 2 ∣ u := by
        intro hc
        obtain ⟨v, rfl⟩ := hc
        have hu_eq_val : a (2 ^ r - 1) = 2 ^ r * v := by
          rw [hu_eq]
          have : 2 ^ (r - 1) * (2 * v) = 2 ^ r * v := by
            have : 2 ^ r = 2 ^ (r - 1) * 2 := by
              have : r = (r - 1) + 1 := by omega
              nth_rw 1 [this]
              exact pow_succ 2 (r - 1)
            rw [this]
            ring
          rw [this]
        have h_a_val2 : padicValNat 2 (a (2 ^ r - 1)) = padicValNat 2 (2 ^ r * v) := by rw [hu_eq_val]
        have h_v_ne : v ≠ 0 := by
          intro hc_v
          subst hc_v
          rw [mul_zero] at hu_eq_val
          exact h_a_ne hu_eq_val
        rw [padicValNat.mul (pow_ne_zero _ (by decide)) h_v_ne, padicValNat.prime_pow (p := 2) r] at h_a_val2
        omega
      have h_div_n : 2 ^ r ∣ a (2 ^ r - 1) + 2 ^ (2 ^ r - 2) := h
      have h_pow_split : 2 ^ (2 ^ r - 2) = 2 ^ (r - 1) * 2 ^ (2 ^ r - r - 1) := by
        have : 2 ^ r - 2 = (r - 1) + (2 ^ r - r - 1) := by
          have h_ge : 2 ^ r ≥ r + 2 := by
            induction r, hr2 using Nat.le_induction with
            | base => decide
            | succ k hk ih =>
              have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
              rw [this]
              omega
          omega
        rw [this, pow_add]
      have h_sum_eq : a (2 ^ r - 1) + 2 ^ (2 ^ r - 2) = 2 ^ (r - 1) * (u + 2 ^ (2 ^ r - r - 1)) := by
        rw [hu_eq, h_pow_split]
        ring
      rw [h_sum_eq] at h_div_n
      have hk_pos : 2 ^ r - r - 1 ≥ 1 := by
        have : 2 ^ r ≥ r + 2 := by
          induction r, hr2 using Nat.le_induction with
          | base => decide
          | succ k hk ih =>
            have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
            rw [this]
            omega
        omega
      have h_pow_split2 : 2 ^ (2 ^ r - r - 1) = 2 * 2 ^ (2 ^ r - r - 2) := by
        have : 2 ^ r - r - 1 = (2 ^ r - r - 2) + 1 := by omega
        nth_rw 1 [this]
        rw [pow_succ, mul_comm]
      have h_div_cancel : 2 ∣ u + 2 ^ (2 ^ r - r - 1) := by
        have h_div_all : 2 ^ r ∣ 2 ^ (r - 1) * (u + 2 ^ (2 ^ r - r - 1)) := h_div_n
        have h_cancel : 2 ^ r = 2 ^ (r - 1) * 2 := by
          have : r = (r - 1) + 1 := by omega
          nth_rw 1 [this]
          exact pow_succ 2 (r - 1)
        nth_rw 1 [h_cancel] at h_div_all
        exact (mul_dvd_mul_iff_left (by positivity)).mp h_div_all
      rw [h_pow_split2] at h_div_cancel
      have h_div_u : 2 ∣ u := by
        have : u = (u + 2 * 2 ^ (2 ^ r - r - 2)) - 2 * 2 ^ (2 ^ r - r - 2) := by omega
        nth_rw 1 [this]
        apply dvd_sub h_div_cancel
        exact dvd_mul_of_dvd_left (by decide) _
      contradiction
