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

lemma geom_sum_identity (x p : ℕ) :
  (x - 1) * (Finset.range p).sum (fun i => x ^ i) = x ^ p - 1 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ]
    rw [mul_add, ih]
    by_cases hx : x = 0
    · subst hx
      cases p <;> simp
    · have h_x1 : x ≥ 1 := by omega
      have h_xp1 : x ^ p ≥ 1 := Nat.one_le_pow p x h_x1
      have h_x_succ : x ^ p ≤ x ^ (p + 1) := by
        rw [pow_succ]
        have : x ^ p * 1 ≤ x ^ p * x := Nat.mul_le_mul_left (x ^ p) h_x1
        rw [mul_one] at this
        exact this
      have h_mul : (x - 1) * x ^ p = x ^ (p + 1) - x ^ p := by
        rw [Nat.sub_mul]
        simp only [one_mul]
        rw [pow_succ']
      omega

lemma pow_modeq_one (x : ℕ) (p k : ℕ) (h_mod : x ≡ 1 [MOD p]) :
  x ^ k ≡ 1 [MOD p] := by
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
    rw [pow_succ]
    have : x ^ k * x ≡ 1 * 1 [MOD p] := Nat.ModEq.mul ih h_mod
    exact this

lemma geom_sum_modeq (x : ℕ) (p k : ℕ) (h_mod : x ≡ 1 [MOD p]) :
  (Finset.range k).sum (fun i => x ^ i) ≡ k [MOD p] := by
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hx_pow : x ^ k ≡ 1 [MOD p] := pow_modeq_one x p k h_mod
    exact Nat.ModEq.add ih hx_pow

lemma prime_sq_dvd_pow_sub_one (p o : ℕ) (pp : p.Prime) (ho : (2 : ZMod p) ^ o = 1) :
  p ^ 2 ∣ (2 ^ o) ^ p - 1 := by
  have h_cast : ((2 ^ o : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_pow, Nat.cast_two, Nat.cast_one]
    exact ho
  have h_mod : 2 ^ o ≡ 1 [MOD p] := by
    rwa [ZMod.natCast_eq_natCast_iff' (2 ^ o) 1 p] at h_cast
  have hp_dvd_x : p ∣ 2 ^ o - 1 := by
    have h_eq : 2 ^ o = p * (2 ^ o / p) + 2 ^ o % p := (Nat.div_add_mod (2 ^ o) p).symm
    have h_mod_val : 2 ^ o % p = 1 := by
      have h_mod_val' : 2 ^ o % p = 1 % p := h_mod
      have h1p : 1 % p = 1 := by
        apply Nat.mod_eq_of_lt
        have : p > 1 := pp.one_lt
        omega
      rwa [h1p] at h_mod_val'
    have h_sub : 2 ^ o - 1 = p * (2 ^ o / p) := by omega
    rw [h_sub]
    exact dvd_mul_right p (2 ^ o / p)
  have h_sum_mod : (Finset.range p).sum (fun i => (2 ^ o) ^ i) ≡ 0 [MOD p] := by
    have h_modeq : (Finset.range p).sum (fun i => (2 ^ o) ^ i) ≡ p [MOD p] := geom_sum_modeq (2 ^ o) p p h_mod
    have hp_zero : p ≡ 0 [MOD p] := by
      rw [Nat.ModEq]
      simp
    exact Nat.ModEq.trans h_modeq hp_zero
  have hp_dvd_sum : p ∣ (Finset.range p).sum (fun i => (2 ^ o) ^ i) := by
    rw [Nat.ModEq] at h_sum_mod
    simp only [Nat.zero_mod] at h_sum_mod
    exact Nat.dvd_of_mod_eq_zero h_sum_mod
  have h_dvd_mul : p * p ∣ (2 ^ o - 1) * (Finset.range p).sum (fun i => (2 ^ o) ^ i) := by
    exact mul_dvd_mul hp_dvd_x hp_dvd_sum
  have h_identity : (2 ^ o - 1) * (Finset.range p).sum (fun i => (2 ^ o) ^ i) = (2 ^ o) ^ p - 1 := by
    exact geom_sum_identity (2 ^ o) p
  rw [h_identity] at h_dvd_mul
  have h_sq : p ^ 2 = p * p := by ring
  rwa [h_sq]

lemma sum_padicVal_strict_ge_div_order_helper (p op : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) (hop : op = orderOf (2 : ZMod p) * p) (k : ℕ) :
  (Finset.Ico 1 (op + 1 + k)).sum (fun m => padicValNat p (2 ^ m - 1)) ≥ (op + k) / orderOf (2 : ZMod p) + 1 := by
  generalize ho : orderOf (2 : ZMod p) = o at hop ⊢
  have ho_ge_2 : o ≥ 2 := by
    rw [← ho]
    exact order_ge_two p pp hp2
  have ho_pos : o > 0 := by omega
  have h_op_ge_1 : op ≥ 1 := by
    subst hop
    have h_p_pos : p > 0 := by
      have : p > 1 := pp.one_lt
      omega
    have h_mul_pos := Nat.mul_pos ho_pos h_p_pos
    omega
  induction k with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero]
    have h_sum_base : (Finset.Ico 1 op).sum (fun m => padicValNat p (2 ^ m - 1)) ≥ (op - 1) / o := by
      have h_sum := sum_padicVal_ge_div_order p op pp hp2
      rw [ho] at h_sum
      exact h_sum
    have h_prod : o * p = o * (p - 1) + o := by
      have : p = (p - 1) + 1 := by
        clear hop h_sum_base
        have : p > 1 := pp.one_lt
        omega
      nth_rw 1 [this]
      rw [mul_add, mul_one]
    have h_op_sub : op - 1 = o * (p - 1) + (o - 1) := by
      rw [hop, h_prod]
      have h_sub_rule : ∀ A, A + o - 1 = A + (o - 1) := by
        intro A
        clear hop
        omega
      exact h_sub_rule (o * (p - 1))
    have h_div : (op - 1) / o = p - 1 := by
      rw [h_op_sub]
      rw [add_comm, Nat.add_mul_div_left _ _ ho_pos]
      have : (o - 1) / o = 0 := Nat.div_eq_of_lt (by omega)
      rw [this, zero_add]
    rw [h_div] at h_sum_base
    have h_sq_dvd : p ^ 2 ∣ 2 ^ op - 1 := by
      rw [hop, pow_mul]
      have ho_eq : (2 : ZMod p) ^ o = 1 := by
        have h_pow := pow_orderOf_eq_one (2 : ZMod p)
        rw [ho] at h_pow
        exact h_pow
      exact prime_sq_dvd_pow_sub_one p o pp ho_eq
    have h_non_zero : 2 ^ op - 1 ≠ 0 := by
      have : 2 ^ 1 ≤ 2 ^ op := Nat.pow_le_pow_right (by decide) h_op_ge_1
      clear hop
      omega
    have h_padic_ge : padicValNat p (2 ^ op - 1) ≥ 2 := by
      haveI : Fact p.Prime := ⟨pp⟩
      exact (padicValNat_dvd_iff_le h_non_zero).mp h_sq_dvd
    have h_div_op : op / o = p - 1 + 1 := by
      rw [div_lemma_dvd op o ho_ge_2 h_op_ge_1 (by
        rw [hop]
        exact dvd_mul_right o p)]
      rw [h_div]
    have h_ico_eq : op + 1 + 0 = op + 1 := by
      clear hop
      omega
    rw [h_ico_eq, Finset.sum_Ico_succ_top h_op_ge_1]
    rw [add_zero]
    rw [h_div_op]
    clear hop
    omega
  | succ k ih =>
    have hd1 : op + 1 + k ≥ 1 := by
      clear hop ih
      omega
    have h_ico_eq : op + 1 + (k + 1) = (op + 1 + k) + 1 := by
      clear hop ih
      omega
    rw [h_ico_eq, Finset.sum_Ico_succ_top hd1]
    have h_eq_add : op + (k + 1) = op + 1 + k := by
      clear hop ih
      omega
    have h_target : (op + (k + 1)) / o = (op + 1 + k) / o := by rw [h_eq_add]
    have h_eq_add2 : op + 1 + k - 1 = op + k := by
      clear hop ih
      omega
    have h_target2 : (op + 1 + k - 1) / o = (op + k) / o := by rw [h_eq_add2]
    by_cases h_dvd : o ∣ op + 1 + k
    · rw [h_target]
      rw [div_lemma_dvd (op + 1 + k) o ho_ge_2 (by clear hop ih; omega) h_dvd]
      rw [h_target2]
      have hp_dvd : p ∣ 2 ^ (op + 1 + k) - 1 := by
        have h_pow : (2 : ZMod p) ^ (op + 1 + k) = 1 := by
          rcases h_dvd with ⟨m, hm⟩
          rw [hm, pow_mul]
          have : (2 : ZMod p) ^ o = 1 := by
            rw [← ho]
            exact pow_orderOf_eq_one (2 : ZMod p)
          rw [this, one_pow]
        have h_cast : ((2 ^ (op + 1 + k) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          rw [Nat.cast_pow, Nat.cast_two, Nat.cast_one]
          exact h_pow
        rw [ZMod.natCast_eq_natCast_iff' (2 ^ (op + 1 + k)) 1 p] at h_cast
        have h1p : 1 % p = 1 := by
          apply Nat.mod_eq_of_lt
          have : p > 1 := pp.one_lt
          clear hop ih
          omega
        rw [h1p] at h_cast
        have h_div_mod := Nat.div_add_mod (2 ^ (op + 1 + k)) p
        have : 2 ^ (op + 1 + k) - 1 = p * (2 ^ (op + 1 + k) / p) := by
          clear hop ih
          omega
        rw [this]
        exact dvd_mul_right p (2 ^ (op + 1 + k) / p)
      have h_non_zero : 2 ^ (op + 1 + k) - 1 ≠ 0 := by
        have : 2 ^ 1 ≤ 2 ^ (op + 1 + k) := Nat.pow_le_pow_right (show 2 > 0 by decide) hd1
        clear hop ih
        omega
      haveI : Fact p.Prime := ⟨pp⟩
      have h_padic_ge : padicValNat p (2 ^ (op + 1 + k) - 1) ≥ 1 :=
        one_le_padicValNat_of_dvd h_non_zero hp_dvd
      clear hop hd1 h_target h_target2 hp_dvd h_non_zero
      omega
    · rw [h_target]
      rw [div_lemma_not_dvd (op + 1 + k) o ho_ge_2 (by clear hop ih; omega) h_dvd]
      rw [h_target2]
      clear hop hd1 h_target h_target2
      omega

lemma sum_padicVal_strict_ge_div_order (p d : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) (h_op : orderOf (2 : ZMod p) * p ≤ d - 1) :
  (Finset.Ico 1 d).sum (fun k => padicValNat p (2 ^ k - 1)) ≥ (d - 1) / orderOf (2 : ZMod p) + 1 := by
  have hd_pos : d ≥ 1 := by
    have hp_ge_3 : p ≥ 3 := by
      have : p > 1 := pp.one_lt
      omega
    have ho_ge_2 := order_ge_two p pp hp2
    have h_mul_ge : orderOf (2 : ZMod p) * p ≥ 6 := by
      nlinarith
    omega
  generalize ho : orderOf (2 : ZMod p) = o at h_op ⊢
  generalize h_op_val : o * p = op at h_op ⊢
  have h_op_le : op ≤ d - 1 := h_op
  have h_k : d - 1 - op ≥ 0 := Nat.zero_le _
  let k := d - 1 - op
  have h_eq : op + k = d - 1 := by
    dsimp [k]
    clear h_op_val ho pp hp2
    omega
  have h_ico : op + 1 + k = d := by
    dsimp [k]
    clear h_op_val ho pp hp2
    omega
  have h_op_eq : op = orderOf (2 : ZMod p) * p := by
    rw [← h_op_val, ho]
  have h_helper := sum_padicVal_strict_ge_div_order_helper p op pp hp2 h_op_eq k
  rw [h_ico] at h_helper
  rw [h_eq] at h_helper
  rw [ho] at h_helper
  exact h_helper

lemma a_exact_divisibility (n : ℕ) (hn : n > 2) :
  (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  have hd0 : n - 1 ≠ 0 := by omega
  have h_fact_ne : (n - 1).factorial ≠ 0 := factorial_ne_zero (n - 1)
  have h_rhs_ne := rhs_ne_zero n hn
  apply dvd_of_padicValNat_le h_fact_ne h_rhs_ne
  intro p pp
  rcases eq_or_ne p 2 with rfl | hp2
  · exact case_p_two n hn
  · have : Fact p.Prime := ⟨pp⟩
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
  have h_sub : (n - 1).pred = n - 2 := by
    change (n - 1) - 1 = n - 2
    omega
  unfold a
  split_ifs with h_zero
  · exfalso
    exact hd0 h_zero
  · dsimp only
    rw [h_sub]
    have h_div : (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) :=
      a_exact_divisibility n hn
    have h_fact_ne : (n - 1).factorial ≠ 0 := factorial_ne_zero (n - 1)
    exact Nat.div_mul_cancel h_div


lemma sum_sub_distrib_nat {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → ℕ) (h : ∀ x ∈ s, g x ≤ f x) :
  ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x := by
  induction s using Finset.induction with
  | empty => simp
  | insert hx s_1 hx_not_mem ih =>
    rw [Finset.sum_insert hx_not_mem, Finset.sum_insert hx_not_mem, Finset.sum_insert hx_not_mem]
    have h_g_le_f : g hx ≤ f hx := h hx (Finset.mem_insert_self hx s_1)
    have h_le_s : ∀ x ∈ s_1, g x ≤ f x := by
      intro x hx'
      exact h x (Finset.mem_insert_of_mem hx')
    have h_sum_le : ∑ x ∈ s_1, g x ≤ ∑ x ∈ s_1, f x := Finset.sum_le_sum h_le_s
    rw [ih h_le_s]
    omega

lemma two_pow_ge_succ (k : ℕ) : 2 ^ k ≥ k + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    omega

lemma sum_pow_two_ico (k : ℕ) :
  (Finset.Ico 1 k).sum (fun i => 2 ^ (k - i)) = 2 ^ k - 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · have hk1 : k ≥ 1 := by omega
      rw [Finset.sum_Ico_succ_top hk1]
      have h_top : 2 ^ (k + 1 - k) = 2 := by
        have : k + 1 - k = 1 := by omega
        rw [this]
        rfl
      rw [h_top]
      have h_step : ∑ i ∈ Finset.Ico 1 k, 2 ^ (k + 1 - i) = ∑ i ∈ Finset.Ico 1 k, 2 * 2 ^ (k - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Ico] at hi
        have : k + 1 - i = k - i + 1 := by omega
        rw [this, pow_succ']
      rw [h_step, ← Finset.mul_sum]
      rw [ih]
      have : 2 ^ k ≥ 2 := by
        have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
        omega
      omega

lemma padicValNat_two_factorial_power (k : ℕ) (hk : k ≥ 2) :
  padicValNat 2 (2 ^ k - 1).factorial = 2 ^ k - k - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_log : Nat.log 2 (2 ^ k - 1) < k := by
    rw [Nat.log_lt_iff_lt_pow (by decide)]
    · have h_ge : 2 ^ k ≥ 3 := by
        have := two_pow_ge_succ k
        omega
      generalize ht : 2 ^ k = tk at h_ge ⊢
      omega
    · have h_ge : 2 ^ k ≥ 3 := by
        have := two_pow_ge_succ k
        omega
      generalize ht : 2 ^ k = tk at h_ge ⊢
      omega
  rw [padicValNat_factorial h_log]
  have h_term : ∀ i ∈ Finset.Ico 1 k, (2 ^ k - 1) / 2 ^ i = 2 ^ (k - i) - 1 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h_pow_eq : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
      rw [← pow_add]
      congr 1
      omega
    have h_sub : 2 ^ k - 1 = (2 ^ (k - i) - 1) * 2 ^ i + (2 ^ i - 1) := by
      rw [h_pow_eq]
      have h1 : (2 ^ (k - i) - 1) * 2 ^ i = 2 ^ (k - i) * 2 ^ i - 2 ^ i := by
        rw [Nat.sub_mul, one_mul]
      rw [h1]
      have h2 : 2 ^ i ≥ 1 := by
        have : 2 ^ 1 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi.1
        omega
      have h3 : 2 ^ (k - i) * 2 ^ i ≥ 2 ^ i := by
        have : 2 ^ (k - i) ≥ 1 := by
          have : k - i ≥ 1 := by omega
          have : 2 ^ 1 ≤ 2 ^ (k - i) := Nat.pow_le_pow_right (by decide) this
          omega
        nlinarith
      omega
    rw [h_sub]
    have h_comm : (2 ^ (k - i) - 1) * 2 ^ i + (2 ^ i - 1) = (2 ^ i - 1) + (2 ^ (k - i) - 1) * 2 ^ i := by omega
    rw [h_comm]
    rw [Nat.add_mul_div_right]
    · have : (2 ^ i - 1) / 2 ^ i = 0 := by
        apply Nat.div_eq_of_lt
        have : 2 ^ i ≥ 2 := by
          have : 2 ^ 1 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi.1
          omega
        generalize ht : 2 ^ i = ti
        omega
      rw [this, zero_add]
    · have : 2 ^ 1 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi.1
      omega
  have h_sum_eq : ∑ i ∈ Finset.Ico 1 k, (2 ^ k - 1) / 2 ^ i = ∑ i ∈ Finset.Ico 1 k, (2 ^ (k - i) - 1) := by
    apply Finset.sum_congr rfl
    exact h_term
  rw [h_sum_eq]
  have h_le_all : ∀ i ∈ Finset.Ico 1 k, 1 ≤ 2 ^ (k - i) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have : k - i ≥ 1 := by omega
    have : 2 ^ 1 ≤ 2 ^ (k - i) := Nat.pow_le_pow_right (by decide) this
    omega
  rw [sum_sub_distrib_nat (Finset.Ico 1 k) (fun i => 2 ^ (k - i)) (fun i => 1) h_le_all]
  rw [sum_pow_two_ico k]
  have h_sum2 : ∑ i ∈ Finset.Ico 1 k, 1 = k - 1 := by
    rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  rw [h_sum2]
  have : 2 ^ k ≥ k + 1 := two_pow_ge_succ k
  omega

lemma padicValNat_factorial_le_m_sub_one (p m : ℕ) (pp : p.Prime) (hp2 : p ≠ 2) (hm : m ≥ 2) (hpm : p > m) :
  padicValNat p (p * m - 1).factorial ≤ m - 1 := by
  haveI : Fact p.Prime := ⟨pp⟩
  have hp_ge_3 : p ≥ 3 := by
    have : p > 1 := pp.one_lt
    omega
  have hp_gt_1 : 1 < p := pp.one_lt
  have h_mul_ge : p * m ≥ 6 := by nlinarith
  have h_num_ne_zero : p * m - 1 ≠ 0 := by
    generalize hp_mul : p * m = pm
    omega
  have h_log : Nat.log p (p * m - 1) < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp_gt_1 h_num_ne_zero]
    calc p * m - 1 < p * m := by
          generalize hp_mul : p * m = pm
          omega
    _ ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
    _ = p ^ 2 - p := by
      rw [pow_two]
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
    _ < p ^ 2 := by
      have hp_pos : p > 0 := by omega
      have hp2_ge : p * p ≥ 9 := by nlinarith
      rw [pow_two]
      generalize hp_sq : p * p = p2 at hp2_ge ⊢
      clear h_mul_ge h_num_ne_zero hm hpm
      omega
  rw [padicValNat_factorial h_log]
  have h_ico : Finset.Ico 1 2 = {1} := rfl
  rw [h_ico]
  simp
  have h_lt : (p * m - 1) / p < m := by
    rw [Nat.div_lt_iff_lt_mul (by clear h_log h_num_ne_zero; omega)]
    rw [mul_comm]
    have h_pm_pos : m * p > 0 := by
      rw [mul_comm] at h_mul_ge
      generalize hp_mul : m * p = pm at h_mul_ge ⊢
      clear h_log h_num_ne_zero hm hpm hp_ge_3 hp_gt_1 pp hp2
      omega
    exact Nat.sub_lt_self (by decide) h_pm_pos
  omega

lemma exists_odd_prime_factor_or_power_of_two (n : ℕ) (hn : n > 1) :
  (∃ k, n = 2 ^ k) ∨ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases eq_or_ne n 2 with rfl | hn2
    · left; use 1; rfl
    · by_cases h_even : 2 ∣ n
      · rcases h_even with ⟨m, rfl⟩
        have hm : m > 1 := by omega
        rcases ih m (by omega) hm with ⟨k, rfl⟩ | ⟨p, hp_prime, hp_ne2, hp_dvd⟩
        · left; use k + 1; ring
        · right; use p; exact ⟨hp_prime, hp_ne2, dvd_mul_of_dvd_right hp_dvd 2⟩
      · have ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
        right; use p
        refine ⟨hp_prime, ?_, hp_dvd⟩
        intro hc
        subst hc
        exact h_even hp_dvd


lemma k_le_two_pow_sub_two (k : ℕ) (hk : k ≥ 2) : k ≤ 2 ^ k - 2 := by
  induction k, hk using Nat.le_induction with
  | base =>
    decide
  | succ k hk ih =>
    rw [pow_succ]
    omega

lemma prime_of_dvd (n : ℕ) (hn : n > 2) (h_dvd : n ∣ (a (n - 1) + 2 ^ (n - 2))) :
  Nat.Prime n := by
  by_contra hnp
  have hn1 : n > 1 := by omega
  rcases exists_odd_prime_factor_or_power_of_two n hn1 with ⟨k, rfl⟩ | ⟨p, pp, hp2, hp_dvd_n⟩
  · have hk : k ≥ 2 := by
      by_contra hc
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · simp at hn
      · simp at hn
    have h_exact := a_exact (2 ^ k) hn
    have h_padic_eq : padicValNat 2 (a (2 ^ k - 1) * (2 ^ k - 1).factorial) =
        padicValNat 2 (2 ^ (2 ^ k - 2) * (Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) := by
      rw [h_exact]
    have h_rhs_eq : padicValNat 2 (2 ^ (2 ^ k - 2) * (Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) = 2 ^ k - 2 := by
      have h_mul : padicValNat 2 (2 ^ (2 ^ k - 2) * (Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) =
          padicValNat 2 (2 ^ (2 ^ k - 2)) + padicValNat 2 ((Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) := by
        apply padicValNat.mul
        · positivity
        · apply Finset.prod_ne_zero_iff.mpr
          intro m hm
          rw [Finset.mem_Ico] at hm
          have hm1 : m ≥ 1 := hm.1
          have h2m : 2 ^ m ≥ 2 := by
            have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm1
            exact this
          omega
      rw [h_mul]
      have h_pow : padicValNat 2 (2 ^ (2 ^ k - 2)) = 2 ^ k - 2 := padicValNat.prime_pow (2 ^ k - 2)
      have h_prod_padic : padicValNat 2 ((Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro h_dvd_odd
        have hp_two_prime : Nat.Prime 2 := Nat.prime_two
        have hp_prime_algebraic : _root_.Prime 2 := Nat.Prime.prime hp_two_prime
        rw [Prime.dvd_finset_prod_iff hp_prime_algebraic] at h_dvd_odd
        have ⟨m, hm_ico, hm_dvd⟩ := h_dvd_odd
        rw [Finset.mem_Ico] at hm_ico
        have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
        have h_sub_dvd : 2 ∣ 2 ^ m - (2 ^ m - 1) := Nat.dvd_sub this hm_dvd
        have h_diff : 2 ^ m - (2 ^ m - 1) = 1 := by
          have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm_ico.1
          omega
        rw [h_diff] at h_sub_dvd
        contradiction
      rw [h_pow, h_prod_padic, add_zero]
    have h_lhs_eq : padicValNat 2 (a (2 ^ k - 1) * (2 ^ k - 1).factorial) =
        padicValNat 2 (a (2 ^ k - 1)) + padicValNat 2 (2 ^ k - 1).factorial := by
      apply padicValNat.mul
      · intro hc
        have h_rhs_ne := rhs_ne_zero (2 ^ k) hn
        rw [hc, zero_mul] at h_exact
        exact h_rhs_ne h_exact.symm
      · exact factorial_ne_zero (2 ^ k - 1)
    rw [h_lhs_eq, h_rhs_eq] at h_padic_eq
    rw [padicValNat_two_factorial_power k hk] at h_padic_eq
    have h_padic_a : padicValNat 2 (a (2 ^ k - 1)) = k - 1 := by
      have h_tk_ge_k : 2 ^ k ≥ k + 1 := two_pow_ge_succ k
      have h_ge : 2 ^ k ≥ 3 := by omega
      generalize ht : 2 ^ k = tk at h_ge h_padic_eq h_tk_ge_k ⊢
      omega
    have hp_dvd_sum : 2 ^ k ∣ a (2 ^ k - 1) + 2 ^ (2 ^ k - 2) := h_dvd
    have h_pow_le : k ≤ 2 ^ k - 2 := k_le_two_pow_sub_two k hk
    have hp_two_dvd_a : 2 ^ k ∣ a (2 ^ k - 1) := by
      have h_div_pow : 2 ^ k ∣ 2 ^ (2 ^ k - 2) := by
        use 2 ^ (2 ^ k - 2 - k)
        rw [← pow_add]
        congr 1
        omega
      have h_sub : a (2 ^ k - 1) = (a (2 ^ k - 1) + 2 ^ (2 ^ k - 2)) - 2 ^ (2 ^ k - 2) := by omega
      rw [h_sub]
      exact Nat.dvd_sub hp_dvd_sum h_div_pow
    have h_val_a_ge : padicValNat 2 (a (2 ^ k - 1)) ≥ k := by
      have h_ne : a (2 ^ k - 1) ≠ 0 := by
        intro hc
        have h_rhs_ne := rhs_ne_zero (2 ^ k) hn
        rw [hc, zero_mul] at h_exact
        exact h_rhs_ne h_exact.symm
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (padicValNat_dvd_iff_le h_ne).mp hp_two_dvd_a
    omega
  · haveI : Fact p.Prime := ⟨pp⟩
    have hp_dvd_sum : p ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans hp_dvd_n h_dvd
    have h_exact := a_exact n hn
    have hp_not_dvd_a : ¬ p ∣ a (n - 1) := by
      intro hc
      have h_sub : 2 ^ (n - 2) = a (n - 1) + 2 ^ (n - 2) - a (n - 1) := by
        generalize ha : a (n - 1) = X
        generalize h_pow : 2 ^ (n - 2) = Y
        omega
      have h_div_pow2 : p ∣ a (n - 1) + 2 ^ (n - 2) - a (n - 1) := Nat.dvd_sub hp_dvd_sum hc
      rw [← h_sub] at h_div_pow2
      rw [(_root_.Prime.dvd_pow_iff_dvd (Nat.Prime.prime pp)) (by omega)] at h_div_pow2
      · exact hp2 (by
          have h_p_dvd_2 : p ∣ 2 := h_div_pow2
          have : p ≤ 2 := Nat.le_of_dvd (by decide) h_p_dvd_2
          have : p > 1 := pp.one_lt
          omega)
    have hp_padic_a : padicValNat p (a (n - 1)) = 0 := padicValNat.eq_zero_of_not_dvd hp_not_dvd_a
    have h_padic_eq : padicValNat p (a (n - 1) * (n - 1).factorial) =
        padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
      rw [h_exact]
    have h_rhs_eq : padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) =
        ∑ k ∈ Finset.Ico 1 (n - 1), padicValNat p (2 ^ k - 1) := by
      have h_mul : padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) =
          padicValNat p (2 ^ (n - 2)) + padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
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
      have h_pow : padicValNat p (2 ^ (n - 2)) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hc
        haveI : Fact p.Prime := ⟨pp⟩
        rw [(_root_.Prime.dvd_pow_iff_dvd (Nat.Prime.prime pp)) (by omega)] at hc
        · exact hp2 (by
            have : p ∣ 2 := hc
            have : p ≤ 2 := Nat.le_of_dvd (by decide) this
            have : p > 1 := pp.one_lt
            omega)
      rw [h_pow, zero_add]
      rw [padicValNat_prod_apply pp]
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : k ≥ 1 := hk.1
      have h2k : 2 ^ k ≥ 2 := by
        have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
        exact this
      omega
    have h_lhs_eq : padicValNat p (a (n - 1) * (n - 1).factorial) =
        padicValNat p (a (n - 1)) + padicValNat p (n - 1).factorial := by
      apply padicValNat.mul
      · intro hc
        have h_rhs_ne := rhs_ne_zero n hn
        rw [hc, zero_mul] at h_exact
        exact h_rhs_ne h_exact.symm
      · exact factorial_ne_zero (n - 1)
    rw [h_lhs_eq, hp_padic_a, zero_add] at h_padic_eq
    rcases hp_dvd_n with ⟨m, rfl⟩
    have hm : m ≥ 2 := by
      cases m
      · exfalso; omega
      · case succ m' =>
        cases m'
        · exfalso
          rw [Nat.mul_one] at hnp
          exact hnp pp
        · omega
    by_cases h_cases : p ≤ m
    · have h_ord_le := order_le_p_sub_one p pp hp2
      have h_mul_le : orderOf (2 : ZMod p) * p ≤ (p - 1) * p := Nat.mul_le_mul_right p h_ord_le
      have h_ineq : orderOf (2 : ZMod p) * p ≤ p * m - 2 := by
        have hp_ge_3 : p ≥ 3 := by
          have : p > 1 := pp.one_lt
          omega
        have h_prod : (p - 1) * p = p * p - p := by
          rw [Nat.sub_mul, one_mul, mul_comm]
        have h_sub_le : p * p - p ≤ p * m - 2 := by
          have : p * p ≤ p * m := Nat.mul_le_mul_left p h_cases
          omega
        omega
      have h_sum_ge := sum_padicVal_strict_ge_div_order p (p * m - 1) pp hp2 (by
        have h_sub_eq : p * m - 1 - 1 = p * m - 2 := by omega
        rw [h_sub_eq]
        exact h_ineq)
      have h_le1 := padicVal_factorial_le_div_order p (p * m - 1) pp hp2 (by omega)
      rw [h_padic_eq] at h_le1
      generalize h_sum_val : ∑ k ∈ Finset.Ico 1 (p * m - 1), padicValNat p (2 ^ k - 1) = S at h_sum_ge h_le1 ⊢
      generalize h_div_eq : (p * m - 1 - 1) / orderOf (2 : ZMod p) = K at h_sum_ge h_le1
      omega
    · have hpm : p > m := by omega
      have h_le_fact := padicValNat_factorial_le_m_sub_one p m pp hp2 hm hpm
      have h_sum_ge : ∑ k ∈ Finset.Ico 1 (p * m - 1), padicValNat p (2 ^ k - 1) ≥ m := by
        have h_sum_ge_div := sum_padicVal_ge_div_order p (p * m - 1) pp hp2
        have h_sub_eq : p * m - 1 - 1 = p * m - 2 := by omega
        rw [h_sub_eq] at h_sum_ge_div
        have h_ord_pos : orderOf (2 : ZMod p) > 0 := by
          have hp_gt : p > 2 := by
            have : p > 1 := pp.one_lt
            omega
          exact orderOf_two_pos p hp_gt pp
        have h_ord_le := order_le_p_sub_one p pp hp2
        have h_mul_le_m : orderOf (2 : ZMod p) * m ≤ (p - 1) * m := Nat.mul_le_mul_right m h_ord_le
        have h_sub_le : (p - 1) * m ≤ p * m - 2 := by
          have h_dist : (p - 1) * m = p * m - m := by
            rw [Nat.sub_mul, one_mul]
          rw [h_dist]
          omega
        have h_trans : orderOf (2 : ZMod p) * m ≤ p * m - 2 := le_trans h_mul_le_m h_sub_le
        have h_div_ge : m ≤ (p * m - 2) / orderOf (2 : ZMod p) := by
          rw [Nat.le_div_iff_mul_le h_ord_pos]
          rw [mul_comm]
          exact h_trans
        omega
      rw [h_padic_eq] at h_le_fact
      omega


lemma primitive_root_of_prime (n : ℕ) (hn : n > 2) (hp : Nat.Prime n) (h_dvd : n ∣ (a (n - 1) + 2 ^ (n - 2))) :
  IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  rw [Nat.totient_prime hp]
  have h_ord_dvd := orderOf_two_dvd n hn hp
  have h_ord_le := Nat.le_of_dvd (by omega) h_ord_dvd
  by_contra hc
  have h_ord_lt : orderOf (2 : ZMod n) < n - 1 := by omega
  have hd_pos := orderOf_two_pos n hn hp
  have h_pow_eq_one : (2 : ZMod n) ^ orderOf (2 : ZMod n) = 1 := pow_orderOf_eq_one (2 : ZMod n)
  generalize hd_val : orderOf (2 : ZMod n) = d at h_ord_lt hd_pos h_pow_eq_one ⊢
  have hd_ico : d ∈ Finset.Ico 1 (n - 1) := by
    rw [Finset.mem_Ico]
    omega
  have hd_dvd_prod : 2 ^ d - 1 ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
    exact Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) hd_ico
  have h_cast : ((2 ^ d : ℕ) : ZMod n) = 1 := by
    have : (2 : ZMod n) ^ d = ((2 ^ d : ℕ) : ZMod n) := by
      push_cast
      rfl
    rw [← this]
    exact h_pow_eq_one
  have h_cast2 : ((2 ^ d : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    rw [Nat.cast_one]
    exact h_cast
  rw [ZMod.natCast_eq_natCast_iff' (2 ^ d) 1 n] at h_cast2
  have h_mod : 2 ^ d % n = 1 := by
    have h1n : 1 % n = 1 := by
      apply Nat.mod_eq_of_lt
      omega
    rw [h1n] at h_cast2
    exact h_cast2
  have h_div_mul : 2 ^ d = n * (2 ^ d / n) + 1 := by
    have h_div_add := Nat.div_add_mod (2 ^ d) n
    rw [h_mod] at h_div_add
    omega
  have h_sub_pow : 2 ^ d - 1 = n * (2 ^ d / n) := by omega
  have hn_dvd_pow : n ∣ 2 ^ d - 1 := by
    rw [h_sub_pow]
    exact dvd_mul_right n (2 ^ d / n)
  have hn_dvd_prod : n ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) :=
    dvd_trans hn_dvd_pow hd_dvd_prod
  have h_eq : 2 ^ (n - 2) * ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) + (n - 1).factorial) =
      (a (n - 1) + 2 ^ (n - 2)) * (n - 1).factorial := by
    rw [mul_add, ← a_exact n hn]
    ring
  have h_prime_alg : _root_.Prime n := Nat.Prime.prime hp
  have h_div_sum : n ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) + (n - 1).factorial := by
    have h_mul_dvd : n ∣ 2 ^ (n - 2) * ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) + (n - 1).factorial) := by
      rw [h_eq]
      exact dvd_mul_of_dvd_left h_dvd _
    rcases h_prime_alg.dvd_mul.mp h_mul_dvd with h_dvd_pow | h_dvd_sum
    · exfalso
      have h_not_dvd_pow : ¬ n ∣ 2 ^ (n - 2) := by
        intro h_dvd_2_pow
        rw [h_prime_alg.dvd_pow_iff_dvd (by omega)] at h_dvd_2_pow
        have : n ∣ 2 := h_dvd_2_pow
        have : n ≤ 2 := Nat.le_of_dvd (by decide) this
        omega
      exact h_not_dvd_pow h_dvd_pow
    · exact h_dvd_sum
  have h_dvd_fact : n ∣ (n - 1).factorial := by
    have h_sub_eq : (n - 1).factorial = ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) + (n - 1).factorial) - (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by omega
    rw [h_sub_eq]
    exact Nat.dvd_sub h_div_sum hn_dvd_prod
  have h_not_dvd_fact : ¬ n ∣ (n - 1).factorial := by
    rw [Nat.Prime.dvd_factorial hp]
    omega
  exact h_not_dvd_fact h_dvd_fact

theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdvd
  have hp : Nat.Prime n := prime_of_dvd n hn hdvd
  have h_root := primitive_root_of_prime n hn hp hdvd
  exact ⟨hp, h_root⟩

