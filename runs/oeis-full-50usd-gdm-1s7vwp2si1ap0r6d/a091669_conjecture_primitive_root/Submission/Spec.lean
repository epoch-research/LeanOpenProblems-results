import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
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


theorem flt_pow_dvd (p i : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) : p ∣ 2 ^ (i * (p - 1)) - 1 := by
  haveI : Fact p.Prime := hp
  have h_neq : (2 : ZMod p) ≠ 0 := by
    intro hc
    have hc' : ((2 : ℕ) : ZMod p) = 0 := hc
    have h_dvd : p ∣ 2 := by
      rwa [CharP.cast_eq_zero_iff (ZMod p) p] at hc'
    have : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  have h_pow : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h_neq
  have h_pow_mul : (2 : ZMod p) ^ (i * (p - 1)) = 1 := by
    rw [mul_comm]
    rw [pow_mul]
    rw [h_pow, one_pow]
  have hd_eq' : ((2 ^ (i * (p - 1)) : ℕ) : ZMod p) = 1 := by
    exact_mod_cast h_pow_mul
  have hd_eq'' : ((2 ^ (i * (p - 1)) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_one]
    exact hd_eq'
  have h_mod : 2 ^ (i * (p - 1)) ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff (2 ^ (i * (p - 1))) 1 p).mp hd_eq''
  have h_pow_ge : 2 ^ (i * (p - 1)) ≥ 1 := Nat.one_le_pow (i * (p - 1)) 2 (by decide)
  have h_mod_eq : 2 ^ (i * (p - 1)) % p = 1 := by
    have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    change 2 ^ (i * (p - 1)) % p = 1 % p at h_mod
    rwa [h1] at h_mod
  have h_div_eq : 2 ^ (i * (p - 1)) = p * (2 ^ (i * (p - 1)) / p) + 1 := by
    have h_div_add := Nat.div_add_mod (2 ^ (i * (p - 1))) p
    rw [h_mod_eq] at h_div_add
    exact h_div_add.symm
  use (2 ^ (i * (p - 1))) / p
  omega

theorem factor_odd (k : ℕ) (hk : k ≥ 1) : (2 ^ k - 1) % 2 = 1 := by
  have : k = (k - 1) + 1 := by omega
  rw [this, pow_succ]
  have h_pow_pos : 2 ^ (k - 1) ≥ 1 := Nat.one_le_pow (k - 1) 2 (by decide)
  have h_eq : 2 ^ (k - 1) * 2 - 1 = 2 * (2 ^ (k - 1) - 1) + 1 := by omega
  rw [h_eq]
  omega

theorem prod_odd (n : ℕ) : (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ)) % 2 = 1 ∨ (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ)) = 1 := by
  induction' n with n ih
  · simp
  · by_cases hn : n = 0
    · subst hn
      simp
    · have hn1 : n ≥ 1 := by omega
      rw [Finset.prod_Ico_succ_top hn1]
      have h_odd := factor_odd n hn1
      rcases ih with ih1 | ih2
      · left
        rw [Nat.mul_mod]
        rw [ih1, h_odd]
      · rw [ih2]
        simp [h_odd]

theorem padic_two (n : ℕ) (hn : n ≥ 1) :
  padicValNat 2 n.factorial ≤ padicValNat 2 ((2 ^ (n - 1)) * (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ))) := by
  haveI : Fact (Nat.Prime 2) := ⟨prime_two⟩
  have h_two_pos : 2 > 0 := by decide
  have h_pow_nz : 2 ^ (n - 1) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos h_two_pos)
  have h_prod_nz : (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ))  ≠ 0 := by
    have h_prod := prod_odd n
    intro hc
    rcases h_prod with h1 | h2
    · rw [hc] at h1; contradiction
    · rw [hc] at h2; contradiction
  rw [padicValNat.mul h_pow_nz h_prod_nz]
  have h_odd : padicValNat 2 ((Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ))) = 0 := by
    have h_prod := prod_odd n
    rcases h_prod with h1 | h2
    · exact padicValNat.eq_zero_of_not_dvd (by
        intro hd
        have hd2 : 2 ∣ (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ)) := hd
        rw [Nat.dvd_iff_mod_eq_zero] at hd2
        rw [hd2] at h1
        contradiction)
    · rw [h2]
      exact padicValNat.one
  rw [h_odd, add_zero]
  rw [padicValNat.prime_pow (n - 1)]
  have h_lt : padicValNat 2 n.factorial < n := padicValNat_factorial_lt_of_ne_zero 2 (by omega)
  omega

theorem factorial_val_le_pred (p n : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) (hn : n ≠ 0) :
  padicValNat p n.factorial ≤ (n - 1) / (p - 1) := by
  have h_val := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) hn
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  rw [mul_comm]
  omega

theorem padic_odd_induction (p : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) (n : ℕ) :
  (n - 1) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ))) := by
  induction' n with n ih
  · simp
  · by_cases hn : n = 0
    · subst hn
      simp
    · have hn1 : n ≥ 1 := by omega
      have hp1 : p - 1 > 0 := by omega
      have h_prod : (Finset.Ico 1 (n + 1)).prod (fun k => (2 ^ k - 1 : ℕ)) = (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ)) * (2 ^ n - 1) := by
        exact Finset.prod_Ico_succ_top (f := fun k => (2 ^ k - 1 : ℕ)) hn1
      have h_nz1 : (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro k hk
        rw [Finset.mem_Ico] at hk
        have : 2 ^ k ≥ 2 := Nat.pow_le_pow_right (show 0 < 2 by decide) hk.1
        omega
      have h_nz2 : 2 ^ n - 1 ≠ 0 := by
        have : 2 ^ n ≥ 2 := Nat.pow_le_pow_right (show 0 < 2 by decide) hn1
        omega
      rw [h_prod]
      rw [padicValNat.mul h_nz1 h_nz2]
      by_cases h_div : p - 1 ∣ n
      · rcases h_div with ⟨c, hc⟩
        have h_flt : p ∣ 2 ^ n - 1 := by
          have h_mul : c * (p - 1) = n := by
            rw [mul_comm]
            exact hc.symm
          have h_flt_orig := flt_pow_dvd p c hp2
          rwa [h_mul] at h_flt_orig
        have h_val_ge : 1 ≤ padicValNat p (2 ^ n - 1) := by
          have h_dvd_iff := padicValNat_dvd_iff (p := p) 1
          rw [pow_one] at h_dvd_iff
          rw [h_dvd_iff] at h_flt
          exact h_flt.resolve_left h_nz2
        have h_arith : (n + 1 - 1) / (p - 1) = (n - 1) / (p - 1) + 1 := by
          have hn_eq : n = (p - 1) * c := hc
          have hc_nz : c ≠ 0 := by
            intro hc0
            subst hc0
            simp [hn_eq] at hn
          have hc_pos : c ≥ 1 := by omega
          have h_eq_c : c = (c - 1) + 1 := by omega
          have h_mul_eq : (p - 1) * c = (p - 1) * (c - 1) + (p - 1) := by
            nth_rw 1 [h_eq_c]
            rw [Nat.mul_add, mul_one]
          have h_sub : (p - 1) * c - 1 = (p - 1) * (c - 1) + (p - 2) := by
            rw [h_mul_eq]
            omega
          rw [hn_eq]
          have h_add_sub : (p - 1) * c + 1 - 1 = (p - 1) * c := by omega
          rw [h_add_sub]
          rw [Nat.mul_div_cancel_left _ hp1]
          rw [h_sub]
          rw [add_comm ((p - 1) * (c - 1)) (p - 2)]
          rw [Nat.add_mul_div_left _ _ hp1]
          have h_lt : (p - 2) / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
          rw [h_lt, zero_add]
          exact h_eq_c
        rw [h_arith]
        have : padicValNat p (2 ^ n - 1) ≥ 1 := h_val_ge
        omega
      · have h_arith : (n + 1 - 1) / (p - 1) = (n - 1) / (p - 1) := by
          have h_sub1 : n + 1 - 1 = n := by omega
          rw [h_sub1]
          have h_mod : n % (p - 1) ≠ 0 := by
            intro hc
            have : p - 1 ∣ n := Nat.dvd_of_mod_eq_zero hc
            contradiction
          have h_div_eq := Nat.div_add_mod n (p - 1)
          have h_eq : n - 1 = (n % (p - 1) - 1) + (p - 1) * (n / (p - 1)) := by omega
          rw [h_eq]
          rw [Nat.add_mul_div_left _ _ hp1]
          have h_lt_mod : n % (p - 1) < p - 1 := Nat.mod_lt _ hp1
          have h_lt : (n % (p - 1) - 1) / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
          rw [h_lt, zero_add]
        rw [h_arith]
        omega

theorem padic_odd (p n : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) (hn : n ≥ 1) :
  padicValNat p n.factorial ≤ padicValNat p ((2 ^ (n - 1)) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)) := by
  have hp1 : p - 1 > 0 := by omega
  have h_pow_nz : (2 : ℕ) ^ (n - 1) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
  have h_prod_nz : (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1) ≠ 0 := by
    have h_prod := prod_odd n
    intro hc
    rcases h_prod with h1 | h2
    · rw [hc] at h1; contradiction
    · rw [hc] at h2; contradiction
  rw [padicValNat.mul h_pow_nz h_prod_nz]
  have h_zero : padicValNat p (2 ^ (n - 1)) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hd_prime := hp.out.dvd_of_dvd_pow hd
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hd_prime
    omega
  rw [h_zero, zero_add]
  have h_le_pred := factorial_val_le_pred p n hp2 (by omega)
  have h_ind := padic_odd_induction p hp2 n
  exact le_trans h_le_pred h_ind

theorem dvd_iff_padicValNat_le (d n : ℕ) (hd : d ≠ 0) (hn : n ≠ 0) :
  d ∣ n ↔ ∀ p [hp : Fact p.Prime], padicValNat p d ≤ padicValNat p n := by
  constructor
  · intro h p hp
    have h_pow_dvd := pow_padicValNat_dvd (p := p) (n := d)
    have h_dvd := dvd_trans h_pow_dvd h
    rw [padicValNat_dvd_iff] at h_dvd
    exact h_dvd.resolve_left hn
  · intro h
    rw [dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    haveI : Fact p.Prime := ⟨hp⟩
    rw [padicValNat_dvd_iff] at hpk
    have hpk_le := hpk.resolve_left hd
    have h_le := h p
    rw [padicValNat_dvd_iff]
    right
    exact le_trans hpk_le h_le

theorem a_integer (n : ℕ) (hn : n ≥ 1) : n.factorial ∣ (2 ^ (n - 1)) * (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ)) := by
  have h_den_nz : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have h_num_nz : (2 ^ (n - 1)) * (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ)) ≠ 0 := by
    apply mul_ne_zero
    · exact Nat.ne_of_gt (Nat.pow_pos (by decide))
    · have h_prod := prod_odd n
      intro hc
      rcases h_prod with h1 | h2
      · rw [hc] at h1; contradiction
      · rw [hc] at h2; contradiction
  rw [dvd_iff_padicValNat_le n.factorial ((2 ^ (n - 1)) * (Finset.Ico 1 n).prod (fun k => (2 ^ k - 1 : ℕ))) h_den_nz h_num_nz]
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2
    exact padic_two n hn
  · have hp2_gt : p > 2 := by
      have : p ≥ 2 := hp.out.two_le
      omega
    exact padic_odd p n hp2_gt hn

theorem factorial_mul_a (n : ℕ) (hn : n ≥ 1) :
  n.factorial * a n = (2 ^ (n - 1)) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1) := by
  have h_nz : n ≠ 0 := by omega
  unfold a
  split_ifs with h
  · contradiction
  · simp only
    have h_dvd := a_integer n hn
    have h_pred : n.pred = n - 1 := by rw [Nat.pred_eq_sub_one]
    rw [h_pred]
    exact Nat.mul_div_cancel' h_dvd

theorem a_of_gt_two (n : ℕ) (hn : n > 2) :
  a (n - 1) = ((2 ^ (n - 2)) * (Finset.Ico 1 (n-1)).prod (fun k => 2 ^ k - 1)) / (n-1).factorial := by
  have h1 : n - 1 ≠ 0 := by omega
  have h2 : (n - 1).pred = n - 2 := by
    rw [Nat.pred_eq_sub_one]
    omega
  unfold a
  split_ifs with h
  · contradiction
  · simp only [h2]

theorem prime_primitive_root (n : ℕ) (hn : n > 2) (hp : Nat.Prime n)
  (h_div : n ∣ a (n - 1) + 2 ^ (n - 2)) :
  IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  haveI : Fact (Nat.Prime n) := ⟨hp⟩
  have h_neq : (2 : ZMod n) ≠ 0 := by
    intro hc
    have hc' : ((2 : ℕ) : ZMod n) = 0 := hc
    have h_dvd : n ∣ 2 := by
      rwa [CharP.cast_eq_zero_iff (ZMod n) n] at hc'
    have : n ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  set d := orderOf (2 : ZMod n) with hd_def
  have hd_eq : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
  have hd_eq' : ((2 ^ d : ℕ) : ZMod n) = 1 := by
    exact_mod_cast hd_eq
  have hd_eq'' : ((2 ^ d : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    rw [Nat.cast_one]
    exact hd_eq'
  have h_mod : 2 ^ d ≡ 1 [MOD n] := (ZMod.natCast_eq_natCast_iff (2 ^ d) 1 n).mp hd_eq''
  have h_pow : (2 : ZMod n) ^ (n - 1) = 1 := ZMod.pow_card_sub_one_eq_one h_neq
  have hd_nz : d ≠ 0 := by
    intro hc
    rw [hd_def, orderOf_eq_zero_iff'] at hc
    have h_not := hc (n - 1) (by omega)
    exact h_not h_pow
  have hd_pos : d > 0 := by omega
  have h_pow_ge : 2 ^ d ≥ 1 := by
    have : 2 ^ d ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hd_pos
    omega
  have h_mod_eq : 2 ^ d % n = 1 := by
    have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    change 2 ^ d % n = 1 % n at h_mod
    rwa [h1] at h_mod
  have h_div_n : n ∣ 2 ^ d - 1 := by
    have h_div_eq : 2 ^ d = n * (2 ^ d / n) + 1 := by
      have h_div_add := Nat.div_add_mod (2 ^ d) n
      rw [h_mod_eq] at h_div_add
      exact h_div_add.symm
    use (2 ^ d) / n
    omega
  have h_dvd_order : d ∣ n - 1 := orderOf_dvd_of_pow_eq_one h_pow
  by_cases hd_eq : d = n - 1
  · rw [Nat.totient_prime hp, IsPrimitiveRoot.iff_orderOf, ← hd_def, hd_eq]
  · have h_lt : d < n - 1 := by
      have hn1 : n - 1 > 0 := by omega
      have : d ≤ n - 1 := Nat.le_of_dvd hn1 h_dvd_order
      omega
    have hd_mem : d ∈ Finset.Ico 1 (n - 1) := by
      rw [Finset.mem_Ico]
      omega
    set P := (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) with hP_def
    have hd_dvd_P : 2 ^ d - 1 ∣ P := Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) hd_mem
    have hn_dvd_P : n ∣ P := Nat.dvd_trans h_div_n hd_dvd_P
    have hn_dvd_fact_mul : n ∣ (n - 1).factorial * (a (n - 1) + 2 ^ (n - 2)) :=
      dvd_mul_of_dvd_right h_div (n - 1).factorial
    have h_distrib : (n - 1).factorial * (a (n - 1) + 2 ^ (n - 2)) =
        (n - 1).factorial * a (n - 1) + (n - 1).factorial * 2 ^ (n - 2) := by
      rw [Nat.mul_add]
    have h_fac_a : (n - 1).factorial * a (n - 1) = 2 ^ (n - 2) * P := by
      have hn_sub_ge : n - 1 ≥ 1 := by omega
      have h_fac_a_orig := factorial_mul_a (n - 1) hn_sub_ge
      have h_pred : (n - 1 - 1) = n - 2 := by omega
      rwa [h_pred] at h_fac_a_orig
    rw [h_distrib, h_fac_a] at hn_dvd_fact_mul
    have h_factor_out : 2 ^ (n - 2) * P + (n - 1).factorial * 2 ^ (n - 2) =
        2 ^ (n - 2) * (P + (n - 1).factorial) := by
      rw [mul_comm (n - 1).factorial _, ← Nat.mul_add]
    rw [h_factor_out] at hn_dvd_fact_mul
    have hn_dvd_sum : n ∣ P + (n - 1).factorial := by
      cases' (Nat.Prime.dvd_mul hp).mp hn_dvd_fact_mul with h1 h2
      · -- n ∣ 2 ^ (n - 2)
        have h_div_two : n ∣ 2 := by
          apply hp.dvd_of_dvd_pow h1
        have : n ≤ 2 := Nat.le_of_dvd (by decide) h_div_two
        omega
      · exact h2
    have hn_dvd_fact : n ∣ (n - 1).factorial := by
      exact (Nat.dvd_add_right hn_dvd_P).mp hn_dvd_sum
    have hn_not_dvd_fact : ¬ n ∣ (n - 1).factorial := by
      rw [Nat.Prime.dvd_factorial hp]
      omega
    contradiction

lemma padicValNat_factorial_mul_prime (p q : ℕ) [hp : Fact p.Prime] (hq : q ≥ 2) :
  padicValNat p (p * q - 1).factorial = padicValNat p (q - 1).factorial + (q - 1) := by
  have h_eq : p * q - 1 = p * (q - 1) + (p - 1) := by
    have hq_eq : q = (q - 1) + 1 := by omega
    have hp_ge : p ≥ 2 := hp.out.two_le
    nth_rw 1 [hq_eq]
    rw [Nat.mul_add, mul_one]
    generalize p * (q - 1) = X
    omega
  have hp_pos : p - 1 < p := by
    have : p ≥ 2 := hp.out.two_le
    omega
  rw [h_eq]
  rw [padicValNat_factorial_mul_add (q - 1) hp_pos]
  rw [padicValNat_factorial_mul (q - 1)]

lemma padicValNat_factorial_mul_prime_lt (p q : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) (hq : q ≥ 2) :
  padicValNat p (p * q - 1).factorial < (p * q - 2) / (p - 1) := by
  rw [padicValNat_factorial_mul_prime p q hq]
  have h_le := factorial_val_le_pred p (q - 1) hp2 (by omega)
  have h_le' : padicValNat p (q - 1).factorial ≤ (q - 2) / (p - 1) := by
    have : q - 1 - 1 = q - 2 := by omega
    rwa [this] at h_le
  have hp1 : p - 1 > 0 := by omega
  have h_div_eq : (p * q - 2) / (p - 1) = (q - 2) / (p - 1) + q := by
    have h_eq : p * q - 2 = (q - 2) + (p - 1) * q := by
      have hq_eq : q = (q - 2) + 2 := by omega
      nth_rw 1 [hq_eq]
      nth_rw 3 [hq_eq]
      rw [Nat.mul_add, Nat.mul_add]
      have hp_eq : p = p - 1 + 1 := by omega
      nth_rw 1 [hp_eq]
      rw [Nat.add_mul, one_mul]
      have : p ≥ 2 := hp.out.two_le
      generalize (p - 1) * (q - 2) = A
      omega
    rw [h_eq]
    rw [Nat.add_mul_div_left _ _ hp1]
  rw [h_div_eq]
  revert h_le'
  generalize (q - 2) / (p - 1) = Y
  intro h_le'
  have : q = (q - 1) + 1 := by omega
  omega

lemma sum_le_length_of_le_one (L : List ℕ) (h : ∀ x ∈ L, x ≤ 1) : L.sum ≤ L.length := by
  induction' L with hd tl ih
  · simp
  · have h_hd : hd ≤ 1 := h hd (by simp)
    have h_tl : ∀ x ∈ tl, x ≤ 1 := by
      intro x hx
      exact h x (by simp [hx])
    have ih' := ih h_tl
    simp only [List.sum_cons, List.length_cons]
    omega

lemma prod_ne_zero (m : ℕ) : (Finset.Ico 1 m).prod (fun k => 2 ^ k - 1) ≠ 0 := by
  have h_prod := prod_odd m
  intro hc_prod
  rcases h_prod with h1 | h2
  · rw [hc_prod] at h1; contradiction
  · rw [hc_prod] at h2; contradiction

lemma a_ne_zero (n : ℕ) (hn : n > 2) : a (n - 1) ≠ 0 := by
  intro hc
  have h_mul := factorial_mul_a (n - 1) (by omega)
  have h_nz : 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by
    apply mul_ne_zero
    · exact Nat.ne_of_gt (Nat.pow_pos (by decide))
    · exact prod_ne_zero (n - 1)
  have h_eq_sub : n - 1 - 1 = n - 2 := by omega
  rw [h_eq_sub] at h_mul
  rw [hc, mul_zero] at h_mul
  exact h_nz h_mul.symm

lemma padic_two_prod_zero (m : ℕ) : padicValNat 2 ((Finset.Ico 1 m).prod (fun k => 2 ^ k - 1)) = 0 := by
  have h_prod := prod_odd m
  rcases h_prod with h1 | h2
  · apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hd2 : 2 ∣ (Finset.Ico 1 m).prod (fun k => (2 ^ k - 1 : ℕ)) := hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd2
    rw [hd2] at h1
    contradiction
  · rw [h2]
    exact padicValNat.one

theorem not_dvd_composite_odd (n : ℕ) (hn : n > 2) (p : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) (hdvd : p ∣ n) (h_comp : p < n) :
  ¬ (n ∣ a (n - 1) + 2 ^ (n - 2)) := by
  intro h_div
  have ⟨q, h_eq_pq⟩ := hdvd
  have h_q_ge : q ≥ 2 := by
    by_contra hc
    have hq : q ≤ 1 := by omega
    interval_cases q
    · subst h_eq_pq
      simp at hn
    · subst h_eq_pq
      simp at h_comp
  set P := (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) with hP_def
  have h_lt : padicValNat p (n - 1).factorial < padicValNat p P := by
    have h_lt_eq := padicValNat_factorial_mul_prime_lt p q hp2 h_q_ge
    have h_ind := padic_odd_induction p hp2 (n - 1)
    have h_eq : (n - 1 - 1) = n - 2 := by omega
    rw [h_eq] at h_ind
    rw [← h_eq_pq] at h_lt_eq
    rw [← hP_def] at h_ind
    omega
  have h_nz_a : a (n - 1) ≠ 0 := a_ne_zero n hn
  have h_val_mul : padicValNat p ((n - 1).factorial * a (n - 1)) =
      padicValNat p (n - 1).factorial + padicValNat p (a (n - 1)) := by
    apply padicValNat.mul (Nat.factorial_ne_zero (n - 1)) h_nz_a
  have h_fac_a_orig := factorial_mul_a (n - 1) (by omega)
  have h_eq_sub : n - 1 - 1 = n - 2 := by omega
  rw [h_eq_sub, ← hP_def] at h_fac_a_orig
  rw [h_fac_a_orig] at h_val_mul
  have h_nz_2pow : (2 : ℕ) ^ (n - 2) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
  have h_nz_P : P ≠ 0 := prod_ne_zero (n - 1)
  have h_val_num : padicValNat p (2 ^ (n - 2) * P) = padicValNat p P := by
    rw [padicValNat.mul h_nz_2pow h_nz_P]
    have h_zero : padicValNat p (2 ^ (n - 2)) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hd_prime := hp.out.dvd_of_dvd_pow hd
      have : p ≤ 2 := Nat.le_of_dvd (by decide) hd_prime
      omega
    rw [h_zero, zero_add]
  rw [h_val_num] at h_val_mul
  have hp_dvd_a : p ∣ a (n - 1) := by
    have h_val_ge : padicValNat p (a (n - 1)) ≥ 1 := by omega
    have h_dvd_iff := padicValNat_dvd_iff (p := p) 1
    rw [pow_one] at h_dvd_iff
    rw [h_dvd_iff]
    right
    exact h_val_ge
  have hp_dvd_sum : p ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans (by omega) h_div
  have hp_dvd_2pow : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hp_dvd_a).mp hp_dvd_sum
  have hp_dvd_2 : p ∣ 2 := hp.out.dvd_of_dvd_pow hp_dvd_2pow
  have : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd_2
  omega

lemma not_dvd_power_of_two (r : ℕ) (hr : r ≥ 2) :
  ¬ (2 ^ r ∣ a (2 ^ r - 1) + 2 ^ (2 ^ r - 2)) := by
  intro h_div
  set n := 2 ^ r with hn_def
  have hn_gt : n > 2 := by
    have : 2 ^ r ≥ 4 := Nat.pow_le_pow_right (show 0 < 2 by decide) hr
    omega
  have hr_le : r ≤ 2 ^ r - 2 := by
    have h_pow : ∀ k ≥ 2, 2 ^ k ≥ k + 2 := by
      intro k hk
      induction' k, hk using Nat.le_induction with j hj ihj
      · decide
      · rw [pow_succ]
        omega
    induction' r, hr using Nat.le_induction with k hk ih
    · decide
    · have h_pow_k := h_pow k hk
      rw [pow_succ]
      omega
  have h_dvd_2pow : 2 ^ r ∣ 2 ^ (2 ^ r - 2) := pow_dvd_pow 2 hr_le
  have h_div_a : 2 ^ r ∣ a (2 ^ r - 1) := by
    rw [hn_def] at h_div
    exact (Nat.dvd_add_left h_dvd_2pow).mp h_div
  haveI : Fact (Nat.Prime 2) := ⟨prime_two⟩
  have h_val_ge : r ≤ padicValNat 2 (a (2 ^ r - 1)) := by
    have h_dvd_iff := padicValNat_dvd_iff (p := 2) r (a (2 ^ r - 1))
    rw [h_dvd_iff] at h_div_a
    exact h_div_a.resolve_left (a_ne_zero n hn_gt)
  have h_mul := factorial_mul_a (n - 1) (by omega)
  have h_val_mul : padicValNat 2 ((n - 1).factorial * a (n - 1)) =
      padicValNat 2 (n - 1).factorial + padicValNat 2 (a (n - 1)) := by
    apply padicValNat.mul (Nat.factorial_ne_zero (n - 1)) (a_ne_zero n hn_gt)
  have h_eq_sub : n - 1 - 1 = n - 2 := by omega
  rw [h_eq_sub] at h_mul
  rw [h_mul] at h_val_mul
  have h_val_num : padicValNat 2 (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = n - 2 := by
    rw [padicValNat.mul (Nat.ne_of_gt (Nat.pow_pos (by decide))) (prod_ne_zero (n - 1))]
    rw [padic_two_prod_zero (n - 1), add_zero]
    rw [padicValNat.prime_pow (n - 2)]
  rw [h_val_num] at h_val_mul
  have h_legendre := sub_one_mul_padicValNat_factorial (n - 1) (p := 2)
  have h_sub_one : 2 - 1 = 1 := by decide
  rw [h_sub_one, one_mul] at h_legendre
  have h_lt_base : ∀ d ∈ Nat.digits 2 (n - 1), d < 2 := fun d hd ↦ digits_lt_base (by decide) hd
  have h_le_one : ∀ d ∈ Nat.digits 2 (n - 1), d ≤ 1 := by
    intro d hd
    have := h_lt_base d hd
    omega
  have h_sum_le := sum_le_length_of_le_one (Nat.digits 2 (n - 1)) h_le_one
  have h_len_le : (Nat.digits 2 (n - 1)).length ≤ r := by
    rw [digits_length_le_iff (by decide)]
    rw [← hn_def]
    omega
  rw [← hn_def] at hr_le
  rw [← hn_def] at h_val_ge
  omega

-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) :=
by
  intro h_div
  have hp : Nat.Prime n := by
    by_contra hc
    rcases eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨k, rfl⟩ | ⟨p, hp_prime, hdvd, hodd⟩
    · have hk : k ≥ 2 := by
        by_contra hc2
        have : k ≤ 1 := by omega
        interval_cases k
        · simp at hn
        · simp at hn
      exact not_dvd_power_of_two k hk h_div
    · haveI : Fact p.Prime := ⟨hp_prime⟩
      have hp2 : p > 2 := by
        have : p ≥ 2 := hp_prime.two_le
        by_contra hc2
        have : p = 2 := by omega
        subst this
        revert hodd
        decide
      have h_comp : p < n := by
        by_contra hc2
        have hp_le : p ≤ n := Nat.le_of_dvd (by omega) hdvd
        have : p = n := by omega
        subst this
        exact hc hp_prime
      exact not_dvd_composite_odd n hn p hp2 hdvd h_comp h_div
  exact ⟨hp, prime_primitive_root n hn hp h_div⟩




