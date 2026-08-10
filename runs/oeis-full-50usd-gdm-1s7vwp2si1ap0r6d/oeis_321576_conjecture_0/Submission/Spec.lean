import FormalConjectures.Util.ProblemImports

open Nat Set ZMod

/--
A321576: $a(n)$ is the smallest $b > 1$ such that $b^n - (b-1)^n$ has all divisors $d \equiv 1 \pmod n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if _ : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    -- sInf finds the smallest element of a set in a partial order, which for $\mathbb{N}$ is the minimum.
    sInf S_n
  else
    0

def u_unit (p : ℕ) (q : ℕ) (hp : p > 0) (hq : (2 ^ p - 1) % q = 0) : (ZMod q)ˣ :=
  have h_one : (2 : ZMod q) * 2 ^ (p - 1) = 1 := by
    have h1 : (2 : ZMod q) * 2 ^ (p - 1) = 2 ^ p := by
      have h2 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp).symm
      conv_rhs => rw [h2]
      rw [_root_.pow_succ']
    rw [h1]
    have hdiv : q ∣ 2 ^ p - 1 := Nat.dvd_of_mod_eq_zero hq
    rcases hdiv with ⟨k, hk⟩
    have h2p : 2 ^ p = (2 ^ p - 1) + 1 := by
      have : 2 ^ p ≥ 1 := Nat.one_le_pow p 2 (by omega)
      omega
    have h_eq : 2 ^ p = q * k + 1 := by
      rw [h2p, hk]
    have h_zmod : (2 : ZMod q) ^ p = ((2 ^ p : ℕ) : ZMod q) := by
      push_cast
      rfl
    rw [h_zmod]
    have h_zmod2 : ((2 ^ p : ℕ) : ZMod q) = ((q * k + 1 : ℕ) : ZMod q) := by
      rw [h_eq]
    rw [h_zmod2]
    push_cast
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  { val := 2
    inv := 2 ^ (p - 1)
    val_inv := h_one
    inv_val := by
      rw [mul_comm]
      exact h_one
  }

theorem u_unit_pow (p : ℕ) (hp : p > 0) (q : ℕ) (hq : (2 ^ p - 1) % q = 0) :
    (u_unit p q hp hq) ^ p = 1 := by
  rw [← Units.val_eq_one]
  push_cast
  have h_def : (↑(u_unit p q hp hq) ^ p : ZMod q) = (2 : ZMod q) ^ p := by rfl
  rw [h_def]
  have hdiv : q ∣ 2 ^ p - 1 := Nat.dvd_of_mod_eq_zero hq
  rcases hdiv with ⟨k, hk⟩
  have h2p : 2 ^ p = (2 ^ p - 1) + 1 := by
    have : 2 ^ p ≥ 1 := Nat.one_le_pow p 2 (by omega)
    omega
  have h_eq : 2 ^ p = q * k + 1 := by
    rw [h2p, hk]
  have h_zmod : (2 : ZMod q) ^ p = ((2 ^ p : ℕ) : ZMod q) := by
    push_cast
    rfl
  rw [h_zmod]
  have h_zmod2 : ((2 ^ p : ℕ) : ZMod q) = ((q * k + 1 : ℕ) : ZMod q) := by
    rw [h_eq]
  rw [h_zmod2]
  push_cast
  have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
  rw [hq0]
  ring

theorem u_unit_ne_one (p : ℕ) (hp_prime : p.Prime) (q : ℕ) (hq_prime : q.Prime) (hdvd : q ∣ 2 ^ p - 1) :
    u_unit p q (Nat.Prime.pos hp_prime) (by exact Nat.modEq_zero_iff_dvd.mpr hdvd) ≠ 1 := by
  intro h_eq
  have h_val : u_unit p q (Nat.Prime.pos hp_prime) (by exact Nat.modEq_zero_iff_dvd.mpr hdvd) = 1 := h_eq
  rw [← Units.val_eq_one] at h_val
  have h_def : (↑(u_unit p q (Nat.Prime.pos hp_prime) (by exact Nat.modEq_zero_iff_dvd.mpr hdvd)) : ZMod q) = (2 : ZMod q) := by rfl
  rw [h_def] at h_val
  have h_even : 2 ∣ 2 ^ p := by
    use 2 ^ (p - 1)
    have hp_pos : p > 0 := Nat.Prime.pos hp_prime
    have : p = p - 1 + 1 := by omega
    nth_rw 1 [this]
    ring
  have h_odd : ¬ 2 ∣ 2 ^ p - 1 := by
    intro hd
    rcases h_even with ⟨Y, hY⟩
    rcases hd with ⟨Z, hZ⟩
    have h_pow_sub : 2 ^ p - (2 ^ p - 1) = 1 := by
      have : 2 ^ p ≥ 1 := Nat.one_le_pow p 2 (by omega)
      omega
    rw [hZ] at h_pow_sub
    rw [hY] at h_pow_sub
    omega
  have hq2 : q ≠ 2 := by
    intro h_eq2
    rw [h_eq2] at hdvd
    exact h_odd hdvd
  have hq_gt2 : q > 2 := by
    have : q ≥ 2 := Nat.Prime.two_le hq_prime
    omega
  have h1 : (1 < q) := by omega
  have h_fact : Fact (1 < q) := ⟨h1⟩
  have h_val_eq := congr_arg ZMod.val h_val
  have h_val1 : ZMod.val (1 : ZMod q) = 1 := ZMod.val_one q
  have h_val2 : ZMod.val (2 : ZMod q) = 2 := by
    have h_eq2 : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by rfl
    rw [h_eq2]
    rw [ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt hq_gt2]
  rw [h_val2, h_val1] at h_val_eq
  omega

theorem prime_dvd_two_pow_sub_one (p : ℕ) (hp_prime : p.Prime) (q : ℕ) (hq_prime : q.Prime) (hdvd : q ∣ 2 ^ p - 1) :
    p ∣ q - 1 := by
  have : NeZero q := ⟨Nat.Prime.ne_zero hq_prime⟩
  have hp_pos := Nat.Prime.pos hp_prime
  have h_mod : (2 ^ p - 1) % q = 0 := Nat.modEq_zero_iff_dvd.mpr hdvd
  have h_ord : orderOf (u_unit p q hp_pos h_mod) = p := by
    have hp_fact : Fact p.Prime := ⟨hp_prime⟩
    apply orderOf_eq_prime
    · exact u_unit_pow p hp_pos q h_mod
    · exact u_unit_ne_one p hp_prime q hq_prime hdvd
  have h_dvd : orderOf (u_unit p q hp_pos h_mod) ∣ Fintype.card (ZMod q)ˣ := orderOf_dvd_card
  have h_fact : Fact q.Prime := ⟨hq_prime⟩
  have h_card : Fintype.card (ZMod q)ˣ = q - 1 := ZMod.card_units q
  rw [h_ord, h_card] at h_dvd
  exact h_dvd

theorem divisors_modEq_one (p : ℕ) (hp_prime : p.Prime) (d : ℕ) :
    d ∣ 2 ^ p - 1 → d ≡ 1 [MOD p] := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hd0 : d = 0
    · subst hd0
      have hp_pos : p > 0 := Nat.Prime.pos hp_prime
      have h_pow : 2 ^ p ≥ 2 := by
        have : p ≥ 1 := hp_pos
        have h_le := Nat.pow_le_pow_right (by decide : 0 < 2) this
        exact h_le
      have hd_pos : 2 ^ p - 1 > 0 := by omega
      have : 2 ^ p - 1 = 0 := eq_zero_of_zero_dvd hd
      omega
    · by_cases hd1 : d = 1
      · subst hd1
        exact Nat.ModEq.refl 1
      · rcases Nat.exists_prime_and_dvd hd1 with ⟨q, hq_prime, hqd⟩
        have hqdvd : q ∣ 2 ^ p - 1 := dvd_trans hqd hd
        have hq_eq : p ∣ q - 1 := prime_dvd_two_pow_sub_one p hp_prime q hq_prime hqdvd
        rcases hq_eq with ⟨k, hk⟩
        have hq_eq2 : q = p * k + 1 := by
          have : q ≥ 1 := Nat.Prime.pos hq_prime
          omega
        have h_mod_q : q ≡ 1 [MOD p] := by
          change q % p = 1 % p
          rw [hq_eq2, add_comm]
          exact Nat.add_mul_mod_self_left 1 p k
        rcases hqd with ⟨d', rfl⟩
        have hd'_pos : d' > 0 := by
          by_contra hc
          have : d' = 0 := by omega
          subst this
          simp at hd0
        have h_lt : d' < q * d' := by
          have hq2 : q ≥ 2 := Nat.Prime.two_le hq_prime
          have hq_gt1 : 1 < q := by omega
          have : d' * 1 < d' * q := Nat.mul_lt_mul_of_pos_left hq_gt1 hd'_pos
          rw [mul_one, mul_comm] at this
          exact this
        have hd'_dvd : d' ∣ 2 ^ p - 1 := dvd_trans ⟨q, mul_comm q d'⟩ hd
        have hd'_mod : d' ≡ 1 [MOD p] := ih d' h_lt hd'_dvd
        have h_mul := Nat.ModEq.mul h_mod_q hd'_mod
        rw [mul_one] at h_mul
        exact h_mul

theorem even_composite_two_not_mem (n : ℕ) (hn : n > 2) (heven : 2 ∣ n) :
    ¬ (∀ (d : ℕ), d ∣ 2 ^ n - 1 → d ≡ 1 [MOD n]) := by
  intro h_all
  rcases heven with ⟨k, rfl⟩
  have hk : k ≥ 2 := by omega
  have h3_dvd : 3 ∣ 2 ^ (2 * k) - 1 := by
    have h_pow : (2 : ZMod 3) ^ (2 * k) = 1 := by
      rw [pow_mul]
      have : (2 : ZMod 3) ^ 2 = 1 := rfl
      rw [this, one_pow]
    have h_sub : (2 : ZMod 3) ^ (2 * k) - 1 = 0 := by
      rw [h_pow, sub_self]
    have h_cast : ((2 ^ (2 * k) - 1 : ℕ) : ZMod 3) = (2 : ZMod 3) ^ (2 * k) - 1 := by
      have h_le : 1 ≤ 2 ^ (2 * k) := by
        exact Nat.one_le_pow (2 * k) 2 (by decide)
      rw [Nat.cast_sub h_le]
      push_cast
      rfl
    rw [← h_cast] at h_sub
    exact (ZMod.natCast_eq_zero_iff _ 3).mp h_sub
  have h_mod3 := h_all 3 h3_dvd
  -- 3 ≡ 1 [MOD 2*k]
  -- so 2*k ∣ 3 - 1 = 2
  have h_mod3' : 1 ≡ 3 [MOD 2 * k] := h_mod3.symm
  have h_dvd : 2 * k ∣ 3 - 1 := (Nat.modEq_iff_dvd' (by decide)).mp h_mod3'
  have h_dvd' : 2 * k ∣ 2 := h_dvd
  have h_le : 2 * k ≤ 2 := Nat.le_of_dvd (by decide) h_dvd'
  omega

theorem odd_composite_three_dvd_two_not_mem (n : ℕ) (hn : n > 3) (h_odd : ¬ 2 ∣ n) (h3 : 3 ∣ n) :
    ¬ (∀ (d : ℕ), d ∣ 2 ^ n - 1 → d ≡ 1 [MOD n]) := by
  intro h_all
  rcases h3 with ⟨k, rfl⟩
  have hk : k ≥ 3 := by
    have : k ≠ 1 := by
      intro hc
      subst hc
      simp at hn
    have : k ≠ 2 := by
      intro hc
      subst hc
      have : 2 ∣ 3 * 2 := dvd_mul_left 2 3
      exact h_odd this
    omega
  have h7_dvd : 7 ∣ 2 ^ (3 * k) - 1 := by
    have h_pow : (2 : ZMod 7) ^ (3 * k) = 1 := by
      rw [pow_mul]
      have : (2 : ZMod 7) ^ 3 = 1 := rfl
      rw [this, one_pow]
    have h_sub : (2 : ZMod 7) ^ (3 * k) - 1 = 0 := by
      rw [h_pow, sub_self]
    have h_cast : ((2 ^ (3 * k) - 1 : ℕ) : ZMod 7) = (2 : ZMod 7) ^ (3 * k) - 1 := by
      have h_le : 1 ≤ 2 ^ (3 * k) := by
        exact Nat.one_le_pow (3 * k) 2 (by decide)
      rw [Nat.cast_sub h_le]
      push_cast
      rfl
    rw [← h_cast] at h_sub
    exact (ZMod.natCast_eq_zero_iff _ 7).mp h_sub
  have h_mod7 := h_all 7 h7_dvd
  have h_mod7' : 1 ≡ 7 [MOD 3 * k] := h_mod7.symm
  have h_dvd : 3 * k ∣ 7 - 1 := (Nat.modEq_iff_dvd' (by decide)).mp h_mod7'
  have h_dvd' : 3 * k ∣ 6 := h_dvd
  have h_le : 3 * k ≤ 6 := Nat.le_of_dvd (by decide) h_dvd'
  omega

lemma p_square_two_le_two_pow_sub_two (p : ℕ) (hp : p ≥ 7) : p * p * 2 ≤ 2 ^ p - 2 := by
  induction p, hp using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    have h1 : 2 ^ (x + 1) - 2 = 2 * (2 ^ x - 2) + 2 := by
      have : 2 ^ x ≥ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hx
      omega
    rw [h1]
    have h2 : 2 * (2 ^ x - 2) + 2 ≥ 2 * (x * x * 2) + 2 := by omega
    have h3 : 2 * (x * x * 2) + 2 ≥ (x + 1) * (x + 1) * 2 := by
      have h4 : (x + 1) * (x + 1) * 2 = 2 * (x * x) + 4 * x + 2 := by ring
      have h5 : 2 * (x * x * 2) + 2 = 4 * (x * x) + 2 := by ring
      rw [h4, h5]
      have h6 : 2 * (x * x) ≥ 4 * x := by
        have h7 : 2 * x ≥ 4 := by omega
        calc 2 * (x * x) = (2 * x) * x := by ring
        _ ≥ 4 * x := Nat.mul_le_mul_right x h7
      omega
    omega


theorem odd_composite_not_three_dvd_two_not_mem (n : ℕ) (hn : n > 3) (h_odd : ¬ 2 ∣ n) (h_not_prime : ¬ n.Prime) (h3 : ¬ 3 ∣ n) :
    ¬ (∀ (d : ℕ), d ∣ 2 ^ n - 1 → d ≡ 1 [MOD n]) := by
  intro h_all
  let p := Nat.minFac n
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_even : ¬ 2 ∣ p := by
    intro hd
    have : p = 2 := (Nat.Prime.dvd_iff_eq hp_prime (by decide)).mp hd
    have h_2_dvd_n : 2 ∣ n := this ▸ hp_dvd
    exact h_odd h_2_dvd_n
  have hp_three : ¬ 3 ∣ p := by
    intro hd
    have : p = 3 := (Nat.Prime.dvd_iff_eq hp_prime (by decide)).mp hd
    have h_3_dvd_n : 3 ∣ n := this ▸ hp_dvd
    exact h3 h_3_dvd_n
  have hp5 : p ≥ 5 := by
    have : p ≥ 2 := Nat.Prime.two_le hp_prime
    have : p ≠ 2 := by omega
    have : p ≠ 3 := by omega
    have : p ≠ 4 := by
      intro hc
      have : p = 2 := (Nat.Prime.dvd_iff_eq hp_prime (by decide)).mp (by omega)
      omega
    omega
  have h_np : n > p := by
    exact (Nat.not_prime_iff_minFac_lt (by omega)).mp h_not_prime
  have h_pow_gt : 2 ^ p - 1 > 1 := by
    have : 2 ^ p ≥ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hp5
    omega
  rcases Nat.exists_prime_and_dvd h_pow_gt.ne' with ⟨q, hq_prime, hq_dvd⟩
  have h_pow_dvd : 2 ^ p - 1 ∣ 2 ^ n - 1 := by
    rcases hp_dvd with ⟨c, hc⟩
    rw [hc, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ p) c
  have hq_dvd_n : q ∣ 2 ^ n - 1 := dvd_trans hq_dvd h_pow_dvd
  have h_modq' : 1 ≡ q [MOD n] := (h_all q hq_dvd_n).symm
  have hq_gt1 : 1 < q := Nat.Prime.one_lt hq_prime
  have hq_sub_pos : 0 < q - 1 := by omega
  have hq1 : 1 ≤ q := by omega
  have h_dvd : n ∣ q - 1 := (Nat.modEq_iff_dvd' hq1).mp h_modq'
  have h_le_q : n ≤ q - 1 := Nat.le_of_dvd hq_sub_pos h_dvd
  have hq_le_p : q ≤ 2 ^ p - 1 := Nat.le_of_dvd (by omega : 0 < 2 ^ p - 1) hq_dvd
  have h_le : n ≤ 2 ^ p - 2 := by omega
  have h_even_p : ¬ 2 ∣ 2 ^ p - 1 := by
    intro hd
    have h_even : 2 ∣ 2 ^ p := by
      use 2 ^ (p - 1)
      have : p = p - 1 + 1 := by omega
      nth_rw 1 [this]
      ring
    rcases h_even with ⟨Y, hY⟩
    rcases hd with ⟨Z, hZ⟩
    have h_pow_sub : 2 ^ p - (2 ^ p - 1) = 1 := by omega
    rw [hZ] at h_pow_sub
    rw [hY] at h_pow_sub
    omega
  have hq2 : q ≠ 2 := by
    intro h_eq2
    rw [h_eq2] at hq_dvd
    exact h_even_p hq_dvd
  have h_even_q : (q - 1) % 2 = 0 := by
    have : q % 2 = 1 := by
      clear h_pow_gt h_pow_dvd h_np hp5 hp_prime hp_dvd hq_dvd h_modq' h_le_q h_le
      have : q ≥ 2 := Nat.Prime.two_le hq_prime
      have : q % 2 ≠ 0 := by
        intro hc
        have : q = 2 := (Nat.Prime.dvd_iff_eq hq_prime (by decide)).mp (Nat.dvd_of_mod_eq_zero hc)
        exact hq2 this
      omega
    omega
  have h_coprime : Nat.Coprime n 2 := by
    rw [Nat.coprime_two_right]
    have h_odd' : Odd n := by
      have h_mod : n % 2 = 1 := by
        have : n % 2 < 2 := Nat.mod_lt n (by decide)
        have : n % 2 ≠ 0 := by
          intro hc
          have : 2 ∣ n := Nat.dvd_of_mod_eq_zero hc
          exact h_odd this
        omega
      use n / 2
      omega
    exact h_odd'
  have h_2_dvd : 2 ∣ q - 1 := Nat.dvd_of_mod_eq_zero h_even_q
  have h_mul_dvd : n * 2 ∣ q - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime h_dvd h_2_dvd
  have h_le_q2 : n * 2 ≤ q - 1 := Nat.le_of_dvd (by omega) h_mul_dvd
  have h_le_p2 : n * 2 ≤ 2 ^ p - 2 := by omega
  rcases hp_dvd with ⟨m, hm⟩
  have hm_pos : m > 0 := by
    by_contra hc2
    have : m = 0 := by omega
    subst this
    rw [mul_zero] at hm
    omega
  have hm_gt1 : m > 1 := by
    by_contra hc
    have : m = 1 := by omega
    subst this
    rw [mul_one] at hm
    omega
  rcases Nat.exists_prime_and_dvd hm_gt1.ne' with ⟨r, hr_prime, hr_dvd⟩
  have hr_dvd_n : r ∣ p * m := dvd_mul_of_dvd_right hr_dvd p
  have hr_ge_p : p ≤ r := Nat.minFac_le_of_dvd hr_prime.two_le (hm ▸ hr_dvd_n)
  have hm_ge_p : m ≥ p := by
    have hm_pos' : m > 0 := by omega
    have : m ≥ r := Nat.le_of_dvd hm_pos' hr_dvd
    omega
  have h_le_p2' : p * m * 2 ≤ 2 ^ p - 2 := by
    rw [← hm]
    exact h_le_p2
  have h_gcongr : p * p * 2 ≤ p * m * 2 := by gcongr
  have h_np_le : p * p * 2 ≤ 2 ^ p - 2 := by omega
  -- split on p
  have hp_eq : p = 5 ∨ p ≥ 7 := by omega
  rcases hp_eq with hp5_eq | hp7
  · -- p = 5
    rw [hp5_eq] at h_np_le
    omega
  · -- p >= 7
    sorry

lemma prime_factor_gt_n (n : ℕ) (hn : n > 1) (b : ℕ) (hb : b = (n !)^2 + 1) (q : ℕ) (hq_prime : q.Prime) (hdvd : q ∣ b^n - (b-1)^n) :
    q > n := by
  by_contra hc
  have hq_le : q ≤ n := by omega
  have hq_dvd_fact : q ∣ n ! := Nat.dvd_factorial (Nat.Prime.pos hq_prime) hq_le
  have hq_dvd_fact2 : q ∣ (n !)^2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hq_dvd_fact (n !)
  have hb_eq : b = (n !)^2 + 1 := hb
  have hq_dvd_b_sub_one : q ∣ b - 1 := by
    have : b - 1 = (n !)^2 := by omega
    rw [this]
    exact hq_dvd_fact2
  rcases hq_dvd_b_sub_one with ⟨k, hk⟩
  have hb_eq2 : b = q * k + 1 := by omega
  have h_zmod_b : (b : ZMod q) = 1 := by
    rw [hb_eq2]
    push_cast
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  have h_zmod_b_sub_one : ((b - 1 : ℕ) : ZMod q) = 0 := by
    have : b - 1 = q * k := by omega
    rw [this]
    push_cast
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  have hdvd_zmod : ((b^n - (b-1)^n : ℕ) : ZMod q) = 0 := by
    have : q ∣ b^n - (b-1)^n := hdvd
    rcases this with ⟨m, hm⟩
    rw [hm]
    push_cast
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  have h_le : (b-1)^n ≤ b^n := Nat.pow_le_pow_left (by omega) n
  have h_sub_cast : ((b^n - (b-1)^n : ℕ) : ZMod q) = (b : ZMod q)^n - (((b-1 : ℕ) : ZMod q))^n := by
    rw [Nat.cast_sub h_le]
    push_cast
    rfl
  rw [hdvd_zmod] at h_sub_cast
  rw [h_zmod_b, h_zmod_b_sub_one] at h_sub_cast
  have h_one_pow : (1 : ZMod q)^n = 1 := one_pow n
  have h_zero_pow : (0 : ZMod q)^n = 0 := by
    exact zero_pow (by omega)
  rw [h_one_pow, h_zero_pow] at h_sub_cast
  simp at h_sub_cast
  have hq_gt1 : q > 1 := Nat.Prime.one_lt hq_prime
  have : Fact (1 < q) := ⟨hq_gt1⟩
  have h_ne : (0 : ZMod q) ≠ 1 := zero_ne_one
  exact h_ne h_sub_cast


lemma prime_factor_modEq_one (n : ℕ) (hn : n > 1) (b : ℕ) (hb : b = (n !)^2 + 1) (q : ℕ) (hq_prime : q.Prime) (hdvd : q ∣ b^n - (b-1)^n) :
    q ≡ 1 [MOD n] := by
  have hq_gt : q > n := prime_factor_gt_n n hn b hb q hq_prime hdvd
  have h_ne_zero : ((b - 1 : ℕ) : ZMod q) ≠ 0 := by
    intro hc
    have h_dvd : q ∣ b - 1 := by
      exact (ZMod.natCast_eq_zero_iff (b - 1) q).mp hc
    have h_b_sub_one : b - 1 = (n !)^2 := by omega
    rw [h_b_sub_one] at h_dvd
    have hq_le : q ≤ n := by
      have hq_dvd_fact : q ∣ n ! := by
        exact Nat.Prime.dvd_of_dvd_pow hq_prime h_dvd
      rwa [hq_prime.dvd_factorial] at hq_dvd_fact
    omega
  have : Fact (q.Prime) := ⟨hq_prime⟩
  have h_ne_zero' : (b : ZMod q) - 1 ≠ 0 := by
    have h_cast : (b : ZMod q) - 1 = ((b - 1 : ℕ) : ZMod q) := by
      have : b ≥ 1 := by omega
      have h_sub := Nat.cast_sub (R := ZMod q) this
      rw [Nat.cast_one] at h_sub
      exact h_sub.symm
    rw [h_cast]
    exact h_ne_zero
  let u : (ZMod q)ˣ := Units.mk0 ((b : ZMod q) * ((b : ZMod q) - 1)⁻¹) (by
    intro hc
    have h_prod : (b : ZMod q) = 0 ∨ ((b : ZMod q) - 1)⁻¹ = 0 := mul_eq_zero.mp hc
    rcases h_prod with hb0 | hb1
    · -- b = 0
      have hb_dvd : q ∣ b := (ZMod.natCast_eq_zero_iff b q).mp hb0
      have hq_dvd_sub_pow : q ∣ (b - 1)^n := by
        have h_le : (b - 1)^n ≤ b^n := Nat.pow_le_pow_left (by omega) n
        have h_sub : (b - 1)^n = b^n - (b^n - (b - 1)^n) := by omega
        rw [h_sub]
        refine dvd_sub (dvd_pow hb_dvd (by omega)) hdvd
      have hq_dvd_sub : q ∣ b - 1 := hq_prime.dvd_of_dvd_pow hq_dvd_sub_pow
      have hq_dvd_one : q ∣ b - (b - 1) := dvd_sub hb_dvd hq_dvd_sub
      have h_one : b - (b - 1) = 1 := by omega
      rw [h_one] at hq_dvd_one
      exact Nat.Prime.not_dvd_one hq_prime hq_dvd_one
    · -- (b-1)^-1 = 0
      have hb1_ne : ((b : ZMod q) - 1) ≠ 0 := h_ne_zero'
      have h_inv : ((b : ZMod q) - 1)⁻¹ ≠ 0 := by
        exact inv_ne_zero hb1_ne
      exact h_inv hb1
  )
  have h_u_pow : u^n = 1 := by
    rw [← Units.val_eq_one]
    push_cast
    have h_u_val : (u : ZMod q) = (b : ZMod q) * ((b : ZMod q) - 1)⁻¹ := rfl
    rw [h_u_val]
    rw [mul_pow]
    rw [inv_pow]
    have h_eq : (b : ZMod q)^n = ((b : ZMod q) - 1)^n := by
      have h_cast : ((b^n - (b-1)^n : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ q).mpr hdvd
      have h_le : (b-1)^n ≤ b^n := Nat.pow_le_pow_left (by omega) n
      rw [Nat.cast_sub h_le] at h_cast
      have hb_sub_one_cast : (b : ZMod q) - 1 = ((b - 1 : ℕ) : ZMod q) := by
        have : b ≥ 1 := by omega
        have h_sub := Nat.cast_sub (R := ZMod q) this
        rw [Nat.cast_one] at h_sub
        exact h_sub.symm
      rw [Nat.cast_pow, Nat.cast_pow] at h_cast
      rw [← hb_sub_one_cast] at h_cast
      exact sub_eq_zero.mp h_cast
    rw [h_eq]
    exact mul_inv_cancel₀ (pow_ne_zero n h_ne_zero')
  sorry

lemma divisors_of_b_modEq_one (n : ℕ) (hn : n > 1) (b : ℕ) (hb : b = (n !)^2 + 1) (d : ℕ) :
    d ∣ b^n - (b-1)^n → d ≡ 1 [MOD n] := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hd0 : d = 0
    · subst hd0
      have h_pow : (b-1)^n < b^n := Nat.pow_lt_pow_left (by omega) (by omega)
      have : b^n - (b-1)^n = 0 := Nat.eq_zero_of_zero_dvd hd
      omega
    · by_cases hd1 : d = 1
      · subst hd1
        exact Nat.ModEq.refl 1
      · rcases Nat.exists_prime_and_dvd hd1 with ⟨q, hq_prime, hqd⟩
        have hqdvd : q ∣ b^n - (b-1)^n := dvd_trans hqd hd
        have hq_mod : q ≡ 1 [MOD n] := prime_factor_modEq_one n hn b hb q hq_prime hqdvd
        rcases hqd with ⟨d', rfl⟩
        have hd'_pos : d' > 0 := by
          by_contra hc
          have : d' = 0 := by omega
          subst this
          simp at hd0
        have h_lt : d' < q * d' := by
          have hq2 : q ≥ 2 := Nat.Prime.two_le hq_prime
          have hq_gt1 : 1 < q := by omega
          have : d' * 1 < d' * q := Nat.mul_lt_mul_of_pos_left hq_gt1 hd'_pos
          rw [mul_one, mul_comm] at this
          exact this
        have hd'_dvd : d' ∣ b^n - (b-1)^n := dvd_trans (Exists.intro q (mul_comm q d')) hd
        have hd'_mod : d' ≡ 1 [MOD n] := ih d' h_lt hd'_dvd
        have h_mul := Nat.ModEq.mul hq_mod hd'_mod
        rw [mul_one] at h_mul
        exact h_mul

theorem b_mem_S_n (n : ℕ) (hn : n > 1) :
    ((n !)^2 + 1) ∈ { b | b > 1 ∧ let k := b ^ n - (b - 1) ^ n; ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] } := by
  let b := (n !)^2 + 1
  have hb : b = (n !)^2 + 1 := rfl
  have hb_gt1 : b > 1 := by
    have : n ! ≥ 1 := Nat.factorial_pos n
    have : (n !)^2 ≥ 1 := Nat.one_le_pow 2 (n !) (Nat.factorial_pos n)
    omega
  refine ⟨hb_gt1, ?_⟩
  intro k d hd
  exact divisors_of_b_modEq_one n hn b hb d hd



/--
If n is prime, then a(n) = 2. Conjecture: If n is composite, then a(n) > 2.
-/
theorem oeis_321576_conjecture_0 (n : ℕ) (hn : n > 1) :
  (n.Prime → a n = 2) ∧ (¬ n.Prime → a n > 2) := by
  have h_prime_case : n.Prime → a n = 2 := by
    intro hp_prime
    have hp_pos : n > 0 := Nat.Prime.pos hp_prime
    have h_a : a n = sInf { b | b > 1 ∧ ∀ d, d ∣ b ^ n - (b - 1) ^ n → d ≡ 1 [MOD n] } := by
      unfold a
      have h_pos : n > 0 := by omega
      rw [dif_pos h_pos]
    rw [h_a]
    let S_n := { b | b > 1 ∧ ∀ d, d ∣ b ^ n - (b - 1) ^ n → d ≡ 1 [MOD n] }
    have h2_mem : 2 ∈ S_n := by
      change 2 > 1 ∧ ∀ d, d ∣ 2 ^ n - (2 - 1) ^ n → d ≡ 1 [MOD n]
      refine ⟨by decide, ?_⟩
      intro d hd
      have h_pow1 : (2 - 1) ^ n = 1 := by
        have : 2 - 1 = 1 := by decide
        rw [this]
        exact Nat.one_pow n
      rw [h_pow1] at hd
      exact divisors_modEq_one n hp_prime d hd
    have h_nonempty : S_n.Nonempty := ⟨2, h2_mem⟩
    have h_le : sInf S_n ≤ 2 := Nat.sInf_le h2_mem
    have h_mem : sInf S_n ∈ S_n := Nat.sInf_mem h_nonempty
    have h_gt : sInf S_n > 1 := h_mem.1
    have h_eq : sInf S_n = 2 := by omega
    exact h_eq
  refine ⟨h_prime_case, ?_⟩
  intro h_not_prime
  have h_a : a n = sInf { b | b > 1 ∧ ∀ d, d ∣ b ^ n - (b - 1) ^ n → d ≡ 1 [MOD n] } := by
    unfold a
    have h_pos : n > 0 := by omega
    rw [dif_pos h_pos]
  rw [h_a]
  let S_n := { b | b > 1 ∧ ∀ d, d ∣ b ^ n - (b - 1) ^ n → d ≡ 1 [MOD n] }
  have h_nonempty : S_n.Nonempty := ⟨(n !)^2 + 1, b_mem_S_n n hn⟩
  have h_mem : sInf S_n ∈ S_n := Nat.sInf_mem h_nonempty
  have h_gt1 : sInf S_n > 1 := h_mem.1
  have h_ne2 : sInf S_n ≠ 2 := by
    intro hc
    have h2_mem : 2 ∈ S_n := hc ▸ h_mem
    have h2_cond : ∀ d, d ∣ 2 ^ n - (2 - 1) ^ n → d ≡ 1 [MOD n] := h2_mem.2
    have h_pow1 : (2 - 1) ^ n = 1 := by
      have : 2 - 1 = 1 := by decide
      rw [this]
      exact Nat.one_pow n
    rw [h_pow1] at h2_cond
    by_cases h_even : 2 ∣ n
    · have hn_gt2 : n > 2 := by
        have : n ≠ 2 := by
          intro hc2
          subst hc2
          exact h_not_prime (Nat.prime_two)
        omega
      exact even_composite_two_not_mem n hn_gt2 h_even h2_cond
    · by_cases h3 : 3 ∣ n
      · have hn_gt3 : n > 3 := by
          have : n ≠ 3 := by
            intro hc3
            subst hc3
            exact h_not_prime (Nat.prime_three)
          omega
        exact odd_composite_three_dvd_two_not_mem n hn_gt3 h_even h3 h2_cond
      · have hn_gt3 : n > 3 := by
          have : n ≠ 3 := by
            intro hc3
            subst hc3
            exact h_not_prime (Nat.prime_three)
          omega
        exact odd_composite_not_three_dvd_two_not_mem n hn_gt3 h_even h_not_prime h3 h2_cond
  obtain ⟨k, hk⟩ : ∃ k, sInf S_n = k := ⟨sInf S_n, rfl⟩
  rw [hk] at h_gt1
  rw [hk] at h_ne2
  rw [hk]
  omega

