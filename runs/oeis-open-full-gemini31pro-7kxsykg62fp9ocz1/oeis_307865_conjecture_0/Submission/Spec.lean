import FormalConjectures.Util.ProblemImports

open Nat Finset ZMod

/--
A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$. We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.
-/
def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  -- The set of bases is $\{1, 2, \dots, 2n\} = \text{Ico } 1 m$.
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

variable {n : ℕ}

/--
A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.
-/
def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)

theorem one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero {R : Type*} [CommRing R] (p : R) (hp : p ^ 2 = 0) (k : ℕ) :
    (1 + p) ^ k = 1 + k * p := by
  induction' k with k ih
  · simp
  · rw [pow_succ, ih]
    calc (1 + (k : R) * p) * (1 + p)
      _ = 1 + p + k * p + k * p^2 := by ring
      _ = 1 + p + k * p + k * 0 := by rw [hp]
      _ = 1 + (k + 1 : R) * p := by ring
      _ = 1 + (k + 1 : ℕ) * p := by push_cast; rfl

theorem prime_power_contradiction {p k n : ℕ} (hp : p.Prime) (hk : 2 ≤ k)
    (hm : p ^ k = 2 * n + 1)
    (h_pseudo : ∀ x : ZMod (p ^ k), IsUnit x → x ^ n = 1 ∨ x ^ n = -1) : False := by
  have h_dvd : p ^ 2 ∣ p ^ k := pow_dvd_pow p hk
  let f : ZMod (p ^ k) →+* ZMod (p ^ 2) := ZMod.castHom h_dvd (ZMod (p ^ 2))
  have h_coprime : Coprime (1 + p) (p ^ k) := by
    have h1 : Coprime (1 + p) p := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left p)
    exact h1.pow_right k
  have hx_unit : IsUnit (1 + (p : ZMod (p ^ k))) := by
    have : (1 + (p : ZMod (p ^ k))) = ((1 + p : ℕ) : ZMod (p ^ k)) := by push_cast; rfl
    rw [this]
    exact (ZMod.isUnit_iff_coprime (1+p) (p^k)).mpr h_coprime
  rcases h_pseudo (1 + (p : ZMod (p ^ k))) hx_unit with h1 | h2
  · have hf1 : f ((1 + (p : ZMod (p ^ k))) ^ n) = f 1 := congrArg f h1
    simp only [map_pow, map_add, map_one, map_natCast] at hf1
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      have : (p : ZMod (p ^ 2)) ^ 2 = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by push_cast; rfl
      rw [this]
      exact ZMod.natCast_self (p ^ 2)
    have h_binom := one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero (p : ZMod (p ^ 2)) hp2 n
    rw [h_binom] at hf1
    have h_np : (n : ZMod (p ^ 2)) * p = 0 := by
      calc (n : ZMod (p ^ 2)) * p = 1 + n * p - 1 := by ring
        _ = 1 - 1 := by rw [hf1]
        _ = 0 := by ring
    have h_dvd2 : p ^ 2 ∣ n * p := by
      rw [← CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
      have : ((n * p : ℕ) : ZMod (p ^ 2)) = (n : ZMod (p ^ 2)) * p := by push_cast; rfl
      rw [this]
      exact h_np
    have h_dvd_n : p ∣ n := by
      cases' h_dvd2 with c hc
      have hc2 : (p * c) * p = n * p := by
        calc (p * c) * p = p ^ 2 * c := by ring
          _ = n * p := hc.symm
      have h_pos : p > 0 := hp.pos
      have hc3 : p * c = n := Nat.eq_of_mul_eq_mul_right h_pos hc2
      exact ⟨c, hc3.symm⟩
    have hm_eq : p ^ k = 2 * n + 1 := hm
    have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (by omega)
    have hp_dvd_2n : p ∣ 2 * n := dvd_mul_of_dvd_right h_dvd_n 2
    have hp_dvd_1 : p ∣ 1 := by
      have h_diff : 1 = p ^ k - 2 * n := by omega
      rw [h_diff]
      exact Nat.dvd_sub hp_dvd_pk hp_dvd_2n
    exact Nat.Prime.not_dvd_one hp hp_dvd_1
  · have hf1 : f ((1 + (p : ZMod (p ^ k))) ^ n) = f (-1) := congrArg f h2
    simp only [map_pow, map_add, map_one, map_natCast, map_neg] at hf1
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      have : (p : ZMod (p ^ 2)) ^ 2 = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by push_cast; rfl
      rw [this]
      exact ZMod.natCast_self (p ^ 2)
    have h_binom := one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero (p : ZMod (p ^ 2)) hp2 n
    rw [h_binom] at hf1
    have h_2_np : (2 : ZMod (p ^ 2)) + (n : ZMod (p ^ 2)) * p = 0 := by
      calc (2 : ZMod (p ^ 2)) + (n : ZMod (p ^ 2)) * p = 1 + n * p + 1 := by ring
        _ = -1 + 1 := by rw [hf1]
        _ = 0 := by ring
    have h_dvd2 : p ^ 2 ∣ 2 + n * p := by
      rw [← CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
      have : (((2 + n * p) : ℕ) : ZMod (p ^ 2)) = 2 + (n : ZMod (p ^ 2)) * p := by push_cast; rfl
      rw [this]
      exact h_2_np
    have hp_dvd_p2 : p ∣ p ^ 2 := dvd_pow_self p (by omega)
    have hp_dvd_2_np : p ∣ 2 + n * p := dvd_trans hp_dvd_p2 h_dvd2
    have hp_dvd_np : p ∣ n * p := dvd_mul_left p n
    have hp_dvd_2 : p ∣ 2 := by
      have h_diff : 2 = 2 + n * p - n * p := by omega
      rw [h_diff]
      exact Nat.dvd_sub hp_dvd_2_np hp_dvd_np
    have hp_le : p ≤ 2 := Nat.le_of_dvd zero_lt_two hp_dvd_2
    have hp_eq_2 : p = 2 := by
      have hp2 : p ≥ 2 := hp.two_le
      omega
    subst hp_eq_2
    have h_even : Even (2 ^ k) := by
      exact even_pow.mpr ⟨even_two, by omega⟩
    have h_odd : Odd (2 ^ k) := by
      have : 2 ^ k = 2 * n + 1 := hm
      rw [this]
      exact odd_two_mul_add_one n
    rcases h_even with ⟨a, ha⟩
    rcases h_odd with ⟨b, hb⟩
    omega

theorem odd_mod_two_eq_zero {u : ℕ} (hu_odd : Odd u) (hu_pos : 0 < u) (h2 : (2 : ZMod u) = 0) : u = 1 := by
  have h_dvd : u ∣ 2 := by
    rw [← CharP.cast_eq_zero_iff (ZMod u) u]
    exact h2
  have h_le : u ≤ 2 := Nat.le_of_dvd zero_lt_two h_dvd
  rcases hu_odd with ⟨k, hk⟩
  omega

theorem isUnit_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) (hx : IsUnit x) : IsUnit (e x) := by
  rw [isUnit_iff_exists_inv] at hx ⊢
  rcases hx with ⟨x_inv, hx_inv⟩
  use e x_inv
  rw [← map_mul e, hx_inv, map_one e]

theorem isUnit_of_pow_eq_m_one {R : Type*} [CommRing R] {b : R} {n : ℕ} (hn : n > 0) (hbn : b ^ n = -1) : IsUnit b := by
  have H : b * (- (b ^ (n - 1))) = 1 := by
    calc b * (- (b ^ (n - 1))) = - (b ^ 1 * b ^ (n - 1)) := by ring
      _ = - (b ^ (1 + (n - 1))) := by rw [← pow_add]
      _ = - (b ^ n) := by
        have : 1 + (n - 1) = n := by omega
        rw [this]
      _ = - (-1) := by rw [hbn]
      _ = 1 := by ring
  exact ⟨⟨b, (- (b ^ (n - 1))), H, by rw [mul_comm, H]⟩, rfl⟩

theorem crt_contradiction {m u v n : ℕ} (huv : m = u * v) (hcop : Coprime u v)
    (hu : 1 < u) (hv : 1 < v) (hm_odd : Odd m) (hn : n > 0)
    (b : ZMod m) (hbn : b ^ n = -1)
    (h_pseudo : ∀ x : ZMod m, IsUnit x → x ^ n = 1 ∨ x ^ n = -1) : False := by
  subst huv
  have e : ZMod (u * v) ≃+* ZMod u × ZMod v := ZMod.chineseRemainder hcop
  let y := e b
  let x_tup : ZMod u × ZMod v := (y.1, 1)
  let x := e.symm x_tup
  have hx_tup : e x = x_tup := RingEquiv.apply_symm_apply e x_tup
  have hy1 : y.1 ^ n = -1 := by
    have h1 : e (b ^ n) = e (-1) := congrArg e hbn
    simp only [map_pow, map_neg, map_one] at h1
    exact congrArg Prod.fst h1
  have hb_unit : IsUnit b := isUnit_of_pow_eq_m_one hn hbn
  have hy_unit : IsUnit y := isUnit_map_ringEquiv e b hb_unit
  have hx_tup_unit : IsUnit x_tup := by
    rw [isUnit_iff_exists_inv] at hy_unit ⊢
    rcases hy_unit with ⟨y_inv, hy_inv⟩
    use (y_inv.1, 1)
    ext
    · have h_fst : (y * y_inv).1 = (1 : ZMod u × ZMod v).1 := congrArg Prod.fst hy_inv
      exact h_fst
    · exact mul_one 1
  have hx_unit : IsUnit x := isUnit_map_ringEquiv e.symm x_tup hx_tup_unit
  rcases h_pseudo x hx_unit with h1 | h2
  · have he1 : e (x ^ n) = e 1 := congrArg e h1
    simp only [map_pow, map_one] at he1
    have he1_tup : x_tup ^ n = 1 := by
      calc x_tup ^ n = (e x) ^ n := by rw [hx_tup]
        _ = 1 := he1
    have hy1_n : y.1 ^ n = 1 := by
      have hh : (x_tup ^ n).1 = (1 : ZMod u × ZMod v).1 := congrArg Prod.fst he1_tup
      exact hh
    rw [hy1] at hy1_n
    have h_u_div_2 : (2 : ZMod u) = 0 := by
      calc (2 : ZMod u) = 1 + 1 := by ring
        _ = (-1 : ZMod u) + 1 := congrArg (· + 1) hy1_n.symm
        _ = 0 := by ring
    have hu_odd : Odd u := hm_odd.of_mul_left
    have hu_pos : 0 < u := by omega
    have hu_eq_1 := odd_mod_two_eq_zero hu_odd hu_pos h_u_div_2
    omega
  · have he1 : e (x ^ n) = e (-1) := congrArg e h2
    simp only [map_pow, map_neg, map_one] at he1
    have he1_tup : x_tup ^ n = -1 := by
      calc x_tup ^ n = (e x) ^ n := by rw [hx_tup]
        _ = -1 := he1
    have h1_n : (1 : ZMod v) ^ n = -1 := by
      have hh : (x_tup ^ n).2 = (-1 : ZMod u × ZMod v).2 := congrArg Prod.snd he1_tup
      exact hh
    simp only [one_pow] at h1_n
    have h_v_div_2 : (2 : ZMod v) = 0 := by
      calc (2 : ZMod v) = 1 + 1 := by ring
        _ = (-1 : ZMod v) + 1 := congrArg (· + 1) h1_n
        _ = 0 := by ring
    have hv_odd : Odd v := hm_odd.of_mul_right
    have hv_pos : 0 < v := by omega
    have hv_eq_1 := odd_mod_two_eq_zero hv_odd hv_pos h_v_div_2
    omega

theorem padic_props {p m : ℕ} (hp : p.Prime) (hm : m > 0) (hpm : p ∣ m) :
    let k := padicValNat p m
    let v := m / p ^ k
    k > 0 ∧ m = p ^ k * v ∧ Coprime (p ^ k) v := by
  intro k v
  haveI : Fact p.Prime := ⟨hp⟩
  have hk_def : k = padicValNat p m := rfl
  have hm_neq : m ≠ 0 := by omega
  have h_pk_dvd : p ^ k ∣ m := by
    rw [padicValNat_dvd_iff k m]
    right
    rfl
  have h_m_eq : m = p ^ k * v := by
    calc m = m / p ^ k * p ^ k := (Nat.div_mul_cancel h_pk_dvd).symm
      _ = p ^ k * (m / p ^ k) := mul_comm _ _
  have h_k_pos : k > 0 := by
    have : p ^ 1 ∣ m := by rw [pow_one]; exact hpm
    have : 1 ≤ k := by
      have hh := (padicValNat_dvd_iff 1 m).mp this
      rcases hh with h_zero | h_le
      · exfalso; exact hm_neq h_zero
      · exact h_le
    omega
  have hp_not_dvd_v : ¬ p ∣ v := by
    intro hp_dvd_v
    have : p ^ (k + 1) ∣ m := by
      rw [h_m_eq, pow_succ]
      exact mul_dvd_mul_left (p ^ k) hp_dvd_v
    have : k + 1 ≤ k := by
      have hh := (padicValNat_dvd_iff (k + 1) m).mp this
      rcases hh with h_zero | h_le
      · exfalso; exact hm_neq h_zero
      · exact h_le
    omega
  have h_coprime : Coprime (p ^ k) v := by
    apply Nat.coprime_of_dvd
    intro q hq hq_dvd_pk
    have hqp : q = p := by
      have : q ∣ p := Nat.Prime.dvd_of_dvd_pow hq hq_dvd_pk
      exact (Nat.Prime.eq_one_or_self_of_dvd hp q this).resolve_left (Nat.Prime.ne_one hq)
    subst hqp
    exact hp_not_dvd_v
  exact ⟨h_k_pos, h_m_eq, h_coprime⟩

/--
oeis_307865_conjecture_0: Conjecture: if $2n+1$ is an absolute Euler pseudoprime, then $a(n) = 0$.
Note: this conjecture trivially holds for $n=0$ since $2 \cdot 0 + 1 = 1$, which is not an absolute Euler pseudoprime.
For a meaningful statement, one usually considers $n>3$.
-/
theorem oeis_307865_conjecture_0 (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
  let m := 2 * n + 1
  have hm : m = 2 * n + 1 := rfl
  have hm_odd : Odd m := odd_two_mul_add_one n
  have hm_gt_1 : m > 1 := h.1
  have h_not_prime : ¬ Nat.Prime m := h.2.1
  have hn_pos : n > 0 := by omega
  have hm_pos : m > 0 := by omega
  have h_pseudo : ∀ x : ZMod m, IsUnit x → x ^ n = 1 ∨ x ^ n = -1 := by
    intro x hx
    have h_coprime : Coprime x.val m := by
      have : x = ((x.val : ℕ) : ZMod m) := (ZMod.natCast_zmod_val x).symm
      rw [this] at hx
      exact (ZMod.isUnit_iff_coprime x.val m).mp hx
    have h_val : (x.val : ZMod m) = x := ZMod.natCast_zmod_val x
    have h_sub : (m - 1) / 2 = n := by omega
    rcases h.2.2 x.val h_coprime with h1 | h2
    · left; rw [h_val, h_sub] at h1; exact h1
    · right; rw [h_val, h_sub] at h2; exact h2
  by_contra h_neq
  have h_pos : 0 < ((Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = -1)).card := Nat.pos_of_ne_zero h_neq
  rcases card_pos.mp h_pos with ⟨b_nat, hb_mem⟩
  rw [mem_filter] at hb_mem
  have hb_ico : b_nat ∈ Ico 1 m := hb_mem.1
  have hbn : (b_nat : ZMod m) ^ n = -1 := hb_mem.2
  let b : ZMod m := b_nat
  have hbn_b : b ^ n = -1 := hbn
  have h_exists_p : ∃ p, p.Prime ∧ p ∣ m := Nat.exists_prime_and_dvd hm_gt_1.ne'
  rcases h_exists_p with ⟨p, hp, hp_dvd⟩
  have hp_props := padic_props hp hm_pos hp_dvd
  let k := padicValNat p m
  let v := m / p ^ k
  rcases hp_props with ⟨hk_pos, h_m_eq, h_coprime⟩
  have hv_gt_0 : 1 ≤ v := Nat.pos_of_ne_zero (by intro h; have : m / p ^ k = 0 := h; rw [this, mul_zero] at h_m_eq; omega)
  rcases eq_or_lt_of_le hv_gt_0 with hv_eq | hv_gt
  · have hv1 : v = 1 := hv_eq.symm
    have hm_pk : p ^ k = m := by
      calc p ^ k = p ^ k * 1 := by ring
        _ = p ^ k * v := by rw [← hv1]
        _ = m := h_m_eq.symm
    have hk_ge_2 : 2 ≤ k := by
      by_contra hk_lt
      have hk1 : k = 1 := by omega
      have hp_m : p = m := by
        calc p = p ^ 1 := by ring
          _ = p ^ k := by rw [hk1]
          _ = m := hm_pk
      subst hp_m
      exact h_not_prime hp
    have h_pseudo_pk : ∀ x : ZMod (p ^ k), IsUnit x → x ^ n = 1 ∨ x ^ n = -1 := by
      intro x hx
      let e : ZMod m ≃+* ZMod (p ^ k) := ZMod.ringEquivCongr hm_pk.symm
      have he_unit : IsUnit (e.symm x) := isUnit_map_ringEquiv e.symm x hx
      rcases h_pseudo (e.symm x) he_unit with h1 | h2
      · left
        have := congrArg e h1
        simp only [map_pow, map_one] at this
        have h_e_symm : e (e.symm x) = x := RingEquiv.apply_symm_apply e x
        rw [h_e_symm] at this
        exact this
      · right
        have := congrArg e h2
        simp only [map_pow, map_neg, map_one] at this
        have h_e_symm : e (e.symm x) = x := RingEquiv.apply_symm_apply e x
        rw [h_e_symm] at this
        exact this
    exact prime_power_contradiction hp hk_ge_2 hm_pk h_pseudo_pk
  · let u := p ^ k
    have hu_gt_1 : 1 < u := Nat.one_lt_pow hk_pos.ne' hp.one_lt
    exact crt_contradiction h_m_eq h_coprime hu_gt_1 hv_gt hm_odd hn_pos b hbn_b h_pseudo

theorem oeis_307865_conjecture_0.disproof : ¬ (type_of% @oeis_307865_conjecture_0) := sorry
