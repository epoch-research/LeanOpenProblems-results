import FormalConjectures.Util.ProblemImports

open Nat

set_option maxHeartbeats 400000

lemma zmod_pow_neg_one_of_dvd {a e N p : ℕ} [NeZero N] (hp : p.Prime) (hdvd : p ∣ N)
    (ha : (a : ZMod N) ^ e = -1) : (a : ZMod p) ^ e = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzero : ((a ^ e + 1 : ℕ) : ZMod N) = 0 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ha, neg_add_cancel]
  have hdivN : N ∣ a ^ e + 1 := (ZMod.natCast_eq_zero_iff (a ^ e + 1) N).mp hzero
  have hdivp : p ∣ a ^ e + 1 := dvd_trans hdvd hdivN
  have : ((a ^ e + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (a ^ e + 1) p).mpr hdivp
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at this
  exact add_eq_zero_iff_eq_neg.mp this

lemma odd_coprime_two {k : ℕ} (h : Odd k) : Nat.Coprime k 2 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  exact h.not_two_dvd_nat

lemma one_ne_neg_one_of_odd_prime {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (1 : ZMod p) ≠ -1 := by
  intro h
  have hsum : (1 + 1 : ZMod p) = 0 := by
    have := congrArg (fun x : ZMod p => x + 1) h
    simpa using this
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have : ((2 : ℕ) : ZMod p) = 1 + 1 := by norm_num
    rw [this, hsum]
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2'
  · exact (Fact.out (p := p.Prime)).ne_one h1
  · exact hodd h2'

lemma two_pow_dvd_orderOf (a : ℕ) (p k n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hkodd : Odd k)
    (ha : (a : ZMod p) ^ (k * 2 ^ (n - 1)) = -1)
    (hne : (1 : ZMod p) ≠ -1) :
    2 ^ n ∣ orderOf (a : ZMod p) := by
  let d : ℕ := orderOf (a : ZMod p)
  have hd_dvd : d ∣ k * 2 ^ n := by
    change orderOf (a : ZMod p) ∣ k * 2 ^ n
    rw [orderOf_dvd_iff_pow_eq_one]
    have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    rw [← hsucc, pow_succ, ← mul_assoc, pow_mul, ha, neg_one_sq]
  have hd_ndvd : ¬ d ∣ k * 2 ^ (n - 1) := by
    intro h
    have h1 : (a : ZMod p) ^ (k * 2 ^ (n - 1)) = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := (a : ZMod p))).mp h
    exact hne (h1.symm.trans ha)
  have dpos : d ≠ 0 := by
    intro h0
    have : ∀ n : ℕ, 0 < n → (a : ZMod p) ^ n ≠ 1 :=
      (orderOf_eq_zero_iff').mp h0
    have hpow1 : (a : ZMod p) ^ (k * 2 ^ n) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp hd_dvd
    have hpos : 0 < k * 2 ^ n :=
      Nat.mul_pos (Odd.pos hkodd) (pow_pos (by decide) n)
    exact this _ hpos hpow1
  obtain ⟨v, t, htodd, hdt⟩ := Nat.exists_eq_two_pow_mul_odd dpos
  have ht_k : t ∣ k := by
    have h1 : t ∣ d := by
      rw [hdt]; exact dvd_mul_left t _
    have h2 : t ∣ 2 ^ n * k := by
      rw [mul_comm]
      exact dvd_trans h1 hd_dvd
    have hcop : Nat.Coprime t (2 ^ n) :=
      (odd_coprime_two htodd).pow_right n
    exact hcop.dvd_of_dvd_mul_left h2
  have hv : n ≤ v := by
    by_contra hlt
    have hvle : v ≤ n - 1 := Nat.le_sub_one_of_lt (lt_of_not_ge hlt)
    have : d ∣ k * 2 ^ (n - 1) := by
      rw [hdt, mul_comm k]
      exact mul_dvd_mul (Nat.pow_dvd_pow 2 hvle) ht_k
    exact hd_ndvd this
  have : 2 ^ n ∣ 2 ^ v := Nat.pow_dvd_pow 2 hv
  have : 2 ^ n ∣ d := by
    rw [hdt]
    exact dvd_mul_of_dvd_left this t
  exact this

lemma proth_prime_ne_two {k n N p : ℕ} (hn : 0 < n) (hkodd : Odd k)
    (hN : N = k * 2 ^ n + 1) (hp : p.Prime) (hdvd : p ∣ N) : p ≠ 2 := by
  intro h2
  subst h2
  have hNodd : ¬ 2 ∣ N := by
    have heven : 2 ∣ k * 2 ^ n := by
      have : 2 ∣ 2 ^ n := (dvd_pow_self 2 (Nat.ne_of_gt hn))
      exact dvd_mul_of_dvd_right this k
    have : N = k * 2 ^ n + 1 := hN
    intro h
    have : 2 ∣ 1 := (Nat.dvd_add_right heven).mp (hN ▸ h)
    exact (by decide : ¬ 2 ∣ 1) this
  exact hNodd hdvd

lemma proth_prime_factor_large {k n a N p : ℕ} [NeZero N]
    (hn : 0 < n) (hkodd : Odd k) (hN : N = k * 2 ^ n + 1)
    (ha : (a : ZMod N) ^ ((N - 1) / 2) = -1)
    (hp : p.Prime) (hdvd : p ∣ N) : 2 ^ n + 1 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpne2 : p ≠ 2 := proth_prime_ne_two hn hkodd hN hp hdvd
  have hN1 : N - 1 = k * 2 ^ n := by
    have : 1 ≤ N := by
      rw [hN]; exact Nat.succ_le_succ (Nat.zero_le _)
    omega
  have hhalf : (N - 1) / 2 = k * 2 ^ (n - 1) := by
    have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    have : k * 2 ^ n = (k * 2 ^ (n - 1)) * 2 := by
      calc
        k * 2 ^ n = k * 2 ^ ((n - 1) + 1) := by rw [hsucc]
        _ = k * (2 ^ (n - 1) * 2) := by rw [pow_succ]
        _ = k * 2 ^ (n - 1) * 2 := by rw [mul_assoc]
    rw [hN1, this, Nat.mul_div_cancel _ two_pos]
  have ha' : (a : ZMod p) ^ (k * 2 ^ (n - 1)) = -1 := by
    rw [← hhalf]
    exact zmod_pow_neg_one_of_dvd hp hdvd ha
  have hne : (1 : ZMod p) ≠ -1 := one_ne_neg_one_of_odd_prime hpne2
  have hpow : 2 ^ n ∣ orderOf (a : ZMod p) :=
    two_pow_dvd_orderOf a p k n hn hkodd ha' hne
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h0
    have hpos : k * 2 ^ (n - 1) ≠ 0 :=
      Nat.mul_ne_zero (Odd.pos hkodd).ne' (pow_ne_zero _ (by decide))
    rw [h0, zero_pow hpos] at ha'
    have : (0 : ZMod p) = -1 := ha'
    have : (1 : ZMod p) = 0 := by
      have := congrArg (fun x : ZMod p => x + 1) this
      simpa using this
    have : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by
      exact_mod_cast this)
    exact hp.not_dvd_one this
  have hdivp1 : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  have : 2 ^ n ∣ p - 1 := dvd_trans hpow hdivp1
  have : 2 ^ n ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) this
  omega

theorem proth_primality {k n a N : ℕ} (hn : 0 < n) (hkodd : Odd k) (hklt : k < 2 ^ n)
    (hN : N = k * 2 ^ n + 1)
    (ha : (a : ZMod N) ^ ((N - 1) / 2) = -1) : Nat.Prime N := by
  have hNgt : 1 < N := by
    rw [hN]
    have : 0 < k * 2 ^ n := Nat.mul_pos (Odd.pos hkodd) (pow_pos (by decide) n)
    omega
  haveI : NeZero N := ⟨by omega⟩
  by_contra hnp
  have hminP : Nat.Prime N.minFac := Nat.minFac_prime (show N ≠ 1 by omega)
  have hge : 2 ^ n + 1 ≤ N.minFac :=
    proth_prime_factor_large hn hkodd hN ha hminP (Nat.minFac_dvd N)
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (Nat.zero_lt_of_lt hNgt) hnp
  have hNbound : N < (2 ^ n + 1) ^ 2 := by
    rw [hN, add_sq]
    have hmul : k * 2 ^ n < 2 ^ n * 2 ^ n :=
      Nat.mul_lt_mul_of_pos_right hklt (pow_pos (by decide) n)
    have : 0 < 2 * 2 ^ n := Nat.mul_pos two_pos (pow_pos (by decide) n)
    -- N = k*2^n + 1 < 2^n*2^n + 1
    -- (2^n+1)^2 = 2^{2n} + 2*2^n + 1
    have : k * 2 ^ n + 1 < 2 ^ n * 2 ^ n + 2 * 2 ^ n + 1 := by
      have : k * 2 ^ n < 2 ^ n * 2 ^ n + 2 * 2 ^ n := by omega
      omega
    simpa [pow_two] using this
  have : (2 ^ n + 1) ^ 2 ≤ N.minFac ^ 2 := Nat.pow_le_pow_left hge 2
  omega
