import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

/--
A228304: The sequence $a(n)$ is defined by the alternating sum of fourth powers of binomial coefficients.
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k$$
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

/--
A228304 c(n) sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}$$
-/
def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

lemma a_cast {R : Type*} [Ring R] (n : ℕ) :
    (a n : R) = ∑ k ∈ range (n + 1), (-1 : R) ^ k * (choose n k : R) ^ 4 := by
  simp only [a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]

lemma c_cast {R : Type*} [Ring R] (n : ℕ) :
    (c n : R) =
      ∑ k ∈ range (n + 1),
        (-1 : R) ^ k * (choose n k : R) ^ 2 * (choose (2 * k) k : R) *
          (choose (2 * (n - k)) (n - k) : R) := by
  simp only [c, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]

lemma choose_mod_mul_div (p n k : ℕ) [Fact p.Prime] :
    (choose n k : ZMod p) =
      (choose (n % p) (k % p) : ZMod p) * (choose (n / p) (k / p) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  simpa [Int.cast_mul, Int.cast_natCast] using h

lemma choose_pred_prime (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    (choose (p - 1) k : ZMod p) = (-1) ^ k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hk' : k < p := lt_trans (lt_add_one k) hk
    have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
    have hdiv : (choose p (k + 1) : ZMod p) = 0 := by
      have : p ∣ choose p (k + 1) :=
        Nat.Prime.dvd_choose_self (Fact.out (p := p.Prime)) (Nat.succ_ne_zero k) hk
      exact (ZMod.natCast_eq_zero_iff _ _).mpr this
    have hpascal : choose p (k + 1) = choose (p - 1) k + choose (p - 1) (k + 1) := by
      have h := choose_succ_succ (p - 1) k
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.sub_add_cancel hppos] at h
      exact h
    have hcast : (choose (p - 1) (k + 1) : ZMod p) + (choose (p - 1) k : ZMod p) = 0 := by
      rw [← Nat.cast_add, add_comm, ← hpascal, hdiv]
    rw [add_eq_zero_iff_eq_neg] at hcast
    rw [hcast, ih hk', _root_.pow_succ']
    ring

lemma nat_mod_eq_sub {p n : ℕ} (h1 : p ≤ n) (h2 : n < 2 * p) : n % p = n - p := by
  have hlt : n - p < p := Nat.sub_lt_left_of_lt_add h1 (by simpa [two_mul] using h2)
  calc
    n % p = (p + (n - p)) % p := by rw [Nat.add_sub_of_le h1]
    _ = (n - p) % p := by rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    _ = n - p := Nat.mod_eq_of_lt hlt

lemma centralBinom_mod_zero (p k : ℕ) [Fact p.Prime] (hpk : p ≤ 2 * k) (hk : k < p) :
    (choose (2 * k) k : ZMod p) = 0 := by
  have h2klt : 2 * k < 2 * p := by nlinarith
  have hdiv : (2 * k) / p = 1 := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · simpa [Nat.mul_one] using hpk
    · simpa [Nat.mul_two] using h2klt
  have hmod : (2 * k) % p = 2 * k - p := nat_mod_eq_sub hpk h2klt
  have hkdiv : k / p = 0 := Nat.div_eq_of_lt hk
  have hkmod : k % p = k := Nat.mod_eq_of_lt hk
  rw [choose_mod_mul_div, hdiv, hmod, hkdiv, hkmod, choose_zero_right]
  simp [choose_eq_zero_of_lt (show 2 * k - p < k by omega)]

lemma centralBinom_prime_add (p m : ℕ) [Fact p.Prime] (hm : m < p) :
    (choose (2 * p + 2 * m) (p + m) : ZMod p) = 2 * (choose (2 * m) m : ZMod p) := by
  have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hnp : (2 * p + 2 * m) % p = (2 * m) % p := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
  have hnd : (2 * p + 2 * m) / p = 2 + (2 * m) / p := by
    rw [Nat.add_comm (2 * p), mul_comm 2 p, Nat.add_mul_div_left _ _ hppos, add_comm]
  have hkp : (p + m) % p = m := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm]
  have hkd : (p + m) / p = 1 := by
    rw [Nat.add_div_left m hppos, Nat.div_eq_of_lt hm]
  rw [choose_mod_mul_div, hnp, hnd, hkp, hkd]
  by_cases h2m : 2 * m < p
  · rw [Nat.mod_eq_of_lt h2m, Nat.div_eq_of_lt h2m]
    simp
    ring
  · have hge : p ≤ 2 * m := le_of_not_gt h2m
    have h2mlt : 2 * m < 2 * p := by nlinarith
    have hdiv1 : (2 * m) / p = 1 := Nat.div_eq_of_lt_le (by simpa using hge) (by simpa [mul_two] using h2mlt)
    have hmod1 : (2 * m) % p = 2 * m - p := nat_mod_eq_sub hge h2mlt
    rw [hdiv1, hmod1, centralBinom_mod_zero p m hge hm]
    simp [choose_eq_zero_of_lt (show 2 * m - p < m by omega)]

lemma choose_prime_add (p r k : ℕ) [Fact p.Prime] (hr : r < p) (hk : k < 2 * p) :
    (choose (p + r) k : ZMod p) =
      if k < p then (choose r k : ZMod p) else (choose r (k - p) : ZMod p) := by
  have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hnp : (p + r) % p = r := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hr]
  have hnd : (p + r) / p = 1 := by
    rw [Nat.add_div_left r hppos, Nat.div_eq_of_lt hr]
  rw [choose_mod_mul_div, hnp, hnd]
  split_ifs with hkp
  · rw [Nat.mod_eq_of_lt hkp, Nat.div_eq_of_lt hkp, choose_zero_right]
    simp
  · have hkge : p ≤ k := le_of_not_gt hkp
    have hkd : k / p = 1 := Nat.div_eq_of_lt_le (by simpa using hkge) (by simpa [mul_two] using hk)
    have hkm : k % p = k - p := nat_mod_eq_sub hkge hk
    rw [hkd, hkm, choose_one_right]
    simp

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2
  · exact (Fact.out (p := p.Prime)).ne_one h1
  · exact h_odd h2

lemma neg_one_ne_one_zmod (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  apply two_ne_zero_zmod p h_odd
  rw [show (2 : ZMod p) = 1 - (-1) by ring, h, sub_self]

lemma a_pred (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (a (p - 1) : ZMod p) = 1 := by
  have hodd : Odd p := (Nat.Prime.eq_two_or_odd' (Fact.out (p := p.Prime))).resolve_left h_odd
  have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hppos
  rw [a_cast, hpred]
  have hsum : ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 4 =
      ∑ k ∈ range p, (-1 : ZMod p) ^ k := by
    refine sum_congr rfl ?_
    intro k hk
    rw [mem_range] at hk
    rw [choose_pred_prime p k hk]
    have hpow : ((-1 : ZMod p) ^ k) ^ 4 = 1 := by
      rw [← pow_mul]
      exact Even.neg_one_pow ⟨k * 2, by ring⟩
    rw [hpow, mul_one]
  rw [hsum, geom_sum_eq (neg_one_ne_one_zmod p h_odd), hodd.neg_one_pow]
  have hden : (-1 - 1 : ZMod p) ≠ 0 := by
    intro h
    apply two_ne_zero_zmod p h_odd
    rw [show (2 : ZMod p) = -(-1 - 1) by ring, h, neg_zero]
  exact div_self hden

lemma a_of_ge (p n : ℕ) [Fact p.Prime] (h_odd : p ≠ 2)
    (hpn : p ≤ n) (hn : n ≤ 2 * p - 2) : (a n : ZMod p) = 0 := by
  have hodd : Odd p := (Nat.Prime.eq_two_or_odd' (Fact.out (p := p.Prime))).resolve_left h_odd
  have hptwo : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  set r := n - p with hrdef
  have hn' : n = p + r := Nat.add_sub_of_le hpn |>.symm
  have hrlt : r < p := by
    have : n - p ≤ p - 2 := by
      have : n ≤ 2 * p - 2 := hn
      omega
    omega
  have hrle : r + 1 ≤ p := Nat.succ_le_of_lt hrlt
  rw [a_cast, hn']
  have hsplit :=
    (sum_range_add_sum_Ico
      (fun k => (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4)
      (show p ≤ p + r + 1 by omega)).symm
  rw [hsplit]
  have hfirst :
      ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4 =
        (a r : ZMod p) := by
    have hcongr :
        ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4 =
          ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4 := by
      refine sum_congr rfl ?_
      intro k hk
      rw [mem_range] at hk
      have hk2 : k < 2 * p := by omega
      rw [choose_prime_add p r k hrlt hk2]
      simp [hk]
    rw [hcongr, a_cast]
    have hsub :=
      (sum_range_add_sum_Ico
        (fun k => (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4) hrle).symm
    rw [hsub]
    have hz : ∑ k ∈ Ico (r + 1) p, (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4 = 0 := by
      refine sum_eq_zero ?_
      intro k hk
      rw [mem_Ico] at hk
      simp [choose_eq_zero_of_lt (lt_of_succ_le hk.1)]
    rw [hz, add_zero]
  have hsecond :
      ∑ k ∈ Ico p (p + r + 1), (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4 =
        -(a r : ZMod p) := by
    rw [sum_Ico_eq_sum_range]
    have hlen : p + r + 1 - p = r + 1 := by omega
    rw [hlen]
    have hcongr :
        ∑ x ∈ range (r + 1),
            (-1 : ZMod p) ^ (p + x) * (choose (p + r) (p + x) : ZMod p) ^ 4 =
          ∑ x ∈ range (r + 1), -((-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 4) := by
      refine sum_congr rfl ?_
      intro x hx
      rw [mem_range] at hx
      have hxlt : p + x < 2 * p := by omega
      rw [choose_prime_add p r (p + x) hrlt hxlt]
      have : ¬ p + x < p := by omega
      simp only [this, ↓reduceIte]
      have hx' : p + x - p = x := by omega
      rw [hx', pow_add, hodd.neg_one_pow]
      ring
    rw [hcongr, sum_neg_distrib, a_cast]
  rw [hfirst, hsecond, add_neg_cancel]

lemma c_pred (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (c (p - 1) : ZMod p) = (-1) ^ ((p - 1) / 2) := by
  have hodd : Odd p := (Nat.Prime.eq_two_or_odd' (Fact.out (p := p.Prime))).resolve_left h_odd
  have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hppos
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by
    have := Nat.two_mul_div_two_add_one_of_odd hodd
    omega
  have hmem : (p - 1) / 2 ∈ range p := by
    rw [mem_range]
    omega
  rw [c_cast, hpred]
  have hterm : ∀ k ∈ range p,
      (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 2 *
          (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) =
        (-1 : ZMod p) ^ k * (choose (2 * k) k : ZMod p) *
          (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) := by
    intro k hk
    rw [mem_range] at hk
    rw [choose_pred_prime p k hk]
    have : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
      rw [← pow_mul]
      exact Even.neg_one_pow ⟨k, by ring⟩
    rw [this, mul_one]
  refine (sum_congr rfl hterm).trans ?_
  rw [sum_eq_single ((p - 1) / 2)]
  · have hk : (p - 1) / 2 < p := by omega
    have hrest : p - 1 - (p - 1) / 2 = (p - 1) / 2 := by omega
    simp only [hhalf, hrest]
    have hc : (choose (p - 1) ((p - 1) / 2) : ZMod p) = (-1) ^ ((p - 1) / 2) :=
      choose_pred_prime p ((p - 1) / 2) hk
    rw [hc]
    have hsq : ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
      rw [← pow_mul]
      exact Even.neg_one_pow ⟨(p - 1) / 2, by ring⟩
    rw [mul_assoc, ← pow_two, hsq, mul_one]
  · intro k hk hne
    rw [mem_range] at hk
    by_cases hlt : k < (p - 1) / 2
    · have hm : p - 1 - k < p := by omega
      have h2 : p ≤ 2 * (p - 1 - k) := by omega
      rw [centralBinom_mod_zero p (p - 1 - k) h2 hm, mul_zero]
    · have hgt : (p - 1) / 2 < k := Nat.lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      have h2 : p ≤ 2 * k := by omega
      rw [centralBinom_mod_zero p k h2 hk, mul_zero, zero_mul]
  · intro h
    exact (h hmem).elim

lemma c_of_ge (p n : ℕ) [Fact p.Prime] (h_odd : p ≠ 2)
    (hpn : p ≤ n) (hn : n ≤ 2 * p - 2) : (c n : ZMod p) = 0 := by
  have hodd : Odd p := (Nat.Prime.eq_two_or_odd' (Fact.out (p := p.Prime))).resolve_left h_odd
  have hptwo : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  set r := n - p with hrdef
  have hn' : n = p + r := (Nat.add_sub_of_le hpn).symm
  have hrlt : r < p := by
    have : n - p ≤ p - 2 := by
      have : n ≤ 2 * p - 2 := hn
      omega
    omega
  have hrle : r + 1 ≤ p := Nat.succ_le_of_lt hrlt
  rw [c_cast, hn']
  have hsplit :=
    (sum_range_add_sum_Ico
      (fun k =>
        (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 *
          (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p))
      (show p ≤ p + r + 1 by omega)).symm
  rw [hsplit]
  have hfirst :
      ∑ k ∈ range p,
          (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 *
            (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
        2 * (c r : ZMod p) := by
    have h1 :
        ∑ k ∈ range p,
            (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 *
              (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
          ∑ k ∈ range (r + 1),
            (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 *
              (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) := by
      have hsub :=
        (sum_range_add_sum_Ico
          (fun k =>
            (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 *
              (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p))
          hrle).symm
      rw [hsub]
      have hz : ∑ k ∈ Ico (r + 1) p,
          (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 *
            (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) = 0 := by
        refine sum_eq_zero ?_
        intro k hk
        rw [mem_Ico] at hk
        have hk2 : k < 2 * p := by omega
        rw [choose_prime_add p r k hrlt hk2]
        simp [hk.2, choose_eq_zero_of_lt (lt_of_succ_le hk.1)]
      have hcong : ∑ k ∈ range (r + 1),
          (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 *
            (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
          ∑ k ∈ range (r + 1),
            (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 *
              (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) := by
        refine sum_congr rfl ?_
        intro k hk
        rw [mem_range] at hk
        have hk2 : k < 2 * p := by omega
        rw [choose_prime_add p r k hrlt hk2]
        simp [show k < p by omega]
      rw [hz, add_zero, hcong]
    rw [h1]
    have h2 :
        ∑ k ∈ range (r + 1),
            (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 *
              (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
          ∑ k ∈ range (r + 1),
            (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 *
              (choose (2 * k) k : ZMod p) * (2 * (choose (2 * (r - k)) (r - k) : ZMod p)) := by
      refine sum_congr rfl ?_
      intro k hk
      rw [mem_range] at hk
      have hsub : p + r - k = p + (r - k) := by omega
      rw [hsub, show 2 * (p + (r - k)) = 2 * p + 2 * (r - k) by ring]
      have : (choose (2 * p + 2 * (r - k)) (p + (r - k)) : ZMod p) =
          2 * (choose (2 * (r - k)) (r - k) : ZMod p) :=
        centralBinom_prime_add p (r - k) (by omega)
      rw [this]
    rw [h2]
    have : ∑ k ∈ range (r + 1),
        (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 *
          (choose (2 * k) k : ZMod p) * (2 * (choose (2 * (r - k)) (r - k) : ZMod p)) =
        2 * (c r : ZMod p) := by
      rw [c_cast]
      have hrearr : ∑ k ∈ range (r + 1),
          (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 *
            (choose (2 * k) k : ZMod p) * (2 * (choose (2 * (r - k)) (r - k) : ZMod p)) =
          ∑ k ∈ range (r + 1),
            2 * ((-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 *
              (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p)) := by
        refine sum_congr rfl ?_
        intro k hk
        ring
      rw [hrearr, ← mul_sum]
    exact this
  have hsecond :
      ∑ k ∈ Ico p (p + r + 1),
          (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 *
            (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
        -(2 * (c r : ZMod p)) := by
    rw [sum_Ico_eq_sum_range]
    have hlen : p + r + 1 - p = r + 1 := by omega
    rw [hlen]
    have hcongr :
        ∑ x ∈ range (r + 1),
            (-1 : ZMod p) ^ (p + x) * (choose (p + r) (p + x) : ZMod p) ^ 2 *
              (choose (2 * (p + x)) (p + x) : ZMod p) *
                (choose (2 * (p + r - (p + x))) (p + r - (p + x)) : ZMod p) =
          ∑ x ∈ range (r + 1),
            -((-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 *
              (2 * (choose (2 * x) x : ZMod p)) *
                (choose (2 * (r - x)) (r - x) : ZMod p)) := by
      refine sum_congr rfl ?_
      intro x hx
      rw [mem_range] at hx
      have hxlt : p + x < 2 * p := by omega
      rw [choose_prime_add p r (p + x) hrlt hxlt]
      have : ¬ p + x < p := by omega
      simp only [this, ↓reduceIte]
      have hx' : p + x - p = x := by omega
      have hrest : p + r - (p + x) = r - x := by omega
      rw [hx', hrest, pow_add, hodd.neg_one_pow]
      have hcb : (choose (2 * p + 2 * x) (p + x) : ZMod p) = 2 * (choose (2 * x) x : ZMod p) :=
        centralBinom_prime_add p x (by omega)
      rw [show 2 * (p + x) = 2 * p + 2 * x by ring, hcb]
      ring
    rw [hcongr, sum_neg_distrib]
    have : ∑ x ∈ range (r + 1),
        (-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 *
          (2 * (choose (2 * x) x : ZMod p)) * (choose (2 * (r - x)) (r - x) : ZMod p) =
        2 * (c r : ZMod p) := by
      rw [c_cast]
      have hrearr : ∑ x ∈ range (r + 1),
          (-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 *
            (2 * (choose (2 * x) x : ZMod p)) * (choose (2 * (r - x)) (r - x) : ZMod p) =
          ∑ x ∈ range (r + 1),
            2 * ((-1 : ZMod p) ^ x * (choose r x : ZMod p) ^ 2 *
              (choose (2 * x) x : ZMod p) * (choose (2 * (r - x)) (r - x) : ZMod p)) := by
        refine sum_congr rfl ?_
        intro x hx
        ring
      rw [hrearr, ← mul_sum]
    rw [this]
  rw [hfirst, hsecond]
  ring

lemma sign_revPerm (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm (n := n)) = ∏ j : Fin n, (-1 : ℤˣ) ^ (j : ℕ) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  refine prod_congr rfl ?_
  intro j _
  have hinner : ∏ i ∈ Iio j, (if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else (-1)) =
      ∏ i ∈ Iio j, (-1 : ℤˣ) := by
    refine prod_congr rfl ?_
    intro i hi
    rw [mem_Iio] at hi
    have : ¬ Fin.rev i < Fin.rev j := by
      rw [Fin.rev_lt_rev]
      exact not_lt.mpr hi.le
    simp [Fin.revPerm_apply, this]
  rw [hinner, prod_const, Fin.card_Iio]

lemma prod_neg_one_pow_range_odd (n : ℕ) (hn : Odd n) :
    (∏ i ∈ range n, (-1 : ℤˣ) ^ i) = (-1) ^ ((n - 1) / 2) := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih]
    have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
    have heven : Even (2 * m + 2) := ⟨m + 1, by ring⟩
    rw [hodd.neg_one_pow, heven.neg_one_pow]
    have h1 : (2 * m + 1 - 1) / 2 = m := by omega
    have h2 : (2 * m + 1 + 1 + 1 - 1) / 2 = m + 1 := by omega
    rw [h1, h2, pow_succ]
    simp

lemma sign_revPerm_odd (n : ℕ) (hn : Odd n) :
    Equiv.Perm.sign (Fin.revPerm (n := n)) = (-1) ^ ((n - 1) / 2) := by
  rw [sign_revPerm, ← Finset.prod_range (fun i => (-1 : ℤˣ) ^ i),
    prod_neg_one_pow_range_odd n hn]

lemma sign_revPerm_zmod (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (Equiv.Perm.sign (Fin.revPerm (n := p)) : ZMod p) = (-1) ^ ((p - 1) / 2) := by
  have hodd : Odd p := (Nat.Prime.eq_two_or_odd' (Fact.out (p := p.Prime))).resolve_left h_odd
  rw [sign_revPerm_odd p hodd]
  simp

lemma det_hankel_vanish (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) (f : ℕ → ℤ)
    (hvanish : ∀ n, p ≤ n → n ≤ 2 * p - 2 → (f n : ZMod p) = 0) :
    let M : Matrix (Fin p) (Fin p) ℤ := fun i j => f (i.val + j.val)
    (M.det : ZMod p) = ((-1 : ZMod p) ^ ((p - 1) / 2)) * (f (p - 1) : ZMod p) := by
  intro M
  have hodd : Odd p := (Nat.Prime.eq_two_or_odd' (Fact.out (p := p.Prime))).resolve_left h_odd
  have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
  let Az : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => (f (i.val + j.val) : ZMod p)
  let Bz : Matrix (Fin p) (Fin p) (ZMod p) := Az.submatrix id Fin.revPerm
  have hcast : (M.det : ZMod p) = Az.det := by
    rw [Int.cast_det]
    rfl
  have htri : Bz.BlockTriangular id := by
    intro i j hij
    change (f (i.val + (Fin.rev j).val) : ZMod p) = 0
    apply hvanish
    · have : i.val + (Fin.rev j).val ≥ p := by
        rw [Fin.val_rev]
        have : j.val < i.val := hij
        omega
      exact this
    · have : i.val + (Fin.rev j).val ≤ 2 * p - 2 := by
        have hi : i.val ≤ p - 1 := Nat.le_pred_of_lt i.isLt
        have hj : (Fin.rev j).val ≤ p - 1 := Nat.le_pred_of_lt (Fin.rev j).isLt
        omega
      exact this
  have hdiag : ∀ i : Fin p, Bz i i = (f (p - 1) : ZMod p) := by
    intro i
    change (f (i.val + (Fin.rev i).val) : ZMod p) = (f (p - 1) : ZMod p)
    have : i.val + (Fin.rev i).val = p - 1 := by
      rw [Fin.val_rev]
      omega
    rw [this]
  have hdetB : Bz.det = (f (p - 1) : ZMod p) ^ p := by
    rw [det_of_upperTriangular htri]
    simp_rw [hdiag]
    simp [prod_const, Fintype.card_fin]
  have hperm : Bz.det = Equiv.Perm.sign Fin.revPerm * Az.det := det_permute' _ _
  have hsign2 : (Equiv.Perm.sign (Fin.revPerm (n := p)) : ZMod p) *
      (Equiv.Perm.sign (Fin.revPerm (n := p)) : ZMod p) = 1 := by
    rw [sign_revPerm_zmod p h_odd]
    rw [← pow_two, ← pow_mul]
    exact Even.neg_one_pow ⟨(p - 1) / 2, by ring⟩
  have hAz : Az.det = (Equiv.Perm.sign (Fin.revPerm (n := p)) : ZMod p) * Bz.det := by
    calc
      Az.det = (1 : ZMod p) * Az.det := (one_mul _).symm
      _ = (Equiv.Perm.sign (Fin.revPerm (n := p)) * Equiv.Perm.sign (Fin.revPerm (n := p))) *
            Az.det := by rw [hsign2]
      _ = Equiv.Perm.sign (Fin.revPerm (n := p)) *
            (Equiv.Perm.sign (Fin.revPerm (n := p)) * Az.det) := by
          rw [mul_assoc]
      _ = Equiv.Perm.sign (Fin.revPerm (n := p)) * Bz.det := by
          rw [hperm]
  rw [hcast, hAz, hdetB, ZMod.pow_card, sign_revPerm_zmod p h_odd]

/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    -- A(p) is the p x p matrix with entries a(i+j)
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    -- C(p) is the p x p matrix with entries c(i+j)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    have h := det_hankel_vanish p h_odd a (fun n hpn hn => a_of_ge p n h_odd hpn hn)
    simp only at h
    rw [h, a_pred p h_odd, mul_one]
    simp
  · rw [← ZMod.intCast_eq_intCast_iff]
    have h := det_hankel_vanish p h_odd c (fun n hpn hn => c_of_ge p n h_odd hpn hn)
    simp only at h
    rw [h, c_pred p h_odd]
    have hsq : ((-1 : ZMod p) ^ ((p - 1) / 2)) * ((-1 : ZMod p) ^ ((p - 1) / 2)) = 1 := by
      rw [← pow_two, ← pow_mul]
      exact Even.neg_one_pow ⟨(p - 1) / 2, by ring⟩
    simpa using hsq
