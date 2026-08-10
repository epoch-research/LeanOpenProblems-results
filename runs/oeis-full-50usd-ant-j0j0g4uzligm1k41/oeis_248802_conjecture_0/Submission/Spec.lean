import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 4000000

open Nat

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

private theorem pow_mod_order {p : ℕ} (x : ZMod p) (d : ℕ) (hx : x ^ d = 1)
    (k : ℕ) : x ^ k = x ^ (k % d) := by
  conv_lhs => rw [← Nat.div_add_mod k d, pow_add, pow_mul, hx, one_pow, one_mul]

private theorem exp_periodic (d a m P : ℕ) (hdeq : d = 2 ^ a * m) (ha : a ≤ 12)
    (hm : m ∣ 2 ^ (10 * P) - 1) (hcop : Nat.Coprime (2 ^ a) m)
    (b t : ℕ) (hb : 1 ≤ b) :
    2 ^ (10 * (b + t * P) + 2) ≡ 2 ^ (10 * b + 2) [MOD d] := by
  have hexp : 10 * (b + t * P) + 2 = (10 * b + 2) + 10 * t * P := by ring
  rw [hexp, pow_add]
  have hle : 2 ^ (10 * b + 2) ≤ 2 ^ (10 * b + 2) * 2 ^ (10 * t * P) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  refine (Nat.modEq_iff_dvd' hle).mpr ?_ |>.symm
  rw [hdeq]
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
  · apply Nat.dvd_sub
    · exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    · exact pow_dvd_pow 2 (by omega)
  · have hmm : (2 : ℕ) ^ (10 * t * P) ≡ 1 [MOD m] := by
      have hle1 : (1 : ℕ) ≤ 2 ^ (10 * P) := Nat.one_le_two_pow
      have h0 : (2 : ℕ) ^ (10 * P) ≡ 1 [MOD m] :=
        ((Nat.modEq_iff_dvd' hle1).mpr hm).symm
      have h1 := h0.pow t
      rw [← pow_mul, one_pow] at h1
      have he : 10 * P * t = 10 * t * P := by ring
      rwa [he] at h1
    have hX : 2 ^ (10 * b + 2) * 2 ^ (10 * t * P) ≡ 2 ^ (10 * b + 2) * 1 [MOD m] :=
      Nat.ModEq.mul_left _ hmm
    rw [mul_one] at hX
    exact (Nat.modEq_iff_dvd' hle).mp hX.symm

private theorem noDvd_gen (p d a m P : ℕ)
    (hdeq : d = 2 ^ a * m) (hcop : Nat.Coprime (2 ^ a) m) (ha : a ≤ 12)
    (hP : 1 ≤ P) (hm : m ∣ 2 ^ (10 * P) - 1)
    (hord : (2 : ZMod p) ^ d = 1)
    (hcheck : ∀ r, r < P → (2 : ZMod p) ^ ((2 ^ (10 * (r + 1) + 2) + 2) % d) + 3 ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) :
    ¬ p ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [pow_mod_order (2 : ZMod p) d hord]
  have hn' : n = (((n - 1) % P) + 1) + ((n - 1) / P) * P := by
    have hmd := Nat.mod_add_div (n - 1) P
    have hc : ((n - 1) / P) * P = P * ((n - 1) / P) := Nat.mul_comm _ _
    omega
  have h1 : 2 ^ (10 * n + 2) ≡ 2 ^ (10 * (((n - 1) % P) + 1) + 2) [MOD d] := by
    conv_lhs => rw [hn']
    exact exp_periodic d a m P hdeq ha hm hcop (((n - 1) % P) + 1) ((n - 1) / P) (by omega)
  have key : (2 ^ (10 * n + 2) + 2) % d = (2 ^ (10 * (((n - 1) % P) + 1) + 2) + 2) % d :=
    h1.add_right 2
  rw [key]
  exact hcheck ((n - 1) % P) (Nat.mod_lt _ hP)

private theorem dvd_gen (p d a m P : ℕ)
    (hdeq : d = 2 ^ a * m) (hcop : Nat.Coprime (2 ^ a) m) (ha : a ≤ 12)
    (hP : 1 ≤ P) (hm : m ∣ 2 ^ (10 * P) - 1)
    (hord : (2 : ZMod p) ^ d = 1)
    (hcheck : ∀ r, r < P → (2 : ZMod p) ^ ((2 ^ (10 * (r + 1) + 2) + 2) % d) + 3 = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    p ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [pow_mod_order (2 : ZMod p) d hord]
  have hn' : n = (((n - 1) % P) + 1) + ((n - 1) / P) * P := by
    have hmd := Nat.mod_add_div (n - 1) P
    have hc : ((n - 1) / P) * P = P * ((n - 1) / P) := Nat.mul_comm _ _
    omega
  have h1 : 2 ^ (10 * n + 2) ≡ 2 ^ (10 * (((n - 1) % P) + 1) + 2) [MOD d] := by
    conv_lhs => rw [hn']
    exact exp_periodic d a m P hdeq ha hm hcop (((n - 1) % P) + 1) ((n - 1) / P) (by omega)
  have key : (2 ^ (10 * n + 2) + 2) % d = (2 ^ (10 * (((n - 1) % P) + 1) + 2) + 2) % d :=
    h1.add_right 2
  rw [key]
  exact hcheck ((n - 1) % P) (Nat.mod_lt _ hP)


private theorem noDvd_2 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 2 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  have h1 : (2 : ℕ) ∣ 2 ^ (2 ^ (10 * n + 2) + 2) := dvd_pow_self 2 (by positivity)
  omega

private theorem noDvd_3 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 3 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 3 2 1 1 1 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_5 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 5 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 5 4 2 1 1 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_7 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 7 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 7 3 0 3 1 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_11 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 11 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 11 10 1 5 2 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_13 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 13 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 13 12 2 3 1 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_17 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 17 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 17 8 3 1 1 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_19 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 19 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 19 18 1 9 3 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_23 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 23 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 23 11 0 11 1 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_29 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 29 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 29 28 2 7 3 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_31 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 31 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 31 5 0 5 2 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_37 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 37 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 37 36 2 9 3 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_41 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 41 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 41 20 2 5 2 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_43 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 43 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 43 14 1 7 3 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_47 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 47 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 47 23 0 23 11 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_53 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 53 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 53 52 2 13 6 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_59 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 59 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 59 58 1 29 14 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem noDvd_61 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 61 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  noDvd_gen 61 60 2 15 2 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

private theorem dvd_67 (n : ℕ) (hn : 1 ≤ n) :
    67 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
  dvd_gen 67 66 1 33 1 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) n hn

/-- OEIS A248802 Conjecture 1: a(10n+2) = 67 for n >= 0. -/
theorem oeis_248802_conjecture_0 (n : ℕ) : a (10 * n + 2) = 67 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    show (2 ^ (2 ^ (10 * 0 + 2) + 2) + 3).minFac = 67
    have he : (2 ^ (2 ^ (10 * 0 + 2) + 2) + 3) = 67 := by norm_num
    rw [he]
    exact Nat.Prime.minFac_eq (by norm_num)
  · show (2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac = 67
    set N := 2 ^ (2 ^ (10 * n + 2) + 2) + 3 with hN
    have hN1 : N ≠ 1 := by
      have h := Nat.one_le_two_pow (n := 2 ^ (10 * n + 2) + 2)
      omega
    have h67 : 67 ∣ N := dvd_67 n hn
    have hle : N.minFac ≤ 67 := Nat.minFac_le_of_dvd (by norm_num) h67
    have hge : 67 ≤ N.minFac := by
      by_contra hlt
      push_neg at hlt
      have hp := Nat.minFac_prime hN1
      have hd := Nat.minFac_dvd N
      have h2le := hp.two_le
      interval_cases h : N.minFac <;>
        first
        | exact absurd hp (by decide)
        | exact (noDvd_2 n hn) hd
        | exact (noDvd_3 n hn) hd
        | exact (noDvd_5 n hn) hd
        | exact (noDvd_7 n hn) hd
        | exact (noDvd_11 n hn) hd
        | exact (noDvd_13 n hn) hd
        | exact (noDvd_17 n hn) hd
        | exact (noDvd_19 n hn) hd
        | exact (noDvd_23 n hn) hd
        | exact (noDvd_29 n hn) hd
        | exact (noDvd_31 n hn) hd
        | exact (noDvd_37 n hn) hd
        | exact (noDvd_41 n hn) hd
        | exact (noDvd_43 n hn) hd
        | exact (noDvd_47 n hn) hd
        | exact (noDvd_53 n hn) hd
        | exact (noDvd_59 n hn) hd
        | exact (noDvd_61 n hn) hd
    omega
