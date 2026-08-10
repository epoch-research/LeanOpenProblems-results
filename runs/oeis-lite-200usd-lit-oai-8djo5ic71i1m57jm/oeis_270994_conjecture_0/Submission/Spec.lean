import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

private lemma pow_mod_period_zmod (p period r e : ℕ)
    (hper : ((2 : ZMod p) ^ period) = 1) (he : e % period = r) :
    ((2 : ZMod p) ^ e) = (2 : ZMod p) ^ r := by
  have hdecomp : e = period * (e / period) + r := by
    rw [← he]
    exact (Nat.div_add_mod e period).symm
  rw [hdecomp, pow_add, pow_mul, hper, one_pow, one_mul]

private lemma cover_dvd (K p period r e : ℕ)
    (hper : ((2 : ZMod p) ^ period) = 1) (he : e % period = r)
    (hzero : (K : ZMod p) * ((2 : ZMod p) ^ r) + 1 = 0) :
    p ∣ K * 2^e + 1 := by
  have hpow : (((2 : ℕ) : ZMod p) ^ e) = (((2 : ℕ) : ZMod p) ^ r) := by
    simpa using pow_mod_period_zmod p period r e hper he
  have hz : ((K * 2^e + 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    rw [hpow]
    simpa using hzero
  exact (ZMod.natCast_eq_zero_iff (K * 2^e + 1) p).mp hz

private lemma not_prime_of_dvd_lt (N p : ℕ) (hp1 : p ≠ 1) (hpN : p < N) (hdvd : p ∣ N) :
    ¬ Nat.Prime N := by
  intro hN
  have h := hN.eq_one_or_self_of_dvd p hdvd
  rcases h with h | h
  · exact hp1 h
  · omega

private lemma not_prime_K_mul_pow_add_one (e : ℕ) :
    ¬ Nat.Prime (550806419973833079563 * 2^e + 1) := by
  have hpowpos : 1 ≤ 2^e := Nat.one_le_pow e 2 (by norm_num)
  have hlt_common : ∀ p : ℕ, p ≤ 1321 → p < 550806419973833079563 * 2^e + 1 := by
    intro p hp
    nlinarith
  have hlt : e % 120 < 120 := Nat.mod_lt e (by norm_num)
  generalize hq : e % 120 = q at hlt
  interval_cases q
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 11 (by norm_num) (hlt_common 11 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 11 10 5 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 10 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 31 (by norm_num) (hlt_common 31 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 31 5 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 5 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 41 (by norm_num) (hlt_common 41 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 41 20 9 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 20 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 11 (by norm_num) (hlt_common 11 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 11 10 5 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 10 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 151 (by norm_num) (hlt_common 151 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 151 15 8 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 15 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 41 (by norm_num) (hlt_common 41 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 41 20 9 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 20 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 1321 (by norm_num) (hlt_common 1321 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 1321 60 17 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 60 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 331 (by norm_num) (hlt_common 331 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 331 30 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 30 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 31 (by norm_num) (hlt_common 31 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 31 5 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 5 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 7 (by norm_num) (hlt_common 7 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 7 3 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 3 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 17 (by norm_num) (hlt_common 17 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 17 8 1 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 8 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 61 (by norm_num) (hlt_common 61 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 61 60 57 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 60 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 3 (by norm_num) (hlt_common 3 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 3 2 0 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 2 ∣ 120), hq]
  · refine not_prime_of_dvd_lt (550806419973833079563 * 2^e + 1) 5 (by norm_num) (hlt_common 5 (by norm_num)) ?_
    refine cover_dvd 550806419973833079563 5 4 3 e (by decide) ?_ (by decide)
    rw [← Nat.mod_mod_of_dvd e (by norm_num : 4 ∣ 120), hq]

private lemma K_is_sierpinski : is_sierpinski_number 550806419973833079563 := by
  refine ⟨by decide, by decide, ?_⟩
  intro e he
  exact not_prime_K_mul_pow_add_one e

/--
oeis_270994_conjecture_0: Are a(n) and a(n) + 28 always consecutive Sierpiński numbers?

This conjecture asserts that for all $n$, $a(n)$ and a(n)+28 are Sierpiński numbers,
and there are no Sierpiński numbers strictly between them.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  let n0 : ℕ := 49245934439103
  have hmid_eq : a n0 + 4 = 550806419973833079563 := by
    norm_num [a, n0]
  have hmid : is_sierpinski_number (a n0 + 4) := by
    rw [hmid_eq]
    exact K_is_sierpinski
  exact (h n0).2.2 (a n0 + 4) hmid (by norm_num [a, n0]) (by norm_num [a, n0])
