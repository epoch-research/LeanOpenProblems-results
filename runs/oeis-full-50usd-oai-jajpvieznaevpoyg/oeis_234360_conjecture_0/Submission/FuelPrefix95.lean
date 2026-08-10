import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
set_option exponentiation.threshold 10000

private def powFuel (a m e : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | f+1 => ((if e % 2 = 1 then a else 1) * powFuel ((a * a) % m) m (e / 2) f) % m

private lemma sq_pow_mod_goal (x m e : ℕ) :
    ((x % m % m * (x % m % m)) % m) ^ e % m = (x ^ e) ^ 2 % m := by
  rw [← Nat.pow_mod ((x % m % m) * (x % m % m)) e m]
  rw [mul_pow]
  rw [pow_two]
  simp [Nat.pow_mod, Nat.mul_mod]

private lemma powFuel_eq (a m e f : ℕ) (hbound : e < 2 ^ f) :
    powFuel a m e f = a ^ e % m := by
  induction f generalizing a e with
  | zero =>
      have he : e = 0 := by omega
      subst e
      simp [powFuel]
  | succ f ih =>
      have hdivbound : e / 2 < 2 ^ f := by
        have h2 : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [pow_succ']
        rw [h2] at hbound
        exact Nat.div_lt_of_lt_mul hbound
      simp [powFuel]
      rw [ih ((a * a) % m) (e / 2) hdivbound]
      have hmodlt : e % 2 = 0 ∨ e % 2 = 1 := by omega
      rcases hmodlt with h0 | h1
      · have heven : e = 2 * (e / 2) := by
          have h := Nat.div_add_mod e 2
          omega
        rw [heven]
        simp [h0, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (e / 2)]
        rw [show (a ^ (e / 2)) ^ 2 = (a ^ 2) ^ (e / 2) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      · have hodd : e = 1 + 2 * (e / 2) := by
          have h := Nat.div_add_mod e 2
          omega
        have hdiv : (1 + 2 * (e / 2)) / 2 = e / 2 := by omega
        rw [hodd]
        simp [h1, hdiv, pow_add, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (e / 2)]
        rw [show (a ^ (e / 2)) ^ 2 = (a ^ 2) ^ (e / 2) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]


open Nat Finset

/--
A234360: $a(n) = \left|\left\{0 < k < n: (k+1)^{\phi(n-k)} + k \text{ is prime}\right\}\right|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (filter (fun k => Nat.Prime ((k + 1) ^ (Nat.totient (n - k)) + k)) (Ico 1 n)).card

private theorem no_prime_1408_1 (hp : Nat.Prime ((1 + 1) ^ (Nat.totient (1408 - 1) / 2) - 1)) : False := by
  have ht : Nat.totient (1408 - 1) / 2 = 396 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((1 + 1) ^ 396 - 1 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (1 + 1) ^ 3 ≤ (1 + 1) ^ 396 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 1 < (1 + 1) ^ 3 := by norm_num
  have hlt : 3 < ((1 + 1) ^ 396 - 1 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_2 (hp : Nat.Prime ((2 + 1) ^ (Nat.totient (1408 - 2) / 2) - 2)) : False := by
  have ht : Nat.totient (1408 - 2) / 2 = 324 := by decide
  rw [ht] at hp
  have hd : 31 ∣ ((2 + 1) ^ 324 - 2 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (2 + 1) ^ 4 ≤ (2 + 1) ^ 324 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 31 + 2 < (2 + 1) ^ 4 := by norm_num
  have hlt : 31 < ((2 + 1) ^ 324 - 2 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 31 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_3 (hp : Nat.Prime ((3 + 1) ^ (Nat.totient (1408 - 3) / 2) - 3)) : False := by
  have ht : Nat.totient (1408 - 3) / 2 = 560 := by decide
  rw [ht] at hp
  have hd : 13 ∣ ((3 + 1) ^ 560 - 3 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (3 + 1) ^ 3 ≤ (3 + 1) ^ 560 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 13 + 3 < (3 + 1) ^ 3 := by norm_num
  have hlt : 13 < ((3 + 1) ^ 560 - 3 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 13 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_4 (hp : Nat.Prime ((4 + 1) ^ (Nat.totient (1408 - 4) / 2) - 4)) : False := by
  have ht : Nat.totient (1408 - 4) / 2 = 216 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((4 + 1) ^ 216 - 4 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (4 + 1) ^ 2 ≤ (4 + 1) ^ 216 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 4 < (4 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((4 + 1) ^ 216 - 4 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_5 (hp : Nat.Prime ((5 + 1) ^ (Nat.totient (1408 - 5) / 2) - 5)) : False := by
  have ht : Nat.totient (1408 - 5) / 2 = 660 := by decide
  rw [ht] at hp
  have hd : 8819 ∣ ((5 + 1) ^ 660 - 5 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (5 + 1) ^ 6 ≤ (5 + 1) ^ 660 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 8819 + 5 < (5 + 1) ^ 6 := by norm_num
  have hlt : 8819 < ((5 + 1) ^ 660 - 5 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 8819 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_6 (hp : Nat.Prime ((6 + 1) ^ (Nat.totient (1408 - 6) / 2) - 6)) : False := by
  have ht : Nat.totient (1408 - 6) / 2 = 350 := by decide
  rw [ht] at hp
  have hd : 43 ∣ ((6 + 1) ^ 350 - 6 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (6 + 1) ^ 3 ≤ (6 + 1) ^ 350 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 43 + 6 < (6 + 1) ^ 3 := by norm_num
  have hlt : 43 < ((6 + 1) ^ 350 - 6 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 43 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_7 (hp : Nat.Prime ((7 + 1) ^ (Nat.totient (1408 - 7) / 2) - 7)) : False := by
  have ht : Nat.totient (1408 - 7) / 2 = 466 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((7 + 1) ^ 466 - 7 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (7 + 1) ^ 2 ≤ (7 + 1) ^ 466 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 7 < (7 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((7 + 1) ^ 466 - 7 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_8 (hp : Nat.Prime ((8 + 1) ^ (Nat.totient (1408 - 8) / 2) - 8)) : False := by
  have ht : Nat.totient (1408 - 8) / 2 = 240 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((8 + 1) ^ 240 - 8 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (8 + 1) ^ 2 ≤ (8 + 1) ^ 240 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 8 < (8 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((8 + 1) ^ 240 - 8 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_9 (hp : Nat.Prime ((9 + 1) ^ (Nat.totient (1408 - 9) / 2) - 9)) : False := by
  have ht : Nat.totient (1408 - 9) / 2 = 699 := by decide
  rw [ht] at hp
  have hd : 5867 ∣ ((9 + 1) ^ 699 - 9 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (9 + 1) ^ 4 ≤ (9 + 1) ^ 699 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 5867 + 9 < (9 + 1) ^ 4 := by norm_num
  have hlt : 5867 < ((9 + 1) ^ 699 - 9 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 5867 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_10 (hp : Nat.Prime ((10 + 1) ^ (Nat.totient (1408 - 10) / 2) - 10)) : False := by
  have ht : Nat.totient (1408 - 10) / 2 = 232 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((10 + 1) ^ 232 - 10 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (10 + 1) ^ 2 ≤ (10 + 1) ^ 232 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 10 < (10 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((10 + 1) ^ 232 - 10 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_11 (hp : Nat.Prime ((11 + 1) ^ (Nat.totient (1408 - 11) / 2) - 11)) : False := by
  have ht : Nat.totient (1408 - 11) / 2 = 630 := by decide
  rw [ht] at hp
  have hd : 122657315801 ∣ ((11 + 1) ^ 630 - 11 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (11 + 1) ^ 11 ≤ (11 + 1) ^ 630 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 122657315801 + 11 < (11 + 1) ^ 11 := by norm_num
  have hlt : 122657315801 < ((11 + 1) ^ 630 - 11 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 122657315801 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_12 (hp : Nat.Prime ((12 + 1) ^ (Nat.totient (1408 - 12) / 2) - 12)) : False := by
  have ht : Nat.totient (1408 - 12) / 2 = 348 := by decide
  rw [ht] at hp
  have hd : 47 ∣ ((12 + 1) ^ 348 - 12 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (12 + 1) ^ 2 ≤ (12 + 1) ^ 348 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 47 + 12 < (12 + 1) ^ 2 := by norm_num
  have hlt : 47 < ((12 + 1) ^ 348 - 12 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 47 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_13 (hp : Nat.Prime ((13 + 1) ^ (Nat.totient (1408 - 13) / 2) - 13)) : False := by
  have ht : Nat.totient (1408 - 13) / 2 = 360 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((13 + 1) ^ 360 - 13 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (13 + 1) ^ 2 ≤ (13 + 1) ^ 360 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 13 < (13 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((13 + 1) ^ 360 - 13 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_14 (hp : Nat.Prime ((14 + 1) ^ (Nat.totient (1408 - 14) / 2) - 14)) : False := by
  have ht : Nat.totient (1408 - 14) / 2 = 320 := by decide
  rw [ht] at hp
  have hd : 47 ∣ ((14 + 1) ^ 320 - 14 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (14 + 1) ^ 2 ≤ (14 + 1) ^ 320 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 47 + 14 < (14 + 1) ^ 2 := by norm_num
  have hlt : 47 < ((14 + 1) ^ 320 - 14 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 47 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_15 (hp : Nat.Prime ((15 + 1) ^ (Nat.totient (1408 - 15) / 2) - 15)) : False := by
  have ht : Nat.totient (1408 - 15) / 2 = 594 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((15 + 1) ^ 594 - 15 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (15 + 1) ^ 2 ≤ (15 + 1) ^ 594 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 15 < (15 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((15 + 1) ^ 594 - 15 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_16 (hp : Nat.Prime ((16 + 1) ^ (Nat.totient (1408 - 16) / 2) - 16)) : False := by
  have ht : Nat.totient (1408 - 16) / 2 = 224 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((16 + 1) ^ 224 - 16 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (16 + 1) ^ 2 ≤ (16 + 1) ^ 224 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 16 < (16 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((16 + 1) ^ 224 - 16 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_17 (hp : Nat.Prime ((17 + 1) ^ (Nat.totient (1408 - 17) / 2) - 17)) : False := by
  have ht : Nat.totient (1408 - 17) / 2 = 636 := by decide
  rw [ht] at hp
  have hd : 5008229652071 ∣ ((17 + 1) ^ 636 - 17 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (17 + 1) ^ 11 ≤ (17 + 1) ^ 636 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 5008229652071 + 17 < (17 + 1) ^ 11 := by norm_num
  have hlt : 5008229652071 < ((17 + 1) ^ 636 - 17 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 5008229652071 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_18 (hp : Nat.Prime ((18 + 1) ^ (Nat.totient (1408 - 18) / 2) - 18)) : False := by
  have ht : Nat.totient (1408 - 18) / 2 = 276 := by decide
  rw [ht] at hp
  have hd : 191 ∣ ((18 + 1) ^ 276 - 18 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (18 + 1) ^ 2 ≤ (18 + 1) ^ 276 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 191 + 18 < (18 + 1) ^ 2 := by norm_num
  have hlt : 191 < ((18 + 1) ^ 276 - 18 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 191 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_19 (hp : Nat.Prime ((19 + 1) ^ (Nat.totient (1408 - 19) / 2) - 19)) : False := by
  have ht : Nat.totient (1408 - 19) / 2 = 462 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((19 + 1) ^ 462 - 19 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (19 + 1) ^ 2 ≤ (19 + 1) ^ 462 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 19 < (19 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((19 + 1) ^ 462 - 19 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_20 (hp : Nat.Prime ((20 + 1) ^ (Nat.totient (1408 - 20) / 2) - 20)) : False := by
  have ht : Nat.totient (1408 - 20) / 2 = 346 := by decide
  rw [ht] at hp
  have hd : 13679 ∣ ((20 + 1) ^ 346 - 20 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (20 + 1) ^ 4 ≤ (20 + 1) ^ 346 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 13679 + 20 < (20 + 1) ^ 4 := by norm_num
  have hlt : 13679 < ((20 + 1) ^ 346 - 20 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 13679 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_21 (hp : Nat.Prime ((21 + 1) ^ (Nat.totient (1408 - 21) / 2) - 21)) : False := by
  have ht : Nat.totient (1408 - 21) / 2 = 648 := by decide
  rw [ht] at hp
  have hd : 5 ∣ ((21 + 1) ^ 648 - 21 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (21 + 1) ^ 2 ≤ (21 + 1) ^ 648 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 5 + 21 < (21 + 1) ^ 2 := by norm_num
  have hlt : 5 < ((21 + 1) ^ 648 - 21 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 5 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_22 (hp : Nat.Prime ((22 + 1) ^ (Nat.totient (1408 - 22) / 2) - 22)) : False := by
  have ht : Nat.totient (1408 - 22) / 2 = 180 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((22 + 1) ^ 180 - 22 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (22 + 1) ^ 2 ≤ (22 + 1) ^ 180 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 22 < (22 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((22 + 1) ^ 180 - 22 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_23 (hp : Nat.Prime ((23 + 1) ^ (Nat.totient (1408 - 23) / 2) - 23)) : False := by
  have ht : Nat.totient (1408 - 23) / 2 = 552 := by decide
  rw [ht] at hp
  have hd : 29 ∣ ((23 + 1) ^ 552 - 23 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (23 + 1) ^ 2 ≤ (23 + 1) ^ 552 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 29 + 23 < (23 + 1) ^ 2 := by norm_num
  have hlt : 29 < ((23 + 1) ^ 552 - 23 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 29 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_24 (hp : Nat.Prime ((24 + 1) ^ (Nat.totient (1408 - 24) / 2) - 24)) : False := by
  have ht : Nat.totient (1408 - 24) / 2 = 344 := by decide
  rw [ht] at hp
  have hd : 601 ∣ ((24 + 1) ^ 344 - 24 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (24 + 1) ^ 3 ≤ (24 + 1) ^ 344 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 601 + 24 < (24 + 1) ^ 3 := by norm_num
  have hlt : 601 < ((24 + 1) ^ 344 - 24 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 601 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_25 (hp : Nat.Prime ((25 + 1) ^ (Nat.totient (1408 - 25) / 2) - 25)) : False := by
  have ht : Nat.totient (1408 - 25) / 2 = 460 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((25 + 1) ^ 460 - 25 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (25 + 1) ^ 2 ≤ (25 + 1) ^ 460 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 25 < (25 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((25 + 1) ^ 460 - 25 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_26 (hp : Nat.Prime ((26 + 1) ^ (Nat.totient (1408 - 26) / 2) - 26)) : False := by
  have ht : Nat.totient (1408 - 26) / 2 = 345 := by decide
  rw [ht] at hp
  have hd : 23 ∣ ((26 + 1) ^ 345 - 26 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (26 + 1) ^ 2 ≤ (26 + 1) ^ 345 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 23 + 26 < (26 + 1) ^ 2 := by norm_num
  have hlt : 23 < ((26 + 1) ^ 345 - 26 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 23 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_27 (hp : Nat.Prime ((27 + 1) ^ (Nat.totient (1408 - 27) / 2) - 27)) : False := by
  have ht : Nat.totient (1408 - 27) / 2 = 690 := by decide
  rw [ht] at hp
  have hd : 347 ∣ ((27 + 1) ^ 690 - 27 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (27 + 1) ^ 2 ≤ (27 + 1) ^ 690 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 347 + 27 < (27 + 1) ^ 2 := by norm_num
  have hlt : 347 < ((27 + 1) ^ 690 - 27 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 347 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_28 (hp : Nat.Prime ((28 + 1) ^ (Nat.totient (1408 - 28) / 2) - 28)) : False := by
  have ht : Nat.totient (1408 - 28) / 2 = 176 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((28 + 1) ^ 176 - 28 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (28 + 1) ^ 2 ≤ (28 + 1) ^ 176 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 28 < (28 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((28 + 1) ^ 176 - 28 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_29 (hp : Nat.Prime ((29 + 1) ^ (Nat.totient (1408 - 29) / 2) - 29)) : False := by
  have ht : Nat.totient (1408 - 29) / 2 = 588 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((29 + 1) ^ 588 - 29 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (29 + 1) ^ 2 ≤ (29 + 1) ^ 588 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 29 < (29 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((29 + 1) ^ 588 - 29 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_30 (hp : Nat.Prime ((30 + 1) ^ (Nat.totient (1408 - 30) / 2) - 30)) : False := by
  have ht : Nat.totient (1408 - 30) / 2 = 312 := by decide
  rw [ht] at hp
  have hd : 12990738933730441801 ∣ ((30 + 1) ^ 312 - 30 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (30 + 1) ^ 13 ≤ (30 + 1) ^ 312 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 12990738933730441801 + 30 < (30 + 1) ^ 13 := by norm_num
  have hlt : 12990738933730441801 < ((30 + 1) ^ 312 - 30 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 12990738933730441801 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_31 (hp : Nat.Prime ((31 + 1) ^ (Nat.totient (1408 - 31) / 2) - 31)) : False := by
  have ht : Nat.totient (1408 - 31) / 2 = 432 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((31 + 1) ^ 432 - 31 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (31 + 1) ^ 2 ≤ (31 + 1) ^ 432 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 31 < (31 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((31 + 1) ^ 432 - 31 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_32 (hp : Nat.Prime ((32 + 1) ^ (Nat.totient (1408 - 32) / 2) - 32)) : False := by
  have ht : Nat.totient (1408 - 32) / 2 = 336 := by decide
  rw [ht] at hp
  have hd : 881 ∣ ((32 + 1) ^ 336 - 32 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (32 + 1) ^ 2 ≤ (32 + 1) ^ 336 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 881 + 32 < (32 + 1) ^ 2 := by norm_num
  have hlt : 881 < ((32 + 1) ^ 336 - 32 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 881 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_33 (hp : Nat.Prime ((33 + 1) ^ (Nat.totient (1408 - 33) / 2) - 33)) : False := by
  have ht : Nat.totient (1408 - 33) / 2 = 500 := by decide
  rw [ht] at hp
  have hd : 97 ∣ ((33 + 1) ^ 500 - 33 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (33 + 1) ^ 2 ≤ (33 + 1) ^ 500 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 97 + 33 < (33 + 1) ^ 2 := by norm_num
  have hlt : 97 < ((33 + 1) ^ 500 - 33 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 97 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_34 (hp : Nat.Prime ((34 + 1) ^ (Nat.totient (1408 - 34) / 2) - 34)) : False := by
  have ht : Nat.totient (1408 - 34) / 2 = 228 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((34 + 1) ^ 228 - 34 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (34 + 1) ^ 2 ≤ (34 + 1) ^ 228 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 34 < (34 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((34 + 1) ^ 228 - 34 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_35 (hp : Nat.Prime ((35 + 1) ^ (Nat.totient (1408 - 35) / 2) - 35)) : False := by
  have ht : Nat.totient (1408 - 35) / 2 = 686 := by decide
  rw [ht] at hp
  have hd : 13 ∣ ((35 + 1) ^ 686 - 35 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (35 + 1) ^ 2 ≤ (35 + 1) ^ 686 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 13 + 35 < (35 + 1) ^ 2 := by norm_num
  have hlt : 13 < ((35 + 1) ^ 686 - 35 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 13 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_36 (hp : Nat.Prime ((36 + 1) ^ (Nat.totient (1408 - 36) / 2) - 36)) : False := by
  have ht : Nat.totient (1408 - 36) / 2 = 294 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((36 + 1) ^ 294 - 36 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (36 + 1) ^ 2 ≤ (36 + 1) ^ 294 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 36 < (36 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((36 + 1) ^ 294 - 36 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_37 (hp : Nat.Prime ((37 + 1) ^ (Nat.totient (1408 - 37) / 2) - 37)) : False := by
  have ht : Nat.totient (1408 - 37) / 2 = 456 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((37 + 1) ^ 456 - 37 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (37 + 1) ^ 2 ≤ (37 + 1) ^ 456 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 37 < (37 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((37 + 1) ^ 456 - 37 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_38 (hp : Nat.Prime ((38 + 1) ^ (Nat.totient (1408 - 38) / 2) - 38)) : False := by
  have ht : Nat.totient (1408 - 38) / 2 = 272 := by decide
  rw [ht] at hp
  have hd : 1483 ∣ ((38 + 1) ^ 272 - 38 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (38 + 1) ^ 3 ≤ (38 + 1) ^ 272 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 1483 + 38 < (38 + 1) ^ 3 := by norm_num
  have hlt : 1483 < ((38 + 1) ^ 272 - 38 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 1483 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_39 (hp : Nat.Prime ((39 + 1) ^ (Nat.totient (1408 - 39) / 2) - 39)) : False := by
  have ht : Nat.totient (1408 - 39) / 2 = 666 := by decide
  rw [ht] at hp
  have hd : 19 ∣ ((39 + 1) ^ 666 - 39 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (39 + 1) ^ 2 ≤ (39 + 1) ^ 666 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 19 + 39 < (39 + 1) ^ 2 := by norm_num
  have hlt : 19 < ((39 + 1) ^ 666 - 39 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 19 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_40 (hp : Nat.Prime ((40 + 1) ^ (Nat.totient (1408 - 40) / 2) - 40)) : False := by
  have ht : Nat.totient (1408 - 40) / 2 = 216 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((40 + 1) ^ 216 - 40 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (40 + 1) ^ 2 ≤ (40 + 1) ^ 216 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 40 < (40 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((40 + 1) ^ 216 - 40 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_41 (hp : Nat.Prime ((41 + 1) ^ (Nat.totient (1408 - 41) / 2) - 41)) : False := by
  have ht : Nat.totient (1408 - 41) / 2 = 683 := by decide
  rw [ht] at hp
  have hd : 794311889339 ∣ ((41 + 1) ^ 683 - 41 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (41 + 1) ^ 8 ≤ (41 + 1) ^ 683 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 794311889339 + 41 < (41 + 1) ^ 8 := by norm_num
  have hlt : 794311889339 < ((41 + 1) ^ 683 - 41 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 794311889339 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_42 (hp : Nat.Prime ((42 + 1) ^ (Nat.totient (1408 - 42) / 2) - 42)) : False := by
  have ht : Nat.totient (1408 - 42) / 2 = 341 := by decide
  rw [ht] at hp
  have hd : 17 ∣ ((42 + 1) ^ 341 - 42 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (42 + 1) ^ 2 ≤ (42 + 1) ^ 341 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 17 + 42 < (42 + 1) ^ 2 := by norm_num
  have hlt : 17 < ((42 + 1) ^ 341 - 42 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 17 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_43 (hp : Nat.Prime ((43 + 1) ^ (Nat.totient (1408 - 43) / 2) - 43)) : False := by
  have ht : Nat.totient (1408 - 43) / 2 = 288 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((43 + 1) ^ 288 - 43 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (43 + 1) ^ 2 ≤ (43 + 1) ^ 288 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 43 < (43 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((43 + 1) ^ 288 - 43 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_44 (hp : Nat.Prime ((44 + 1) ^ (Nat.totient (1408 - 44) / 2) - 44)) : False := by
  have ht : Nat.totient (1408 - 44) / 2 = 300 := by decide
  rw [ht] at hp
  have hd : 269 ∣ ((44 + 1) ^ 300 - 44 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (44 + 1) ^ 2 ≤ (44 + 1) ^ 300 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 269 + 44 < (44 + 1) ^ 2 := by norm_num
  have hlt : 269 < ((44 + 1) ^ 300 - 44 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 269 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_45 (hp : Nat.Prime ((45 + 1) ^ (Nat.totient (1408 - 45) / 2) - 45)) : False := by
  have ht : Nat.totient (1408 - 45) / 2 = 644 := by decide
  rw [ht] at hp
  have hd : 19 ∣ ((45 + 1) ^ 644 - 45 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (45 + 1) ^ 2 ≤ (45 + 1) ^ 644 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 19 + 45 < (45 + 1) ^ 2 := by norm_num
  have hlt : 19 < ((45 + 1) ^ 644 - 45 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 19 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_46 (hp : Nat.Prime ((46 + 1) ^ (Nat.totient (1408 - 46) / 2) - 46)) : False := by
  have ht : Nat.totient (1408 - 46) / 2 = 226 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((46 + 1) ^ 226 - 46 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (46 + 1) ^ 2 ≤ (46 + 1) ^ 226 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 46 < (46 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((46 + 1) ^ 226 - 46 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_47 (hp : Nat.Prime ((47 + 1) ^ (Nat.totient (1408 - 47) / 2) - 47)) : False := by
  have ht : Nat.totient (1408 - 47) / 2 = 680 := by decide
  rw [ht] at hp
  have hd : 37 ∣ ((47 + 1) ^ 680 - 47 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (47 + 1) ^ 2 ≤ (47 + 1) ^ 680 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 37 + 47 < (47 + 1) ^ 2 := by norm_num
  have hlt : 37 < ((47 + 1) ^ 680 - 47 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 37 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_48 (hp : Nat.Prime ((48 + 1) ^ (Nat.totient (1408 - 48) / 2) - 48)) : False := by
  have ht : Nat.totient (1408 - 48) / 2 = 256 := by decide
  rw [ht] at hp
  have hd : 107 ∣ ((48 + 1) ^ 256 - 48 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (48 + 1) ^ 2 ≤ (48 + 1) ^ 256 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 107 + 48 < (48 + 1) ^ 2 := by norm_num
  have hlt : 107 < ((48 + 1) ^ 256 - 48 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 107 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_49 (hp : Nat.Prime ((49 + 1) ^ (Nat.totient (1408 - 49) / 2) - 49)) : False := by
  have ht : Nat.totient (1408 - 49) / 2 = 450 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((49 + 1) ^ 450 - 49 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (49 + 1) ^ 2 ≤ (49 + 1) ^ 450 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 49 < (49 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((49 + 1) ^ 450 - 49 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_50 (hp : Nat.Prime ((50 + 1) ^ (Nat.totient (1408 - 50) / 2) - 50)) : False := by
  have ht : Nat.totient (1408 - 50) / 2 = 288 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((50 + 1) ^ 288 - 50 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (50 + 1) ^ 2 ≤ (50 + 1) ^ 288 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 50 < (50 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((50 + 1) ^ 288 - 50 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_51 (hp : Nat.Prime ((51 + 1) ^ (Nat.totient (1408 - 51) / 2) - 51)) : False := by
  have ht : Nat.totient (1408 - 51) / 2 = 638 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((51 + 1) ^ 638 - 51 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (51 + 1) ^ 2 ≤ (51 + 1) ^ 638 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 51 < (51 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((51 + 1) ^ 638 - 51 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_52 (hp : Nat.Prime ((52 + 1) ^ (Nat.totient (1408 - 52) / 2) - 52)) : False := by
  have ht : Nat.totient (1408 - 52) / 2 = 224 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((52 + 1) ^ 224 - 52 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (52 + 1) ^ 2 ≤ (52 + 1) ^ 224 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 52 < (52 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((52 + 1) ^ 224 - 52 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_53 (hp : Nat.Prime ((53 + 1) ^ (Nat.totient (1408 - 53) / 2) - 53)) : False := by
  have ht : Nat.totient (1408 - 53) / 2 = 540 := by decide
  rw [ht] at hp
  have hd : 13 ∣ ((53 + 1) ^ 540 - 53 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (53 + 1) ^ 2 ≤ (53 + 1) ^ 540 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 13 + 53 < (53 + 1) ^ 2 := by norm_num
  have hlt : 13 < ((53 + 1) ^ 540 - 53 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 13 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_54 (hp : Nat.Prime ((54 + 1) ^ (Nat.totient (1408 - 54) / 2) - 54)) : False := by
  have ht : Nat.totient (1408 - 54) / 2 = 338 := by decide
  rw [ht] at hp
  have hd : 2971 ∣ ((54 + 1) ^ 338 - 54 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (54 + 1) ^ 3 ≤ (54 + 1) ^ 338 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 2971 + 54 < (54 + 1) ^ 3 := by norm_num
  have hlt : 2971 < ((54 + 1) ^ 338 - 54 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 2971 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_55 (hp : Nat.Prime ((55 + 1) ^ (Nat.totient (1408 - 55) / 2) - 55)) : False := by
  have ht : Nat.totient (1408 - 55) / 2 = 400 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((55 + 1) ^ 400 - 55 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (55 + 1) ^ 2 ≤ (55 + 1) ^ 400 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 55 < (55 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((55 + 1) ^ 400 - 55 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_56 (hp : Nat.Prime ((56 + 1) ^ (Nat.totient (1408 - 56) / 2) - 56)) : False := by
  have ht : Nat.totient (1408 - 56) / 2 = 312 := by decide
  rw [ht] at hp
  have hd : 5 ∣ ((56 + 1) ^ 312 - 56 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (56 + 1) ^ 2 ≤ (56 + 1) ^ 312 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 5 + 56 < (56 + 1) ^ 2 := by norm_num
  have hlt : 5 < ((56 + 1) ^ 312 - 56 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 5 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_57 (hp : Nat.Prime ((57 + 1) ^ (Nat.totient (1408 - 57) / 2) - 57)) : False := by
  have ht : Nat.totient (1408 - 57) / 2 = 576 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((57 + 1) ^ 576 - 57 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (57 + 1) ^ 2 ≤ (57 + 1) ^ 576 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 57 < (57 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((57 + 1) ^ 576 - 57 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_58 (hp : Nat.Prime ((58 + 1) ^ (Nat.totient (1408 - 58) / 2) - 58)) : False := by
  have ht : Nat.totient (1408 - 58) / 2 = 180 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((58 + 1) ^ 180 - 58 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (58 + 1) ^ 2 ≤ (58 + 1) ^ 180 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 58 < (58 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((58 + 1) ^ 180 - 58 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_59 (hp : Nat.Prime ((59 + 1) ^ (Nat.totient (1408 - 59) / 2) - 59)) : False := by
  have ht : Nat.totient (1408 - 59) / 2 = 630 := by decide
  rw [ht] at hp
  have hd : 67 ∣ ((59 + 1) ^ 630 - 59 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (59 + 1) ^ 2 ≤ (59 + 1) ^ 630 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 67 + 59 < (59 + 1) ^ 2 := by norm_num
  have hlt : 67 < ((59 + 1) ^ 630 - 59 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 67 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_60 (hp : Nat.Prime ((60 + 1) ^ (Nat.totient (1408 - 60) / 2) - 60)) : False := by
  have ht : Nat.totient (1408 - 60) / 2 = 336 := by decide
  rw [ht] at hp
  have hd : 11 ∣ ((60 + 1) ^ 336 - 60 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (60 + 1) ^ 2 ≤ (60 + 1) ^ 336 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 11 + 60 < (60 + 1) ^ 2 := by norm_num
  have hlt : 11 < ((60 + 1) ^ 336 - 60 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 11 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_61 (hp : Nat.Prime ((61 + 1) ^ (Nat.totient (1408 - 61) / 2) - 61)) : False := by
  have ht : Nat.totient (1408 - 61) / 2 = 448 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((61 + 1) ^ 448 - 61 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (61 + 1) ^ 2 ≤ (61 + 1) ^ 448 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 61 < (61 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((61 + 1) ^ 448 - 61 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_62 (hp : Nat.Prime ((62 + 1) ^ (Nat.totient (1408 - 62) / 2) - 62)) : False := by
  have ht : Nat.totient (1408 - 62) / 2 = 336 := by decide
  rw [ht] at hp
  have hd : 199 ∣ ((62 + 1) ^ 336 - 62 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (62 + 1) ^ 2 ≤ (62 + 1) ^ 336 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 199 + 62 < (62 + 1) ^ 2 := by norm_num
  have hlt : 199 < ((62 + 1) ^ 336 - 62 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 199 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_63 (hp : Nat.Prime ((63 + 1) ^ (Nat.totient (1408 - 63) / 2) - 63)) : False := by
  have ht : Nat.totient (1408 - 63) / 2 = 536 := by decide
  rw [ht] at hp
  have hd : 37 ∣ ((63 + 1) ^ 536 - 63 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (63 + 1) ^ 2 ≤ (63 + 1) ^ 536 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 37 + 63 < (63 + 1) ^ 2 := by norm_num
  have hlt : 37 < ((63 + 1) ^ 536 - 63 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 37 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_64 (hp : Nat.Prime ((64 + 1) ^ (Nat.totient (1408 - 64) / 2) - 64)) : False := by
  have ht : Nat.totient (1408 - 64) / 2 = 192 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((64 + 1) ^ 192 - 64 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (64 + 1) ^ 2 ≤ (64 + 1) ^ 192 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 64 < (64 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((64 + 1) ^ 192 - 64 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_65 (hp : Nat.Prime ((65 + 1) ^ (Nat.totient (1408 - 65) / 2) - 65)) : False := by
  have ht : Nat.totient (1408 - 65) / 2 = 624 := by decide
  rw [ht] at hp
  have hd : 164357 ∣ ((65 + 1) ^ 624 - 65 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (65 + 1) ^ 3 ≤ (65 + 1) ^ 624 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 164357 + 65 < (65 + 1) ^ 3 := by norm_num
  have hlt : 164357 < ((65 + 1) ^ 624 - 65 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 164357 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_66 (hp : Nat.Prime ((66 + 1) ^ (Nat.totient (1408 - 66) / 2) - 66)) : False := by
  have ht : Nat.totient (1408 - 66) / 2 = 300 := by decide
  rw [ht] at hp
  have hd : 5 ∣ ((66 + 1) ^ 300 - 66 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (66 + 1) ^ 2 ≤ (66 + 1) ^ 300 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 5 + 66 < (66 + 1) ^ 2 := by norm_num
  have hlt : 5 < ((66 + 1) ^ 300 - 66 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 5 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_67 (hp : Nat.Prime ((67 + 1) ^ (Nat.totient (1408 - 67) / 2) - 67)) : False := by
  have ht : Nat.totient (1408 - 67) / 2 = 444 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((67 + 1) ^ 444 - 67 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (67 + 1) ^ 2 ≤ (67 + 1) ^ 444 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 67 < (67 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((67 + 1) ^ 444 - 67 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_68 (hp : Nat.Prime ((68 + 1) ^ (Nat.totient (1408 - 68) / 2) - 68)) : False := by
  have ht : Nat.totient (1408 - 68) / 2 = 264 := by decide
  rw [ht] at hp
  have hd : 67 ∣ ((68 + 1) ^ 264 - 68 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (68 + 1) ^ 2 ≤ (68 + 1) ^ 264 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 67 + 68 < (68 + 1) ^ 2 := by norm_num
  have hlt : 67 < ((68 + 1) ^ 264 - 68 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 67 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_69 (hp : Nat.Prime ((69 + 1) ^ (Nat.totient (1408 - 69) / 2) - 69)) : False := by
  have ht : Nat.totient (1408 - 69) / 2 = 612 := by decide
  rw [ht] at hp
  have hd : 743 ∣ ((69 + 1) ^ 612 - 69 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (69 + 1) ^ 2 ≤ (69 + 1) ^ 612 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 743 + 69 < (69 + 1) ^ 2 := by norm_num
  have hlt : 743 < ((69 + 1) ^ 612 - 69 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 743 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_70 (hp : Nat.Prime ((70 + 1) ^ (Nat.totient (1408 - 70) / 2) - 70)) : False := by
  have ht : Nat.totient (1408 - 70) / 2 = 222 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((70 + 1) ^ 222 - 70 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (70 + 1) ^ 2 ≤ (70 + 1) ^ 222 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 70 < (70 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((70 + 1) ^ 222 - 70 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_71 (hp : Nat.Prime ((71 + 1) ^ (Nat.totient (1408 - 71) / 2) - 71)) : False := by
  have ht : Nat.totient (1408 - 71) / 2 = 570 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((71 + 1) ^ 570 - 71 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (71 + 1) ^ 2 ≤ (71 + 1) ^ 570 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 71 < (71 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((71 + 1) ^ 570 - 71 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_72 (hp : Nat.Prime ((72 + 1) ^ (Nat.totient (1408 - 72) / 2) - 72)) : False := by
  have ht : Nat.totient (1408 - 72) / 2 = 332 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((72 + 1) ^ 332 - 72 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (72 + 1) ^ 2 ≤ (72 + 1) ^ 332 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 72 < (72 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((72 + 1) ^ 332 - 72 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_73 (hp : Nat.Prime ((73 + 1) ^ (Nat.totient (1408 - 73) / 2) - 73)) : False := by
  have ht : Nat.totient (1408 - 73) / 2 = 352 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((73 + 1) ^ 352 - 73 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (73 + 1) ^ 2 ≤ (73 + 1) ^ 352 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 73 < (73 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((73 + 1) ^ 352 - 73 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_74 (hp : Nat.Prime ((74 + 1) ^ (Nat.totient (1408 - 74) / 2) - 74)) : False := by
  have ht : Nat.totient (1408 - 74) / 2 = 308 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((74 + 1) ^ 308 - 74 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (74 + 1) ^ 2 ≤ (74 + 1) ^ 308 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 74 < (74 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((74 + 1) ^ 308 - 74 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_75 (hp : Nat.Prime ((75 + 1) ^ (Nat.totient (1408 - 75) / 2) - 75)) : False := by
  have ht : Nat.totient (1408 - 75) / 2 = 630 := by decide
  rw [ht] at hp
  have hd : 660719 ∣ ((75 + 1) ^ 630 - 75 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (75 + 1) ^ 4 ≤ (75 + 1) ^ 630 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 660719 + 75 < (75 + 1) ^ 4 := by norm_num
  have hlt : 660719 < ((75 + 1) ^ 630 - 75 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 660719 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_76 (hp : Nat.Prime ((76 + 1) ^ (Nat.totient (1408 - 76) / 2) - 76)) : False := by
  have ht : Nat.totient (1408 - 76) / 2 = 216 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((76 + 1) ^ 216 - 76 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (76 + 1) ^ 2 ≤ (76 + 1) ^ 216 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 76 < (76 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((76 + 1) ^ 216 - 76 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_77 (hp : Nat.Prime ((77 + 1) ^ (Nat.totient (1408 - 77) / 2) - 77)) : False := by
  have ht : Nat.totient (1408 - 77) / 2 = 605 := by decide
  rw [ht] at hp
  have hd : 61357 ∣ ((77 + 1) ^ 605 - 77 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (77 + 1) ^ 3 ≤ (77 + 1) ^ 605 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 61357 + 77 < (77 + 1) ^ 3 := by norm_num
  have hlt : 61357 < ((77 + 1) ^ 605 - 77 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 61357 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_78 (hp : Nat.Prime ((78 + 1) ^ (Nat.totient (1408 - 78) / 2) - 78)) : False := by
  have ht : Nat.totient (1408 - 78) / 2 = 216 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((78 + 1) ^ 216 - 78 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (78 + 1) ^ 2 ≤ (78 + 1) ^ 216 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 78 < (78 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((78 + 1) ^ 216 - 78 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_79 (hp : Nat.Prime ((79 + 1) ^ (Nat.totient (1408 - 79) / 2) - 79)) : False := by
  have ht : Nat.totient (1408 - 79) / 2 = 442 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((79 + 1) ^ 442 - 79 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (79 + 1) ^ 2 ≤ (79 + 1) ^ 442 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 79 < (79 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((79 + 1) ^ 442 - 79 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_80 (hp : Nat.Prime ((80 + 1) ^ (Nat.totient (1408 - 80) / 2) - 80)) : False := by
  have ht : Nat.totient (1408 - 80) / 2 = 328 := by decide
  rw [ht] at hp
  have hd : 101 ∣ ((80 + 1) ^ 328 - 80 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (80 + 1) ^ 2 ≤ (80 + 1) ^ 328 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 101 + 80 < (80 + 1) ^ 2 := by norm_num
  have hlt : 101 < ((80 + 1) ^ 328 - 80 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 101 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_81 (hp : Nat.Prime ((81 + 1) ^ (Nat.totient (1408 - 81) / 2) - 81)) : False := by
  have ht : Nat.totient (1408 - 81) / 2 = 663 := by decide
  rw [ht] at hp
  have hd : 11 ∣ ((81 + 1) ^ 663 - 81 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (81 + 1) ^ 2 ≤ (81 + 1) ^ 663 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 11 + 81 < (81 + 1) ^ 2 := by norm_num
  have hlt : 11 < ((81 + 1) ^ 663 - 81 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 11 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_82 (hp : Nat.Prime ((82 + 1) ^ (Nat.totient (1408 - 82) / 2) - 82)) : False := by
  have ht : Nat.totient (1408 - 82) / 2 = 192 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((82 + 1) ^ 192 - 82 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (82 + 1) ^ 2 ≤ (82 + 1) ^ 192 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 82 < (82 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((82 + 1) ^ 192 - 82 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_83 (hp : Nat.Prime ((83 + 1) ^ (Nat.totient (1408 - 83) / 2) - 83)) : False := by
  have ht : Nat.totient (1408 - 83) / 2 = 520 := by decide
  rw [ht] at hp
  have hd : 41 ∣ ((83 + 1) ^ 520 - 83 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (83 + 1) ^ 2 ≤ (83 + 1) ^ 520 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 41 + 83 < (83 + 1) ^ 2 := by norm_num
  have hlt : 41 < ((83 + 1) ^ 520 - 83 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 41 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_84 (hp : Nat.Prime ((84 + 1) ^ (Nat.totient (1408 - 84) / 2) - 84)) : False := by
  let N : ℕ := 5107936453918163757264144602051577257414121185886005338395391607121227801932615294179583059492436369272615585485700794681486733768732418148359567759868140497460565021156428719460152120747316441094689398177803284079388294504357126230002821106889365117054425239570578079550126103401255444920911105667656243114006578714491673987093930455894878714681879683967051436970976905592751317445343012987618483177821599031675327689540003253284517855415011642264965149577583460510528304293793780954927846566860932121209418682519402982150232124776854821418043513580010322826212336285503607227260208698658649714187396373432648033485747873783111572265541
  have hN : ((84 + 1) ^ (Nat.totient (1408 - 84) / 2) - 84) = N := by decide
  rw [hN] at hp
  have hndvd : ¬ (N ∣ 2) := by decide
  have hc : Nat.Coprime 2 N := ((hp.coprime_iff_not_dvd).2 hndvd).symm
  have hfer := Nat.ModEq.pow_card_sub_one_eq_one hp hc
  have hbound : N - 1 < 2 ^ 2116 := by decide
  have hpow : powFuel 2 N (N - 1) 2116 = 3932055639753323355671058877877921197494848472601092735999170940757673330699711082307745545791403089499258643365073684779473655008168992507715828908508666984312991800881692031545346231163450247486537260148958206524423016670099538688432039948129062337164016329353138184828090077216640855205809373890737804803368281854062334497806605877398872752840441537462753303897598241394068724728275087318104422286086406713592882122718236947866787416847778500490896068699837574734370056696094141219125149795527281891247814877822745162862722039552907266994780828476195913977719542410088448652874073758653984585602355537488241849392278169434114548698878 := by decide
  have hmod : 2 ^ (N - 1) % N = 3932055639753323355671058877877921197494848472601092735999170940757673330699711082307745545791403089499258643365073684779473655008168992507715828908508666984312991800881692031545346231163450247486537260148958206524423016670099538688432039948129062337164016329353138184828090077216640855205809373890737804803368281854062334497806605877398872752840441537462753303897598241394068724728275087318104422286086406713592882122718236947866787416847778500490896068699837574734370056696094141219125149795527281891247814877822745162862722039552907266994780828476195913977719542410088448652874073758653984585602355537488241849392278169434114548698878 := by
    have h := powFuel_eq 2 N (N - 1) 2116 hbound
    rw [hpow] at h
    exact h.symm
  have hcalc : 2 ^ (N - 1) % N ≠ 1 % N := by
    rw [hmod]
    decide
  exact hcalc hfer

private theorem no_prime_1408_85 (hp : Nat.Prime ((85 + 1) ^ (Nat.totient (1408 - 85) / 2) - 85)) : False := by
  have ht : Nat.totient (1408 - 85) / 2 = 378 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((85 + 1) ^ 378 - 85 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (85 + 1) ^ 2 ≤ (85 + 1) ^ 378 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 85 < (85 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((85 + 1) ^ 378 - 85 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_86 (hp : Nat.Prime ((86 + 1) ^ (Nat.totient (1408 - 86) / 2) - 86)) : False := by
  have ht : Nat.totient (1408 - 86) / 2 = 330 := by decide
  rw [ht] at hp
  have hd : 8719 ∣ ((86 + 1) ^ 330 - 86 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (86 + 1) ^ 3 ≤ (86 + 1) ^ 330 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 8719 + 86 < (86 + 1) ^ 3 := by norm_num
  have hlt : 8719 < ((86 + 1) ^ 330 - 86 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 8719 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_87 (hp : Nat.Prime ((87 + 1) ^ (Nat.totient (1408 - 87) / 2) - 87)) : False := by
  have ht : Nat.totient (1408 - 87) / 2 = 660 := by decide
  rw [ht] at hp
  have hd : 101 ∣ ((87 + 1) ^ 660 - 87 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (87 + 1) ^ 2 ≤ (87 + 1) ^ 660 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 101 + 87 < (87 + 1) ^ 2 := by norm_num
  have hlt : 101 < ((87 + 1) ^ 660 - 87 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 101 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_88 (hp : Nat.Prime ((88 + 1) ^ (Nat.totient (1408 - 88) / 2) - 88)) : False := by
  have ht : Nat.totient (1408 - 88) / 2 = 160 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((88 + 1) ^ 160 - 88 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (88 + 1) ^ 2 ≤ (88 + 1) ^ 160 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 88 < (88 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((88 + 1) ^ 160 - 88 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_89 (hp : Nat.Prime ((89 + 1) ^ (Nat.totient (1408 - 89) / 2) - 89)) : False := by
  have ht : Nat.totient (1408 - 89) / 2 = 659 := by decide
  rw [ht] at hp
  have hd : 19 ∣ ((89 + 1) ^ 659 - 89 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (89 + 1) ^ 2 ≤ (89 + 1) ^ 659 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 19 + 89 < (89 + 1) ^ 2 := by norm_num
  have hlt : 19 < ((89 + 1) ^ 659 - 89 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 19 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_90 (hp : Nat.Prime ((90 + 1) ^ (Nat.totient (1408 - 90) / 2) - 90)) : False := by
  have ht : Nat.totient (1408 - 90) / 2 = 329 := by decide
  rw [ht] at hp
  have hd : 313 ∣ ((90 + 1) ^ 329 - 90 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (90 + 1) ^ 2 ≤ (90 + 1) ^ 329 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 313 + 90 < (90 + 1) ^ 2 := by norm_num
  have hlt : 313 < ((90 + 1) ^ 329 - 90 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 313 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_91 (hp : Nat.Prime ((91 + 1) ^ (Nat.totient (1408 - 91) / 2) - 91)) : False := by
  have ht : Nat.totient (1408 - 91) / 2 = 438 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((91 + 1) ^ 438 - 91 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (91 + 1) ^ 2 ≤ (91 + 1) ^ 438 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 91 < (91 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((91 + 1) ^ 438 - 91 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_92 (hp : Nat.Prime ((92 + 1) ^ (Nat.totient (1408 - 92) / 2) - 92)) : False := by
  have ht : Nat.totient (1408 - 92) / 2 = 276 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((92 + 1) ^ 276 - 92 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (92 + 1) ^ 2 ≤ (92 + 1) ^ 276 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 92 < (92 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((92 + 1) ^ 276 - 92 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_93 (hp : Nat.Prime ((93 + 1) ^ (Nat.totient (1408 - 93) / 2) - 93)) : False := by
  have ht : Nat.totient (1408 - 93) / 2 = 524 := by decide
  rw [ht] at hp
  have hd : 7 ∣ ((93 + 1) ^ 524 - 93 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (93 + 1) ^ 2 ≤ (93 + 1) ^ 524 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 7 + 93 < (93 + 1) ^ 2 := by norm_num
  have hlt : 7 < ((93 + 1) ^ 524 - 93 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 7 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_94 (hp : Nat.Prime ((94 + 1) ^ (Nat.totient (1408 - 94) / 2) - 94)) : False := by
  have ht : Nat.totient (1408 - 94) / 2 = 216 := by decide
  rw [ht] at hp
  have hd : 3 ∣ ((94 + 1) ^ 216 - 94 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  have hpowle : (94 + 1) ^ 2 ≤ (94 + 1) ^ 216 := by
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsmall : 3 + 94 < (94 + 1) ^ 2 := by norm_num
  have hlt : 3 < ((94 + 1) ^ 216 - 94 : ℕ) := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hd with hone | hself
  · norm_num at hone
  · omega

private theorem no_prime_1408_95 (hp : Nat.Prime ((95 + 1) ^ (Nat.totient (1408 - 95) / 2) - 95)) : False := by
  let N : ℕ := 23053656811411589166859421315793512416266162573879036820835334586231252298121550225747900003155399043619977930259665086011100278134410269652888506478100947227386565863546625151707259586912013728105146318634851853251027380583879386813764017807115107010895343796217886234617704858874578052896459642729675298850306291530654687181676811909053198529582963206540031697329292393395940783140757694953468348541204661226180970725551257430642128789596983019676430179802473642945867183485302082587340938163215112708939210079422679436569673564632984511550229290835053466376431031873012635601950967739198702209455538499138598039465782372877777785879760304167637736083220435402310374511803888001747135826166123047488744438237501160482572437496544518096608639620297260730462023505858499616967739535283667962568405745663304534855207729528268348222393019563850051470891131901287947185898472750335405230470763788626645328416664779442091652153127321230472655690420807717241413239369527747318900306054179438013391510744935709978325052665763347314835590555558811699704164725656745050286131264498236941177655569903600336353079861060138889530949610613324723780927064264113797070462259494922947820170575266107621281
  have hN : ((95 + 1) ^ (Nat.totient (1408 - 95) / 2) - 95) = N := by decide
  rw [hN] at hp
  have hndvd : ¬ (N ∣ 2) := by decide
  have hc : Nat.Coprime 2 N := ((hp.coprime_iff_not_dvd).2 hndvd).symm
  have hfer := Nat.ModEq.pow_card_sub_one_eq_one hp hc
  have hbound : N - 1 < 2 ^ 3951 := by decide
  have hpow : powFuel 2 N (N - 1) 3951 = 10897982377678829155632041183200305513219160730664068659172311634092128566901394476966350251750666433008763263930434959028600093830944582526525315742754278106190003931257553414079804129970470090018148498508610648590697150434081239052099166711919438156765552387234406942370922825105476827342250774346179345688034160186511507364774893429009694915428693654884792384476683896663876903664836723742373759668479542817173795356398911992563695757871651879150712078629488420291079411979512819869573738526475393465138814392947870175558349781369888062330290768991997099271399070284767730984726816079106127180097106378418267313571230665606004427334480824931042211993829333203943816662760974571468076422486397330291198896483012055273293444316194410038278871438055260346427562773443973729524708238003097843438592627902222750930705670704583694570371552496162425267178945512175618020232793594227870203917634989475533203362758524395364486431020680512263390731346945893066698787250348384654178919886420614292453209271279359758765368140063970459314901475360963688923570626892446032528555838793277579296960245540123031266191319732333309726293539717624981814779203793241050591147378971274548919800988735454457203 := by decide
  have hmod : 2 ^ (N - 1) % N = 10897982377678829155632041183200305513219160730664068659172311634092128566901394476966350251750666433008763263930434959028600093830944582526525315742754278106190003931257553414079804129970470090018148498508610648590697150434081239052099166711919438156765552387234406942370922825105476827342250774346179345688034160186511507364774893429009694915428693654884792384476683896663876903664836723742373759668479542817173795356398911992563695757871651879150712078629488420291079411979512819869573738526475393465138814392947870175558349781369888062330290768991997099271399070284767730984726816079106127180097106378418267313571230665606004427334480824931042211993829333203943816662760974571468076422486397330291198896483012055273293444316194410038278871438055260346427562773443973729524708238003097843438592627902222750930705670704583694570371552496162425267178945512175618020232793594227870203917634989475533203362758524395364486431020680512263390731346945893066698787250348384654178919886420614292453209271279359758765368140063970459314901475360963688923570626892446032528555838793277579296960245540123031266191319732333309726293539717624981814779203793241050591147378971274548919800988735454457203 := by
    have h := powFuel_eq 2 N (N - 1) 3951 hbound
    rw [hpow] at h
    exact h.symm
  have hcalc : 2 ^ (N - 1) % N ≠ 1 % N := by
    rw [hmod]
    decide
  exact hcalc hfer

