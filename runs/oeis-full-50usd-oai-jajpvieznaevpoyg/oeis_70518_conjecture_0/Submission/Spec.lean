import FormalConjectures.Util.ProblemImports


open Polynomial

/--
A070518: Value of $n$-th cyclotomic polynomial at $n$.
$$ a(n) = \Phi_n(n) $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Polynomial.eval (Int.ofNat n) (cyclotomic n ℤ)).natAbs

private lemma prime_dvd_28341 {q : ℕ} (hq : Nat.Prime q) (hdvd : q ∣ 28341) :
    q = 3 ∨ q = 47 ∨ q = 67 := by
  have hfac : 28341 = 3 ^ 2 * 47 * 67 := by norm_num
  rw [hfac] at hdvd
  rcases hq.dvd_mul.mp hdvd with h | h
  · rcases hq.dvd_mul.mp h with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h)
    · right; left
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 47)).mp h
  · right; right
    exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 67)).mp h

private lemma zmod_intCast_unit_mod_prime_sq_of_ne_zero_mod_prime {p : ℕ} (hp : Nat.Prime p)
    {z : ℤ} (hz : (z : ZMod p) ≠ 0) : IsUnit (z : ZMod (p ^ 2)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  have hcop : IsCoprime (p : ℤ) z := by
    rw [(Nat.prime_iff_prime_int).mp hp |>.coprime_iff_not_dvd]
    intro hdiv
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).2 hdiv)
  simpa using hcop.pow_left

private lemma eval_cyclotomic_intCast (m N x : ℕ) :
    Polynomial.eval (x : ZMod N) (cyclotomic m (ZMod N)) =
      ((Polynomial.eval (Int.ofNat x) (cyclotomic m ℤ) : ℤ) : ZMod N) := by
  have h := Polynomial.eval_intCast_map (Int.castRingHom (ZMod N)) (cyclotomic m ℤ)
    (Int.ofNat x)
  rw [Polynomial.map_cyclotomic_int] at h
  simpa using h

private lemma zmod_mul_eq_of_modEq (M a b r : ℕ) (h : (a * b) % M = r % M) :
    ((a : ZMod M) * (b : ZMod M) = (r : ZMod M)) := by
  rw [← Nat.cast_mul]
  change (((a * b : ℕ) : ZMod M) = ((r : ℕ) : ZMod M))
  rw [ZMod.natCast_eq_natCast_iff]
  exact h

private lemma zmod_pow_add_eq_of (M n e f r s t : ℕ)
    (he : ((n : ZMod M) ^ e = (r : ZMod M)))
    (hf : ((n : ZMod M) ^ f = (s : ZMod M)))
    (hmod : (r * s) % M = t % M) :
    ((n : ZMod M) ^ (e + f) = (t : ZMod M)) := by
  rw [pow_add, he, hf]
  exact zmod_mul_eq_of_modEq M r s t hmod

private lemma zmod_natCast_ne_of_mod_ne (M a b : ℕ) (h : a % M ≠ b % M) :
    ((a : ZMod M) ≠ (b : ZMod M)) := by
  intro heq
  rw [ZMod.natCast_eq_natCast_iff] at heq
  rw [Nat.ModEq] at heq
  exact h heq

private lemma zmod_283411_pow_28341 : ((28341 : ZMod 283411) ^ 28341 = (1 : ZMod 283411)) := by
  have h0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := by simp
  have h1 : ((28341 : ZMod 283411) ^ 2 = (25507 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 1 28341 28341 25507 h0 h0 (by norm_num)
  have h2 : ((28341 : ZMod 283411) ^ 4 = (178804 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 2 2 25507 25507 178804 h1 h1 (by norm_num)
  have h3 : ((28341 : ZMod 283411) ^ 8 = (125739 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 4 4 178804 178804 125739 h2 h2 (by norm_num)
  have h4 : ((28341 : ZMod 283411) ^ 16 = (213486 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 8 8 125739 125739 213486 h3 h3 (by norm_num)
  have h5 : ((28341 : ZMod 283411) ^ 32 = (99053 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 16 16 213486 213486 99053 h4 h4 (by norm_num)
  have h6 : ((28341 : ZMod 283411) ^ 64 = (91400 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 32 32 99053 99053 91400 h5 h5 (by norm_num)
  have h7 : ((28341 : ZMod 283411) ^ 128 = (137364 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 64 64 91400 91400 137364 h6 h6 (by norm_num)
  have h8 : ((28341 : ZMod 283411) ^ 256 = (214349 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 128 128 137364 137364 214349 h7 h7 (by norm_num)
  have h9 : ((28341 : ZMod 283411) ^ 512 = (36125 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 256 256 214349 214349 36125 h8 h8 (by norm_num)
  have h10 : ((28341 : ZMod 283411) ^ 1024 = (191381 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 512 512 36125 36125 191381 h9 h9 (by norm_num)
  have h11 : ((28341 : ZMod 283411) ^ 2048 = (66576 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1024 1024 191381 191381 66576 h10 h10 (by norm_num)
  have h12 : ((28341 : ZMod 283411) ^ 4096 = (99147 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 2048 2048 66576 66576 99147 h11 h11 (by norm_num)
  have h13 : ((28341 : ZMod 283411) ^ 8192 = (17074 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 4096 4096 99147 99147 17074 h12 h12 (by norm_num)
  have h14 : ((28341 : ZMod 283411) ^ 16384 = (174968 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 8192 8192 17074 17074 174968 h13 h13 (by norm_num)
  have a0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := h0
  have a1 : ((28341 : ZMod 283411) ^ 5 = (95484 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 4 28341 178804 95484 a0 h2 (by norm_num)
  have a2 : ((28341 : ZMod 283411) ^ 21 = (161049 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 5 16 95484 213486 161049 a1 h4 (by norm_num)
  have a3 : ((28341 : ZMod 283411) ^ 53 = (31640 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 21 32 161049 99053 31640 a2 h5 (by norm_num)
  have a4 : ((28341 : ZMod 283411) ^ 181 = (89275 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 53 128 31640 137364 89275 a3 h7 (by norm_num)
  have a5 : ((28341 : ZMod 283411) ^ 693 = (125606 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 181 512 89275 36125 125606 a4 h9 (by norm_num)
  have a6 : ((28341 : ZMod 283411) ^ 1717 = (247688 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 693 1024 125606 191381 247688 a5 h10 (by norm_num)
  have a7 : ((28341 : ZMod 283411) ^ 3765 = (90664 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1717 2048 247688 66576 90664 a6 h11 (by norm_num)
  have a8 : ((28341 : ZMod 283411) ^ 11957 = (6254 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 3765 8192 90664 17074 6254 a7 h13 (by norm_num)
  have a9 : ((28341 : ZMod 283411) ^ 28341 = (1 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 11957 16384 6254 174968 1 a8 h14 (by norm_num)
  simpa using a9

private lemma zmod_283411_pow_9447 : ((28341 : ZMod 283411) ^ 9447 = (153836 : ZMod 283411)) := by
  have h0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := by simp
  have h1 : ((28341 : ZMod 283411) ^ 2 = (25507 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 1 28341 28341 25507 h0 h0 (by norm_num)
  have h2 : ((28341 : ZMod 283411) ^ 4 = (178804 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 2 2 25507 25507 178804 h1 h1 (by norm_num)
  have h3 : ((28341 : ZMod 283411) ^ 8 = (125739 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 4 4 178804 178804 125739 h2 h2 (by norm_num)
  have h4 : ((28341 : ZMod 283411) ^ 16 = (213486 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 8 8 125739 125739 213486 h3 h3 (by norm_num)
  have h5 : ((28341 : ZMod 283411) ^ 32 = (99053 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 16 16 213486 213486 99053 h4 h4 (by norm_num)
  have h6 : ((28341 : ZMod 283411) ^ 64 = (91400 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 32 32 99053 99053 91400 h5 h5 (by norm_num)
  have h7 : ((28341 : ZMod 283411) ^ 128 = (137364 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 64 64 91400 91400 137364 h6 h6 (by norm_num)
  have h8 : ((28341 : ZMod 283411) ^ 256 = (214349 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 128 128 137364 137364 214349 h7 h7 (by norm_num)
  have h9 : ((28341 : ZMod 283411) ^ 512 = (36125 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 256 256 214349 214349 36125 h8 h8 (by norm_num)
  have h10 : ((28341 : ZMod 283411) ^ 1024 = (191381 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 512 512 36125 36125 191381 h9 h9 (by norm_num)
  have h11 : ((28341 : ZMod 283411) ^ 2048 = (66576 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1024 1024 191381 191381 66576 h10 h10 (by norm_num)
  have h12 : ((28341 : ZMod 283411) ^ 4096 = (99147 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 2048 2048 66576 66576 99147 h11 h11 (by norm_num)
  have h13 : ((28341 : ZMod 283411) ^ 8192 = (17074 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 4096 4096 99147 99147 17074 h12 h12 (by norm_num)
  have a0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := h0
  have a1 : ((28341 : ZMod 283411) ^ 3 = (195837 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 2 28341 25507 195837 a0 h1 (by norm_num)
  have a2 : ((28341 : ZMod 283411) ^ 7 = (159665 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 3 4 195837 178804 159665 a1 h2 (by norm_num)
  have a3 : ((28341 : ZMod 283411) ^ 39 = (113212 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 7 32 159665 99053 113212 a2 h5 (by norm_num)
  have a4 : ((28341 : ZMod 283411) ^ 103 = (241190 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 39 64 113212 91400 241190 a3 h6 (by norm_num)
  have a5 : ((28341 : ZMod 283411) ^ 231 = (77260 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 103 128 241190 137364 77260 a4 h7 (by norm_num)
  have a6 : ((28341 : ZMod 283411) ^ 1255 = (260779 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 231 1024 77260 191381 260779 a5 h10 (by norm_num)
  have a7 : ((28341 : ZMod 283411) ^ 9447 = (153836 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1255 8192 260779 17074 153836 a6 h13 (by norm_num)
  simpa using a7

private lemma zmod_283411_pow_603 : ((28341 : ZMod 283411) ^ 603 = (168687 : ZMod 283411)) := by
  have h0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := by simp
  have h1 : ((28341 : ZMod 283411) ^ 2 = (25507 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 1 28341 28341 25507 h0 h0 (by norm_num)
  have h2 : ((28341 : ZMod 283411) ^ 4 = (178804 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 2 2 25507 25507 178804 h1 h1 (by norm_num)
  have h3 : ((28341 : ZMod 283411) ^ 8 = (125739 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 4 4 178804 178804 125739 h2 h2 (by norm_num)
  have h4 : ((28341 : ZMod 283411) ^ 16 = (213486 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 8 8 125739 125739 213486 h3 h3 (by norm_num)
  have h5 : ((28341 : ZMod 283411) ^ 32 = (99053 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 16 16 213486 213486 99053 h4 h4 (by norm_num)
  have h6 : ((28341 : ZMod 283411) ^ 64 = (91400 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 32 32 99053 99053 91400 h5 h5 (by norm_num)
  have h7 : ((28341 : ZMod 283411) ^ 128 = (137364 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 64 64 91400 91400 137364 h6 h6 (by norm_num)
  have h8 : ((28341 : ZMod 283411) ^ 256 = (214349 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 128 128 137364 137364 214349 h7 h7 (by norm_num)
  have h9 : ((28341 : ZMod 283411) ^ 512 = (36125 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 256 256 214349 214349 36125 h8 h8 (by norm_num)
  have a0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := h0
  have a1 : ((28341 : ZMod 283411) ^ 3 = (195837 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 2 28341 25507 195837 a0 h1 (by norm_num)
  have a2 : ((28341 : ZMod 283411) ^ 11 = (183808 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 3 8 195837 125739 183808 a1 h3 (by norm_num)
  have a3 : ((28341 : ZMod 283411) ^ 27 = (197861 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 11 16 183808 213486 197861 a2 h4 (by norm_num)
  have a4 : ((28341 : ZMod 283411) ^ 91 = (39490 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 27 64 197861 91400 39490 a3 h6 (by norm_num)
  have a5 : ((28341 : ZMod 283411) ^ 603 = (168687 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 91 512 39490 36125 168687 a4 h9 (by norm_num)
  simpa using a5

private lemma zmod_283411_pow_423 : ((28341 : ZMod 283411) ^ 423 = (196258 : ZMod 283411)) := by
  have h0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := by simp
  have h1 : ((28341 : ZMod 283411) ^ 2 = (25507 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 1 28341 28341 25507 h0 h0 (by norm_num)
  have h2 : ((28341 : ZMod 283411) ^ 4 = (178804 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 2 2 25507 25507 178804 h1 h1 (by norm_num)
  have h3 : ((28341 : ZMod 283411) ^ 8 = (125739 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 4 4 178804 178804 125739 h2 h2 (by norm_num)
  have h4 : ((28341 : ZMod 283411) ^ 16 = (213486 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 8 8 125739 125739 213486 h3 h3 (by norm_num)
  have h5 : ((28341 : ZMod 283411) ^ 32 = (99053 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 16 16 213486 213486 99053 h4 h4 (by norm_num)
  have h6 : ((28341 : ZMod 283411) ^ 64 = (91400 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 32 32 99053 99053 91400 h5 h5 (by norm_num)
  have h7 : ((28341 : ZMod 283411) ^ 128 = (137364 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 64 64 91400 91400 137364 h6 h6 (by norm_num)
  have h8 : ((28341 : ZMod 283411) ^ 256 = (214349 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 128 128 137364 137364 214349 h7 h7 (by norm_num)
  have a0 : ((28341 : ZMod 283411) ^ 1 = (28341 : ZMod 283411)) := h0
  have a1 : ((28341 : ZMod 283411) ^ 3 = (195837 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 1 2 28341 25507 195837 a0 h1 (by norm_num)
  have a2 : ((28341 : ZMod 283411) ^ 7 = (159665 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 3 4 195837 178804 159665 a1 h2 (by norm_num)
  have a3 : ((28341 : ZMod 283411) ^ 39 = (113212 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 7 32 159665 99053 113212 a2 h5 (by norm_num)
  have a4 : ((28341 : ZMod 283411) ^ 167 = (208187 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 39 128 113212 137364 208187 a3 h7 (by norm_num)
  have a5 : ((28341 : ZMod 283411) ^ 423 = (196258 : ZMod 283411)) := by
    simpa using zmod_pow_add_eq_of 283411 28341 167 256 208187 214349 196258 a4 h8 (by norm_num)
  simpa using a5

private lemma zmod_80321794921_pow_28341 : ((28341 : ZMod 80321794921) ^ 28341 = (1 : ZMod 80321794921)) := by
  have h0 : ((28341 : ZMod 80321794921) ^ 1 = (28341 : ZMod 80321794921)) := by simp
  have h1 : ((28341 : ZMod 80321794921) ^ 2 = (803212281 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 1 1 28341 28341 803212281 h0 h0 (by norm_num)
  have h2 : ((28341 : ZMod 80321794921) ^ 4 = (10305286175 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 2 2 803212281 803212281 10305286175 h1 h1 (by norm_num)
  have h3 : ((28341 : ZMod 80321794921) ^ 8 = (56856623504 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 4 4 10305286175 10305286175 56856623504 h2 h2 (by norm_num)
  have h4 : ((28341 : ZMod 80321794921) ^ 16 = (11119560660 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 8 8 56856623504 56856623504 11119560660 h3 h3 (by norm_num)
  have h5 : ((28341 : ZMod 80321794921) ^ 32 = (34823658856 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 16 16 11119560660 11119560660 34823658856 h4 h4 (by norm_num)
  have h6 : ((28341 : ZMod 80321794921) ^ 64 = (7305860158 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 32 32 34823658856 34823658856 7305860158 h5 h5 (by norm_num)
  have h7 : ((28341 : ZMod 80321794921) ^ 128 = (72720565854 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 64 64 7305860158 7305860158 72720565854 h6 h6 (by norm_num)
  have h8 : ((28341 : ZMod 80321794921) ^ 256 = (77339958728 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 128 128 72720565854 72720565854 77339958728 h7 h7 (by norm_num)
  have h9 : ((28341 : ZMod 80321794921) ^ 512 = (48530202121 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 256 256 77339958728 77339958728 48530202121 h8 h8 (by norm_num)
  have h10 : ((28341 : ZMod 80321794921) ^ 1024 = (18484540212 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 512 512 48530202121 48530202121 18484540212 h9 h9 (by norm_num)
  have h11 : ((28341 : ZMod 80321794921) ^ 2048 = (77970117019 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 1024 1024 18484540212 18484540212 77970117019 h10 h10 (by norm_num)
  have h12 : ((28341 : ZMod 80321794921) ^ 4096 = (39630026099 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 2048 2048 77970117019 77970117019 39630026099 h11 h11 (by norm_num)
  have h13 : ((28341 : ZMod 80321794921) ^ 8192 = (23437256541 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 4096 4096 39630026099 39630026099 23437256541 h12 h12 (by norm_num)
  have h14 : ((28341 : ZMod 80321794921) ^ 16384 = (8780247748 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 8192 8192 23437256541 23437256541 8780247748 h13 h13 (by norm_num)
  have a0 : ((28341 : ZMod 80321794921) ^ 1 = (28341 : ZMod 80321794921)) := h0
  have a1 : ((28341 : ZMod 80321794921) ^ 5 = (12069152919 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 1 4 28341 10305286175 12069152919 a0 h2 (by norm_num)
  have a2 : ((28341 : ZMod 80321794921) ^ 21 = (58902886234 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 5 16 12069152919 11119560660 58902886234 a1 h4 (by norm_num)
  have a3 : ((28341 : ZMod 80321794921) ^ 53 = (3524814247 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 21 32 58902886234 34823658856 3524814247 a2 h5 (by norm_num)
  have a4 : ((28341 : ZMod 80321794921) ^ 181 = (59346352675 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 53 128 3524814247 72720565854 59346352675 a3 h7 (by norm_num)
  have a5 : ((28341 : ZMod 80321794921) ^ 693 = (71235197045 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 181 512 59346352675 48530202121 71235197045 a4 h9 (by norm_num)
  have a6 : ((28341 : ZMod 80321794921) ^ 1717 = (8309007975 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 693 1024 71235197045 18484540212 8309007975 a5 h10 (by norm_num)
  have a7 : ((28341 : ZMod 80321794921) ^ 3765 = (79405617822 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 1717 2048 8309007975 77970117019 79405617822 a6 h11 (by norm_num)
  have a8 : ((28341 : ZMod 80321794921) ^ 11957 = (20736622302 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 3765 8192 79405617822 23437256541 20736622302 a7 h13 (by norm_num)
  have a9 : ((28341 : ZMod 80321794921) ^ 28341 = (1 : ZMod 80321794921)) := by
    simpa using zmod_pow_add_eq_of 80321794921 28341 11957 16384 20736622302 8780247748 1 a8 h14 (by norm_num)
  simpa using a9


private lemma zmod_283411_sq_pow_28341 : ((28341 : ZMod (283411 ^ 2)) ^ 28341 = (1 : ZMod (283411 ^ 2))) := by
  have h0 : ((28341 : ZMod (283411 ^ 2)) ^ 1 = (28341 : ZMod (283411 ^ 2))) := by simp
  have h1 : ((28341 : ZMod (283411 ^ 2)) ^ 2 = (803212281 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 1 1 28341 28341 803212281 h0 h0 (by norm_num)
  have h2 : ((28341 : ZMod (283411 ^ 2)) ^ 4 = (10305286175 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 2 2 803212281 803212281 10305286175 h1 h1 (by norm_num)
  have h3 : ((28341 : ZMod (283411 ^ 2)) ^ 8 = (56856623504 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 4 4 10305286175 10305286175 56856623504 h2 h2 (by norm_num)
  have h4 : ((28341 : ZMod (283411 ^ 2)) ^ 16 = (11119560660 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 8 8 56856623504 56856623504 11119560660 h3 h3 (by norm_num)
  have h5 : ((28341 : ZMod (283411 ^ 2)) ^ 32 = (34823658856 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 16 16 11119560660 11119560660 34823658856 h4 h4 (by norm_num)
  have h6 : ((28341 : ZMod (283411 ^ 2)) ^ 64 = (7305860158 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 32 32 34823658856 34823658856 7305860158 h5 h5 (by norm_num)
  have h7 : ((28341 : ZMod (283411 ^ 2)) ^ 128 = (72720565854 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 64 64 7305860158 7305860158 72720565854 h6 h6 (by norm_num)
  have h8 : ((28341 : ZMod (283411 ^ 2)) ^ 256 = (77339958728 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 128 128 72720565854 72720565854 77339958728 h7 h7 (by norm_num)
  have h9 : ((28341 : ZMod (283411 ^ 2)) ^ 512 = (48530202121 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 256 256 77339958728 77339958728 48530202121 h8 h8 (by norm_num)
  have h10 : ((28341 : ZMod (283411 ^ 2)) ^ 1024 = (18484540212 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 512 512 48530202121 48530202121 18484540212 h9 h9 (by norm_num)
  have h11 : ((28341 : ZMod (283411 ^ 2)) ^ 2048 = (77970117019 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 1024 1024 18484540212 18484540212 77970117019 h10 h10 (by norm_num)
  have h12 : ((28341 : ZMod (283411 ^ 2)) ^ 4096 = (39630026099 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 2048 2048 77970117019 77970117019 39630026099 h11 h11 (by norm_num)
  have h13 : ((28341 : ZMod (283411 ^ 2)) ^ 8192 = (23437256541 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 4096 4096 39630026099 39630026099 23437256541 h12 h12 (by norm_num)
  have h14 : ((28341 : ZMod (283411 ^ 2)) ^ 16384 = (8780247748 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 8192 8192 23437256541 23437256541 8780247748 h13 h13 (by norm_num)
  have a0 : ((28341 : ZMod (283411 ^ 2)) ^ 1 = (28341 : ZMod (283411 ^ 2))) := h0
  have a1 : ((28341 : ZMod (283411 ^ 2)) ^ 5 = (12069152919 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 1 4 28341 10305286175 12069152919 a0 h2 (by norm_num)
  have a2 : ((28341 : ZMod (283411 ^ 2)) ^ 21 = (58902886234 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 5 16 12069152919 11119560660 58902886234 a1 h4 (by norm_num)
  have a3 : ((28341 : ZMod (283411 ^ 2)) ^ 53 = (3524814247 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 21 32 58902886234 34823658856 3524814247 a2 h5 (by norm_num)
  have a4 : ((28341 : ZMod (283411 ^ 2)) ^ 181 = (59346352675 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 53 128 3524814247 72720565854 59346352675 a3 h7 (by norm_num)
  have a5 : ((28341 : ZMod (283411 ^ 2)) ^ 693 = (71235197045 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 181 512 59346352675 48530202121 71235197045 a4 h9 (by norm_num)
  have a6 : ((28341 : ZMod (283411 ^ 2)) ^ 1717 = (8309007975 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 693 1024 71235197045 18484540212 8309007975 a5 h10 (by norm_num)
  have a7 : ((28341 : ZMod (283411 ^ 2)) ^ 3765 = (79405617822 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 1717 2048 8309007975 77970117019 79405617822 a6 h11 (by norm_num)
  have a8 : ((28341 : ZMod (283411 ^ 2)) ^ 11957 = (20736622302 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 3765 8192 79405617822 23437256541 20736622302 a7 h13 (by norm_num)
  have a9 : ((28341 : ZMod (283411 ^ 2)) ^ 28341 = (1 : ZMod (283411 ^ 2))) := by
    simpa using zmod_pow_add_eq_of (283411 ^ 2) 28341 11957 16384 20736622302 8780247748 1 a8 h14 (by norm_num)
  simpa using a9


/--
A070518 a(28341) is divisible by 283411^2. What is the next n such that a(n) is not squarefree? - _Jianing Song_, Nov 01 2024
-/
theorem oeis_70518_conjecture_0 :
  (283411 : ℕ) ^ 2 ∣ a 28341 :=
by
  have hp : Nat.Prime 283411 := by norm_num
  have hnpos : 0 < 28341 := by norm_num
  have hpow_p : (28341 : ZMod 283411) ^ 28341 = 1 := by
    exact zmod_283411_pow_28341
  have hnot_p : ∀ q : ℕ, Nat.Prime q → q ∣ 28341 →
      (28341 : ZMod 283411) ^ (28341 / q) ≠ 1 := by
    intro q hq hqdn
    have hq' : q = 3 ∨ q = 47 ∨ q = 67 := prime_dvd_28341 hq hqdn
    rcases hq' with rfl | rfl | rfl
    · rw [show 28341 / 3 = 9447 by norm_num]
      rw [zmod_283411_pow_9447]
      exact zmod_natCast_ne_of_mod_ne 283411 153836 1 (by norm_num)
    · rw [show 28341 / 47 = 603 by norm_num]
      rw [zmod_283411_pow_603]
      exact zmod_natCast_ne_of_mod_ne 283411 168687 1 (by norm_num)
    · rw [show 28341 / 67 = 423 by norm_num]
      rw [zmod_283411_pow_423]
      exact zmod_natCast_ne_of_mod_ne 283411 196258 1 (by norm_num)
  have horder : orderOf (28341 : ZMod 283411) = 28341 :=
    orderOf_eq_of_pow_and_pow_div_prime hnpos hpow_p hnot_p
  have hnonzero_mod_p : ∀ d ∈ Nat.properDivisors 28341,
      ((Polynomial.eval (Int.ofNat 28341) (cyclotomic d ℤ) : ℤ) : ZMod 283411) ≠ 0 := by
    intro d hd hzero
    have hd_lt : d < 28341 := (Nat.mem_properDivisors.mp hd).2
    have hd_pos : 0 < d := Nat.pos_of_mem_properDivisors hd
    have hroot : (cyclotomic d (ZMod 283411)).IsRoot (28341 : ZMod 283411) := by
      rw [Polynomial.IsRoot.def]
      change Polynomial.eval ((28341 : ℕ) : ZMod 283411) (cyclotomic d (ZMod 283411)) = 0
      rw [eval_cyclotomic_intCast]
      exact hzero
    haveI : Fact (Nat.Prime 283411) := ⟨hp⟩
    have hdiv_order := Polynomial.orderOf_root_cyclotomic_dvd hd_pos (p := 283411) (a := 28341) hroot
    have horder_unit : orderOf (ZMod.unitOfCoprime 28341
        (Polynomial.coprime_of_root_cyclotomic hd_pos hroot)) = 28341 := by
      rw [← orderOf_units]
      simpa [ZMod.coe_unitOfCoprime] using horder
    have hndvd : 28341 ∣ d := by
      simpa [horder_unit] using hdiv_order
    exact (not_le_of_gt hd_lt) (Nat.le_of_dvd hd_pos hndvd)
  have hunit_prod : IsUnit
      (∏ d ∈ Nat.properDivisors 28341,
        Polynomial.eval (28341 : ZMod (283411 ^ 2)) (cyclotomic d (ZMod (283411 ^ 2)))) := by
    rw [IsUnit.prod_iff]
    intro d hd
    change IsUnit (Polynomial.eval ((28341 : ℕ) : ZMod (283411 ^ 2))
      (cyclotomic d (ZMod (283411 ^ 2))))
    rw [eval_cyclotomic_intCast]
    exact zmod_intCast_unit_mod_prime_sq_of_ne_zero_mod_prime hp (hnonzero_mod_p d hd)
  have hroot_mod_p2 : Polynomial.eval (28341 : ZMod (283411 ^ 2))
      (cyclotomic 28341 (ZMod (283411 ^ 2))) = 0 := by
    have hprod := congr_arg (Polynomial.eval (28341 : ZMod (283411 ^ 2)))
      (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hnpos (ZMod (283411 ^ 2)))
    rw [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hprod
    rw [← Nat.cons_self_properDivisors (by norm_num : 28341 ≠ 0), Finset.prod_cons] at hprod
    have hpow_p2 : (28341 : ZMod (283411 ^ 2)) ^ 28341 = 1 := by
      exact zmod_283411_sq_pow_28341
    rw [hpow_p2, sub_self] at hprod
    exact hunit_prod.mul_left_eq_zero.mp hprod
  have hcast_zero : ((Polynomial.eval (Int.ofNat 28341) (cyclotomic 28341 ℤ) : ℤ) :
      ZMod (283411 ^ 2)) = 0 := by
    rw [← eval_cyclotomic_intCast]
    exact hroot_mod_p2
  have hdiv_int : (((283411 : ℕ) ^ 2 : ℕ) : ℤ) ∣
      Polynomial.eval (Int.ofNat 28341) (cyclotomic 28341 ℤ) := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (Polynomial.eval (Int.ofNat 28341) (cyclotomic 28341 ℤ)) (283411 ^ 2)).mp hcast_zero
  have hdiv_nat : (283411 : ℕ) ^ 2 ∣
      (Polynomial.eval (Int.ofNat 28341) (cyclotomic 28341 ℤ)).natAbs :=
    Int.natCast_dvd.mp hdiv_int
  simpa [a] using hdiv_nat
