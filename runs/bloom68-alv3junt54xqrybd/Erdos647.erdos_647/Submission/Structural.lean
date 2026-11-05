import FormalConjecturesUtil

/-!
# Necessary structural restrictions for Erdős problem 647

This helper is independent of `Submission.Spec`.  Here `P n` denotes the
pointwise divisor-count condition, not a conjectured theorem.  All computations
in this file are ordinary kernel-checked proofs.

The principal entry points are `base_dvd_of_P`, `necessary_base`, and
`base_dvd_of_iSup_le`: a solution above 24 must be a multiple of 360360.
The file also provides complete low-count classifications, the entire
2,3,5-smooth decomposition, and `prime_cofactor_of_P`, the thirteen-offset
prime-cofactor table. The base proof uses finite bounded-exponent cases for
11 and 13 and includes square cofactors; the table subsequently eliminates
every square by explicit quadratic-residue checks. These are necessary
restrictions only, not a proof of global nonexistence.
-/

namespace Structural

open scoped ArithmeticFunction.sigma

/-- The pointwise condition in Erdős problem 647. -/
def P (n : ℕ) : Prop := ∀ m : ℕ, m < n → m + σ 0 m ≤ n + 2

/-- The condition at a positive offset. -/
theorem offset_bound {n k : ℕ} (h : P n) (hk : 0 < k) (hkn : k ≤ n) :
    σ 0 (n - k) ≤ k + 2 := by
  have := h (n - k) (by omega)
  omega

/-- Divisor count is monotone along divisibility (away from zero). -/
theorem sigma_zero_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    σ 0 a ≤ σ 0 b := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using
    Finset.card_le_card (Nat.divisors_subset_of_dvd hb hab)

/-- Every natural number greater than one has at least two divisors. -/
theorem two_le_sigma_zero {n : ℕ} (hn : 1 < n) : 2 ≤ σ 0 n := by
  have hpos := ArithmeticFunction.sigma_pos 0 n (by omega)
  have hne : σ 0 n ≠ 1 := by
    intro ht
    have := (ArithmeticFunction.sigma_eq_one_iff 0 n).mp ht
    omega
  omega

/-- The complete classification for at most three divisors. -/
theorem sigma_zero_le_three {n : ℕ} (hn : n ≠ 0) (hτ : σ 0 n ≤ 3) :
    n = 1 ∨ n.Prime ∨ ∃ p : ℕ, p.Prime ∧ n = p ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => contradiction
  | one => exact Or.inl rfl
  | prime_pow p e hp he =>
      rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp] at hτ
      have he' : e = 1 ∨ e = 2 := by omega
      rcases he' with rfl | rfl
      · exact Or.inr (Or.inl (by simpa using hp))
      · exact Or.inr (Or.inr ⟨p, hp, rfl⟩)
  | coprime a b ha hb hab iha ihb =>
      have hmul : σ 0 (a * b) = σ 0 a * σ 0 b :=
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab
      have hτa := two_le_sigma_zero ha
      have hτb := two_le_sigma_zero hb
      rw [hmul] at hτ
      nlinarith

/-- The complete classification for at most two divisors. -/
theorem sigma_zero_le_two {n : ℕ} (hn : n ≠ 0) (hτ : σ 0 n ≤ 2) :
    n = 1 ∨ n.Prime := by
  rcases sigma_zero_le_three hn (by omega) with h1 | hp | ⟨p, hp, rfl⟩
  · exact Or.inl h1
  · exact Or.inr hp
  · have := ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hp
    omega

/-- Split off the entire power of a given prime, including the divisor-count identity. -/
theorem prime_power_split {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ∃ e r : ℕ, 0 < r ∧ ¬ p ∣ r ∧ n = p ^ e * r ∧
      σ 0 n = (e + 1) * σ 0 r := by
  refine ⟨n.factorization p, ordCompl[p] n, Nat.ordCompl_pos p hn,
    Nat.not_dvd_ordCompl hp hn, (Nat.ordProj_mul_ordCompl_eq_self n p).symm, ?_⟩
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.coprime_ordCompl hp hn).pow_left _)]
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]

/-- A prime divisor with multiplicity at least `v` and a small divisor-count bound
leaves only a unit or a prime residual. -/
theorem prime_power_low_count {p n v B : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hv : p ^ v ∣ n) (hB : B < 3 * (v + 1)) (hτ : σ 0 n ≤ B) :
    (∃ e : ℕ, v ≤ e ∧ e + 1 ≤ B ∧ n = p ^ e) ∨
    (∃ e q : ℕ, v ≤ e ∧ 2 * (e + 1) ≤ B ∧ q.Prime ∧ q ≠ p ∧
      n = p ^ e * q) := by
  obtain ⟨e, r, hr, hpr, hn', hτ'⟩ := prime_power_split hp hn
  have he : v ≤ e := by
    have hdiv : p ^ v ∣ p ^ e * r := hn' ▸ hv
    have hcp : (p ^ v).Coprime r := (hp.coprime_iff_not_dvd.mpr hpr).pow_left v
    have hpdiv := hcp.dvd_of_dvd_mul_right hdiv
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpdiv
  have hτr : σ 0 r ≤ 2 := by
    have hpos := ArithmeticFunction.sigma_pos 0 r (by omega)
    rw [hτ'] at hτ
    nlinarith
  rcases sigma_zero_le_two (by omega) hτr with rfl | hq
  · left
    refine ⟨e, he, ?_, by simpa using hn'⟩
    simpa only [ArithmeticFunction.sigma_one, mul_one] using hτ'.symm.trans_le hτ
  · right
    have hqτ : σ 0 r = 2 := by
      simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hq
    refine ⟨e, r, he, ?_, hq, ?_, hn'⟩
    · rw [hτ', hqτ] at hτ
      omega
    · rintro rfl
      exact hpr (dvd_refl _)

/-- Complete even-number classification with at most four divisors. -/
theorem even_sigma_zero_le_four {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n)
    (hτ : σ 0 n ≤ 4) :
    n = 2 ∨ n = 4 ∨ n = 8 ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n = 2 * p := by
  rcases prime_power_low_count (p := 2) (v := 1) (B := 4) Nat.prime_two hn
      (by simpa using h2) (by decide) hτ with ⟨e, he, heB, hn'⟩ |
      ⟨e, q, he, heB, hq, hq2, hn'⟩
  · have : e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all
  · have : e = 1 := by omega
    subst e
    exact Or.inr (Or.inr (Or.inr ⟨q, hq, hq2, by simpa using hn'⟩))

/-- Complete classification of multiples of four with at most six divisors. -/
theorem four_dvd_sigma_zero_le_six {n : ℕ} (hn : n ≠ 0) (h4 : 4 ∣ n)
    (hτ : σ 0 n ≤ 6) :
    (∃ e : ℕ, 2 ≤ e ∧ e ≤ 5 ∧ n = 2 ^ e) ∨
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ n = 4 * q := by
  rcases prime_power_low_count (p := 2) (v := 2) (B := 6) Nat.prime_two hn
      (by simpa using h4) (by decide) hτ with ⟨e, he, heB, hn'⟩ |
      ⟨e, q, he, heB, hq, hq2, hn'⟩
  · exact Or.inl ⟨e, he, by omega, hn'⟩
  · have : e = 2 := by omega
    subst e
    exact Or.inr ⟨q, hq, hq2, by simpa using hn'⟩

/-- An even positive number with at most three divisors is 2 or 4. -/
theorem even_sigma_zero_le_three {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n)
    (hτ : σ 0 n ≤ 3) : n = 2 ∨ n = 4 := by
  rcases sigma_zero_le_three hn hτ with rfl | hp | ⟨p, hp, hn'⟩
  · norm_num at h2
  · have := hp.eq_one_or_self_of_dvd 2 h2
    omega
  · have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (hn' ▸ h2)
    have := hp.eq_one_or_self_of_dvd 2 h2p
    have hp2 : p = 2 := by omega
    simp_all

/-- No natural square is 3 modulo 4. -/
theorem square_not_three_mod_four (a : ℕ) : a ^ 2 % 4 ≠ 3 := by
  have ha : a % 4 < 4 := Nat.mod_lt _ (by decide)
  have : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

/-- A prime larger than `d > 1` is not divisible by `d`. -/
theorem prime_not_dvd_of_lt {q d : ℕ} (hq : q.Prime) (hd : 1 < d)
    (hdq : d < q) : ¬ d ∣ q := by
  intro h
  have := hq.eq_one_or_self_of_dvd d h
  omega

/-- Every solution above 24 is even. -/
theorem two_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 2 ∣ n := by
  have hτ := offset_bound h (k := 1) (by decide) (by omega)
  by_contra hn2
  have hmod : n % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hn2
  have h2 : 2 ∣ n - 1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have := even_sigma_zero_le_three (n := n - 1) (by omega) h2 (by omega)
  omega

/-- The parity formulation of `two_dvd_of_P`. -/
theorem even_of_P {n : ℕ} (h : P n) (hn : 24 < n) : Even n :=
  even_iff_two_dvd.mpr (two_dvd_of_P h hn)

/-- The offset-two prime form. -/
theorem sub_two_prime_form {n : ℕ} (h : P n) (hn : 24 < n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n = 2 * p + 2 := by
  have hn2 := Nat.mod_eq_zero_of_dvd (two_dvd_of_P h hn)
  have h2 : 2 ∣ n - 2 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hτ := offset_bound h (k := 2) (by decide) (by omega)
  rcases even_sigma_zero_le_four (n := n - 2) (by omega) h2 (by omega) with
    h2 | h4 | h8 | ⟨p, hp, hp2, heq⟩
  · omega
  · omega
  · omega
  · exact ⟨p, hp, hp2, by omega⟩

/-- Every solution above 24 is divisible by four. -/
theorem four_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 4 ∣ n := by
  obtain ⟨p, hp, hp2, hn'⟩ := sub_two_prime_form h hn
  have hpodd := hp.eq_two_or_odd.resolve_left hp2
  apply Nat.dvd_iff_mod_eq_zero.mpr
  omega

/-- The offset-one value is prime, not a prime square. -/
theorem prime_sub_one_of_P {n : ℕ} (h : P n) (hn : 24 < n) : (n - 1).Prime := by
  have h4 := Nat.mod_eq_zero_of_dvd (four_dvd_of_P h hn)
  have hτ := offset_bound h (k := 1) (by decide) (by omega)
  rcases sigma_zero_le_three (n := n - 1) (by omega) (by omega) with
    h1 | hp | ⟨p, hp, heq⟩
  · omega
  · exact hp
  · have := square_not_three_mod_four p
    rw [← heq] at this
    omega

/-- The offset-four prime form; all pure powers are explicitly excluded. -/
theorem sub_four_prime_form {n : ℕ} (h : P n) (hn : 24 < n) :
    ∃ q : ℕ, q.Prime ∧ 5 < q ∧ n = 4 * q + 4 := by
  have h4 := Nat.mod_eq_zero_of_dvd (four_dvd_of_P h hn)
  have h4' : 4 ∣ n - 4 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hτ := offset_bound h (k := 4) (by decide) (by omega)
  rcases four_dvd_sigma_zero_le_six (n := n - 4) (by omega) h4' (by omega) with
    ⟨e, he, he5, hn'⟩ | ⟨q, hq, hq2, hn'⟩
  · have hp := prime_sub_one_of_P h hn
    interval_cases e <;> norm_num at hn' <;> try omega
    have hn36 : n = 36 := by omega
    subst n
    norm_num at hp
  · exact ⟨q, hq, by omega, by omega⟩

/-- Every solution above 24 is divisible by 24. -/
theorem twentyfour_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 24 ∣ n := by
  obtain ⟨p, hp, hp2, hnp⟩ := sub_two_prime_form h hn
  obtain ⟨q, hq, hq5, hnq⟩ := sub_four_prime_form h hn
  have hpq : p = 2 * q + 1 := by omega
  have h3q := prime_not_dvd_of_lt hq (d := 3) (by decide) (by omega)
  have h3p := prime_not_dvd_of_lt hp (d := 3) (by decide) (by omega)
  have hqodd := hq.eq_two_or_odd.resolve_left (by omega : q ≠ 2)
  have hqmod : q % 3 = 2 := by
    have hq0 : q % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using h3q
    have hp0 : p % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using h3p
    have hq1 : q % 3 ≠ 1 := by
      intro hq1
      simp [hpq, Nat.add_mod, Nat.mul_mod, hq1] at hp0
    omega
  have h3 : 3 ∣ n := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    simp [hnq, Nat.add_mod, Nat.mul_mod, hqmod]
  have h8 : 8 ∣ n := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  simpa using (show Nat.Coprime 3 8 by decide).mul_dvd_of_dvd_of_dvd h3 h8

/-- Read a lower bound on the exponent in a prime-power decomposition. -/
theorem prime_power_exponent_ge {p n e r v : ℕ} (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hn : n = p ^ e * r) (hv : p ^ v ∣ n) : v ≤ e := by
  have hdiv : p ^ v ∣ p ^ e * r := hn ▸ hv
  have hcp : (p ^ v).Coprime r := (hp.coprime_iff_not_dvd.mpr hpr).pow_left v
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hcp.dvd_of_dvd_mul_right hdiv)

/-- Read an upper bound on the exponent from a missing prime-power divisor. -/
theorem prime_power_exponent_lt {p n e r v : ℕ} (hn : n = p ^ e * r)
    (hv : ¬ p ^ v ∣ n) : e < v := by
  by_contra he
  have hpow : p ^ v ∣ p ^ e := Nat.pow_dvd_pow p (by omega)
  exact hv (hn ▸ hpow.trans (dvd_mul_right _ _))

/-- The offset-three prime form on the 24 lattice. -/
theorem sub_three_prime_form {n : ℕ} (h : P n) (hn : 24 < n) :
    ∃ s : ℕ, s.Prime ∧ 7 < s ∧ n = 3 * s + 3 := by
  have h24 := Nat.mod_eq_zero_of_dvd (twentyfour_dvd_of_P h hn)
  have h3 : 3 ∣ n - 3 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hτ := offset_bound h (k := 3) (by decide) (by omega)
  rcases prime_power_low_count (p := 3) (v := 1) (B := 5) Nat.prime_three
      (n := n - 3) (by omega) (by simpa using h3) (by decide) (by omega) with
      ⟨e, he, heB, hn'⟩ | ⟨e, s, he, heB, hs, hs3, hn'⟩
  · have he4 : e ≤ 4 := by omega
    interval_cases e <;> norm_num at hn' <;> omega
  · have he1 : e = 1 := by omega
    subst e
    norm_num at hn'
    exact ⟨s, hs, by omega, by omega⟩

/-- The offset-six prime form on the 24 lattice. -/
theorem sub_six_prime_form {n : ℕ} (h : P n) (hn : 24 < n) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ n = 6 * r + 6 := by
  have h24 := Nat.mod_eq_zero_of_dvd (twentyfour_dvd_of_P h hn)
  have h2 : 2 ^ 1 ∣ n - 6 := Nat.dvd_iff_mod_eq_zero.mpr (by norm_num; omega)
  have h4 : ¬ 2 ^ 2 ∣ n - 6 := by
    norm_num
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  have h3 : 3 ∣ n - 6 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hτ := offset_bound h (k := 6) (by decide) (by omega)
  obtain ⟨e, u, hu, h2u, hnu, hτu⟩ := prime_power_split Nat.prime_two (n := n - 6) (by omega)
  have hege := prime_power_exponent_ge Nat.prime_two h2u hnu h2
  have helt := prime_power_exponent_lt hnu h4
  have he1 : e = 1 := by omega
  subst e
  norm_num at hnu hτu
  have hτu4 : σ 0 u ≤ 4 := by omega
  have h3u : 3 ∣ u := by
    rw [hnu] at h3
    exact (Nat.prime_three.dvd_mul.mp h3).resolve_left (by decide)
  rcases prime_power_low_count (p := 3) (v := 1) (B := 4) Nat.prime_three
      (n := u) (by omega) (by simpa using h3u) (by decide) hτu4 with
      ⟨f, hf, hfB, huf⟩ | ⟨f, r, hf, hfB, hr, hr3, huf⟩
  · have hf3 : f ≤ 3 := by omega
    interval_cases f <;> norm_num at huf <;> omega
  · have hf1 : f = 1 := by omega
    subst f
    norm_num at huf
    refine ⟨r, hr, ?_, ?_⟩ <;> omega

/-- A prime form larger than the modulus cannot take residue one before subtracting one. -/
theorem prime_form_not_mod_one {p q c t : ℕ} (hq : q.Prime) (hp : 1 < p)
    (hpq : p < q) (hform : c * t = q + 1) : c * t % p ≠ 1 := by
  intro hm
  have heq : q + 1 ≡ 0 + 1 [MOD p] := by
    change (q + 1) % p = (0 + 1) % p
    rw [← hform]
    simpa [Nat.mod_eq_of_lt hp] using hm
  have hq0 : q ≡ 0 [MOD p] := Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) heq
  have hd : p ∣ q := Nat.dvd_iff_mod_eq_zero.mpr (by simpa [Nat.ModEq] using hq0)
  exact prime_not_dvd_of_lt hq hp hpq hd

/-- Every solution above 24 is divisible by 360. -/
theorem three_sixty_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 360 ∣ n := by
  obtain ⟨t, hnt⟩ := twentyfour_dvd_of_P h hn
  obtain ⟨p, hp, hp2, hnp⟩ := sub_two_prime_form h hn
  obtain ⟨q, hq, hq5, hnq⟩ := sub_four_prime_form h hn
  obtain ⟨s, hs, hs7, hns⟩ := sub_three_prime_form h hn
  obtain ⟨r, hr, hr3, hnr⟩ := sub_six_prime_form h hn
  have ht : 2 ≤ t := by omega
  have hp5 : 5 < p := by omega
  have hr5 : 5 < r := by omega
  have hfp : 12 * t = p + 1 := by omega
  have hfq : 6 * t = q + 1 := by omega
  have hfs : 8 * t = s + 1 := by omega
  have hfr : 4 * t = r + 1 := by omega
  have h3r := prime_form_not_mod_one hr (p := 3) (by decide) (by omega) hfr
  have h3s := prime_form_not_mod_one hs (p := 3) (by decide) (by omega) hfs
  have ht3 : t % 3 = 0 := by
    have hb : t % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hm : t % 3 <;> norm_num [Nat.mul_mod, hm] at *
  have h5p := prime_form_not_mod_one hp (p := 5) (by decide) hp5 hfp
  have h5q := prime_form_not_mod_one hq (p := 5) (by decide) hq5 hfq
  have h5s := prime_form_not_mod_one hs (p := 5) (by decide) (by omega) hfs
  have h5r := prime_form_not_mod_one hr (p := 5) (by decide) hr5 hfr
  have ht5 : t % 5 = 0 := by
    have hb : t % 5 < 5 := Nat.mod_lt _ (by decide)
    interval_cases hm : t % 5 <;> norm_num [Nat.mul_mod, hm] at *
  have ht15 : 15 ∣ t := (show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd
    (Nat.dvd_iff_mod_eq_zero.mpr ht3) (Nat.dvd_iff_mod_eq_zero.mpr ht5)
  have := Nat.mul_dvd_mul_left 24 ht15
  simpa [← hnt] using this

/-- The offset-twelve prime form on the 360 lattice. -/
theorem sub_twelve_prime_form {n : ℕ} (h : P n) (hn : 24 < n) :
    ∃ u : ℕ, u.Prime ∧ 28 < u ∧ n = 12 * u + 12 := by
  obtain ⟨b, hnb⟩ := three_sixty_dvd_of_P h hn
  have hb : 1 ≤ b := by omega
  let u := 30 * b - 1
  have hu : 29 ≤ u := by dsimp [u]; omega
  have hnu : n - 12 = 12 * u := by dsimp [u]; omega
  have h2u : ¬ 2 ∣ u := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    dsimp [u]
    omega
  have h3u : ¬ 3 ∣ u := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    dsimp [u]
    omega
  have hcp : Nat.Coprime 12 u := by
    have h4u := (Nat.prime_two.coprime_iff_not_dvd.mpr h2u).pow_left 2
    have := h4u.mul_left (Nat.prime_three.coprime_iff_not_dvd.mpr h3u)
    simpa using this
  have hτ12 : σ 0 12 = 6 := by
    have hcp43 : Nat.Coprime 4 3 := by decide
    have hτ4 := ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) Nat.prime_two
    have hτ3 := ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) Nat.prime_three
    have hm : σ 0 (4 * 3) = σ 0 4 * σ 0 3 :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcp43
    norm_num at hτ4 hτ3 hm
    rw [hm, hτ4, hτ3]
  have hτ := offset_bound h (k := 12) (by decide) (by omega)
  rw [hnu, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcp, hτ12] at hτ
  have hτu : σ 0 u ≤ 2 := by omega
  rcases sigma_zero_le_two (by omega : u ≠ 0) hτu with hu1 | hup
  · omega
  · exact ⟨u, hup, by omega, by omega⟩

/-- Every solution above 24 is divisible by 2520. -/
theorem two_five_twenty_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 2520 ∣ n := by
  obtain ⟨b, hnb⟩ := three_sixty_dvd_of_P h hn
  have hb : 1 ≤ b := by omega
  have hp1 := prime_sub_one_of_P h hn
  obtain ⟨p, hp, hp2, hnp⟩ := sub_two_prime_form h hn
  obtain ⟨q, hq, hq5, hnq⟩ := sub_four_prime_form h hn
  obtain ⟨s, hs, hs7, hns⟩ := sub_three_prime_form h hn
  obtain ⟨r, hr, hr3, hnr⟩ := sub_six_prime_form h hn
  obtain ⟨u, hu, hu28, hnu⟩ := sub_twelve_prime_form h hn
  have hf1 : 360 * b = (n - 1) + 1 := by omega
  have hfp : 180 * b = p + 1 := by omega
  have hfq : 90 * b = q + 1 := by omega
  have hfs : 120 * b = s + 1 := by omega
  have hfr : 60 * b = r + 1 := by omega
  have hfu : 30 * b = u + 1 := by omega
  have h71 := prime_form_not_mod_one hp1 (p := 7) (by decide) (by omega) hf1
  have h7p := prime_form_not_mod_one hp (p := 7) (by decide) (by omega) hfp
  have h7q := prime_form_not_mod_one hq (p := 7) (by decide) (by omega) hfq
  have h7s := prime_form_not_mod_one hs (p := 7) (by decide) (by omega) hfs
  have h7r := prime_form_not_mod_one hr (p := 7) (by decide) (by omega) hfr
  have h7u := prime_form_not_mod_one hu (p := 7) (by decide) (by omega) hfu
  have hb7 : b % 7 = 0 := by
    have hb7lt : b % 7 < 7 := Nat.mod_lt _ (by decide)
    interval_cases hm : b % 7 <;> norm_num [Nat.mul_mod, hm] at *
  have hd := Nat.mul_dvd_mul_left 360 (Nat.dvd_iff_mod_eq_zero.mpr hb7)
  simpa [← hnb] using hd

/-- The exponent in a coprime prime-power split is the factorization exponent. -/
theorem prime_power_exponent_eq_factorization {p n e r : ℕ} (hp : p.Prime)
    (hr : r ≠ 0) (hpr : ¬ p ∣ r) (hn : n = p ^ e * r) : e = n.factorization p := by
  rw [hn, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hr]
  simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hpr]

/-- Strip the entire 2,3,5-smooth part, without losing small-prime coincidences. -/
theorem smooth_split {n : ℕ} (hn : n ≠ 0) :
    ∃ a b c r : ℕ,
      a = n.factorization 2 ∧ b = n.factorization 3 ∧ c = n.factorization 5 ∧
      0 < r ∧ ¬ 2 ∣ r ∧ ¬ 3 ∣ r ∧ ¬ 5 ∣ r ∧
      n = 2 ^ a * 3 ^ b * 5 ^ c * r ∧
      σ 0 n = (a + 1) * (b + 1) * (c + 1) * σ 0 r := by
  obtain ⟨a, u, hu, h2u, hnu, hτnu⟩ := prime_power_split Nat.prime_two hn
  obtain ⟨b, v, hv, h3v, huv, hτuv⟩ := prime_power_split Nat.prime_three (by omega : u ≠ 0)
  obtain ⟨c, r, hr, h5r, hvr, hτvr⟩ := prime_power_split (by decide : Nat.Prime 5) (by omega : v ≠ 0)
  have hvu : v ∣ u := huv ▸ dvd_mul_left v (3 ^ b)
  have hrv : r ∣ v := hvr ▸ dvd_mul_left r (5 ^ c)
  have h2r : ¬ 2 ∣ r := fun hd => h2u (hd.trans (hrv.trans hvu))
  have h3r : ¬ 3 ∣ r := fun hd => h3v (hd.trans hrv)
  have ha := prime_power_exponent_eq_factorization Nat.prime_two (by omega) h2u hnu
  have hb := prime_power_exponent_eq_factorization Nat.prime_three (by omega) h3v huv
  have hc := prime_power_exponent_eq_factorization (by decide : Nat.Prime 5) (by omega) h5r hvr
  have hfn3 : n.factorization 3 = u.factorization 3 := by
    rw [hnu, Nat.factorization_mul (pow_ne_zero _ (by decide : 2 ≠ 0)) (by omega : u ≠ 0)]
    simp [Nat.prime_two.factorization_pow]
  have hfn5 : n.factorization 5 = v.factorization 5 := by
    rw [hnu, Nat.factorization_mul (pow_ne_zero _ (by decide : 2 ≠ 0)) (by omega : u ≠ 0),
      huv, Nat.factorization_mul (pow_ne_zero _ (by decide : 3 ≠ 0)) (by omega : v ≠ 0)]
    simp [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
  refine ⟨a, b, c, r, ha, hb.trans hfn3.symm, hc.trans hfn5.symm,
    hr, h2r, h3r, h5r, ?_, ?_⟩
  · rw [hnu, huv, hvr]
    ring
  · rw [hτnu, hτuv, hτvr]
    ring

/-- A fixed valuation is preserved when subtracting a lower-valuation offset. -/
theorem factorization_sub_eq {p n k v : ℕ} (hp : p.Prime) (hkn : k < n)
    (hnp : p ^ (v + 1) ∣ n) (hkp : p ^ v ∣ k) (hkp' : ¬ p ^ (v + 1) ∣ k) :
    (n - k).factorization p = v := by
  have hn0 : n - k ≠ 0 := by omega
  have hd : p ^ v ∣ n - k := Nat.dvd_sub
    ((Nat.pow_dvd_pow p (Nat.le_succ v)).trans hnp) hkp
  have hnd : ¬ p ^ (v + 1) ∣ n - k := by
    intro hd'
    have h := Nat.dvd_sub hnp hd'
    rw [Nat.sub_sub_self hkn.le] at h
    exact hkp' h
  have hge := (hp.pow_dvd_iff_le_factorization hn0).mp hd
  have hlt : (n - k).factorization p < v + 1 := by
    by_contra he
    exact hnd ((hp.pow_dvd_iff_le_factorization hn0).mpr (by omega))
  omega

/-- Specialization to an arbitrary lattice. -/
theorem offset_factorization_fixed {p n k v L : ℕ} (hp : p.Prime) (hkn : k < n)
    (hL : L ∣ n) (hLp : p ^ (v + 1) ∣ L) (hkp : p ^ v ∣ k)
    (hkp' : ¬ p ^ (v + 1) ∣ k) : (n - k).factorization p = v :=
  factorization_sub_eq hp hkn (hLp.trans hL) hkp hkp'

/-- The matching lower-valuation bound when the offset and lattice valuations coincide. -/
theorem offset_factorization_lower {p n k v L : ℕ} (hp : p.Prime) (hkn : k < n)
    (hL : L ∣ n) (hLp : p ^ v ∣ L) (hkp : p ^ v ∣ k) :
    v ≤ (n - k).factorization p :=
  (hp.pow_dvd_iff_le_factorization (by omega : n - k ≠ 0)).mp
    (Nat.dvd_sub (hLp.trans hL) hkp)

/-- A small count forces the residual to be a unit once the smooth part and
one additional prime already consume more than half of the divisor budget. -/
theorem residual_eq_one_of_count {A e r B M : ℕ} (hr : 0 < r) (he : 1 ≤ e)
    (hA : M ≤ A) (hB : B < 4 * M) (hcount : A * (e + 1) * σ 0 r ≤ B) : r = 1 := by
  have hpos := ArithmeticFunction.sigma_pos 0 r (by omega)
  have hle : σ 0 r ≤ 1 := by
    by_contra hc
    have hcoef := Nat.mul_le_mul hA (show 2 ≤ e + 1 by omega)
    have hbig := Nat.mul_le_mul hcoef (show 2 ≤ σ 0 r by omega)
    nlinarith
  exact (ArithmeticFunction.sigma_eq_one_iff 0 r).mp (by omega)

/-- Explicit bounds on both exponents from a two-factor divisor budget. -/
theorem product_exponent_caps {D f e B v : ℕ} (hf : v ≤ f) (he : 1 ≤ e)
    (hcount : D * (f + 1) * (e + 1) ≤ B) :
    2 * D * (f + 1) ≤ B ∧ D * (v + 1) * (e + 1) ≤ B := by
  constructor
  · have hh := Nat.mul_le_mul_left (D * (f + 1)) (show 2 ≤ e + 1 by omega)
    nlinarith
  · exact (Nat.mul_le_mul_right (e + 1)
      (Nat.mul_le_mul_left D (show v + 1 ≤ f + 1 by omega))).trans hcount

/-- The thirteen offsets used to force 11 and 13. -/
def offsets : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 20, 24}

set_option maxHeartbeats 4000000 in
/-- No offset in the thirteen-element set can be divisible by 11 or 13.

For this implication alone it is unnecessary to first rule out prime-square
cofactors by quadratic residues: stripping the additional prime leaves a unit,
and the bounded exponent cases are all incompatible with the 2520 lattice.
The finite cases therefore include the square cofactors, rather than assuming
that they have been eliminated.
-/
theorem eleven_thirteen_not_dvd_offset {n k p : ℕ} (h : P n) (hn : 24 < n)
    (hL : 2520 ∣ n) (hk : k ∈ offsets) (hpchoice : p = 11 ∨ p = 13) : ¬ p ∣ n - k := by
  have hk' := hk
  simp only [offsets, Finset.mem_insert, Finset.mem_singleton] at hk'
  have hk0 : 0 < k := by omega
  have hk24 : k ≤ 24 := by omega
  have hkn : k < n := by omega
  have hp : p.Prime := by rcases hpchoice with rfl | rfl <;> norm_num
  have hp5 : 5 < p := by omega
  intro hpx
  obtain ⟨a, b, c, r, hfa, hfb, hfc, hr, h2r, h3r, h5r, hxr, hτxr⟩ :=
    smooth_split (n := n - k) (by omega)
  have hcp2 : p.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr
    (prime_not_dvd_of_lt hp (by decide : 1 < 2) (by omega))).symm
  have hcp3 : p.Coprime 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr
    (prime_not_dvd_of_lt hp (by decide : 1 < 3) (by omega))).symm
  have hcp5 : p.Coprime 5 := ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr
    (prime_not_dvd_of_lt hp (by decide : 1 < 5) hp5)).symm
  have hcp : p.Coprime (2 ^ a * 3 ^ b * 5 ^ c) :=
    ((hcp2.pow_right a).mul_right (hcp3.pow_right b)).mul_right (hcp5.pow_right c)
  have hpr : p ∣ r := hcp.dvd_of_dvd_mul_left (hxr ▸ hpx)
  obtain ⟨e, s, hs, hps, hrs, hτrs⟩ := prime_power_split hp (by omega : r ≠ 0)
  have he : 1 ≤ e := prime_power_exponent_ge hp hps hrs (by simpa using hpr)
  have hfull : n - k = 2 ^ a * 3 ^ b * 5 ^ c * p ^ e * s := by
    rw [hxr, hrs]
    ring
  have hcount : (a + 1) * (b + 1) * (c + 1) * (e + 1) * σ 0 s ≤ k + 2 := by
    have ht := offset_bound h hk0 hkn.le
    rw [hτxr, hτrs] at ht
    simpa only [Nat.mul_assoc] using ht
  have hmod := Nat.mod_eq_zero_of_dvd hL
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- Offset 1: the complete smooth-part valuation pattern.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 1 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 1) (B := 3) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb, hc] at hcount hfull
    have hemax : e ≤ 2 := by omega
    interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 2: the complete smooth-part valuation pattern.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 2 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 2) (B := 4) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb, hc] at hcount hfull
    have hemax : e ≤ 1 := by omega
    interval_cases e
    rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 3: the complete smooth-part valuation pattern.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 2 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 2) (B := 5) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb, hc] at hcount hfull
    have hemax : e ≤ 1 := by omega
    interval_cases e
    rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 4: the complete smooth-part valuation pattern.
    have ha : a = 2 := hfa.trans
      (offset_factorization_fixed (v := 2) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 3 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 3) (B := 6) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb, hc] at hcount hfull
    have hemax : e ≤ 1 := by omega
    interval_cases e
    rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 5: the complete smooth-part valuation pattern.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : 1 ≤ c := by
      rw [hfc]
      exact offset_factorization_lower (v := 1) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num)
    have hA : 2 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb]
      omega
    have hs1 := residual_eq_one_of_count (M := 2) (B := 7) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb] at hcount hfull
    have hcnt : 1 * (c + 1) * (e + 1) ≤ 7 := by nlinarith
    obtain ⟨hcap1, hcap2⟩ := product_exponent_caps hc he hcnt
    have hcmax : c ≤ 2 := by omega
    have hemax : e ≤ 2 := by omega
    interval_cases c <;> interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 6: the complete smooth-part valuation pattern.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 4 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 4) (B := 8) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb, hc] at hcount hfull
    have hemax : e ≤ 1 := by omega
    interval_cases e
    rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 8: the complete smooth-part valuation pattern.
    have ha : 3 ≤ a := by
      rw [hfa]
      exact offset_factorization_lower (v := 3) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num)
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 4 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 4) (B := 10) hs he hA
      (by decide) hcount
    subst s
    norm_num [hb, hc] at hcount hfull
    have hcnt : 1 * (a + 1) * (e + 1) ≤ 10 := by nlinarith
    obtain ⟨hcap1, hcap2⟩ := product_exponent_caps ha he hcnt
    have hamax : a ≤ 4 := by omega
    have hemax : e ≤ 1 := by omega
    interval_cases a <;> interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 9: the complete smooth-part valuation pattern.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : 2 ≤ b := by
      rw [hfb]
      exact offset_factorization_lower (v := 2) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num)
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 3 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 3) (B := 11) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hc] at hcount hfull
    have hcnt : 1 * (b + 1) * (e + 1) ≤ 11 := by nlinarith
    obtain ⟨hcap1, hcap2⟩ := product_exponent_caps hb he hcnt
    have hbmax : b ≤ 4 := by omega
    have hemax : e ≤ 2 := by omega
    interval_cases b <;> interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 10: the complete smooth-part valuation pattern.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : 1 ≤ c := by
      rw [hfc]
      exact offset_factorization_lower (v := 1) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num)
    have hA : 4 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb]
      omega
    have hs1 := residual_eq_one_of_count (M := 4) (B := 12) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb] at hcount hfull
    have hcnt : 2 * (c + 1) * (e + 1) ≤ 12 := by nlinarith
    obtain ⟨hcap1, hcap2⟩ := product_exponent_caps hc he hcnt
    have hcmax : c ≤ 2 := by omega
    have hemax : e ≤ 2 := by omega
    interval_cases c <;> interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 12: the complete smooth-part valuation pattern.
    have ha : a = 2 := hfa.trans
      (offset_factorization_fixed (v := 2) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 6 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 6) (B := 14) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb, hc] at hcount hfull
    have hemax : e ≤ 1 := by omega
    interval_cases e
    rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 18: the complete smooth-part valuation pattern.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : 2 ≤ b := by
      rw [hfb]
      exact offset_factorization_lower (v := 2) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num)
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 6 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 6) (B := 20) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hc] at hcount hfull
    have hcnt : 2 * (b + 1) * (e + 1) ≤ 20 := by nlinarith
    obtain ⟨hcap1, hcap2⟩ := product_exponent_caps hb he hcnt
    have hbmax : b ≤ 4 := by omega
    have hemax : e ≤ 2 := by omega
    interval_cases b <;> interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 20: the complete smooth-part valuation pattern.
    have ha : a = 2 := hfa.trans
      (offset_factorization_fixed (v := 2) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : 1 ≤ c := by
      rw [hfc]
      exact offset_factorization_lower (v := 1) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num)
    have hA : 6 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb]
      omega
    have hs1 := residual_eq_one_of_count (M := 6) (B := 22) hs he hA
      (by decide) hcount
    subst s
    norm_num [ha, hb] at hcount hfull
    have hcnt : 3 * (c + 1) * (e + 1) ≤ 22 := by nlinarith
    obtain ⟨hcap1, hcap2⟩ := product_exponent_caps hc he hcnt
    have hcmax : c ≤ 2 := by omega
    have hemax : e ≤ 2 := by omega
    interval_cases c <;> interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega
  · -- Offset 24: the complete smooth-part valuation pattern.
    have ha : 3 ≤ a := by
      rw [hfa]
      exact offset_factorization_lower (v := 3) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num)
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 8 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [hb, hc]
      omega
    have hs1 := residual_eq_one_of_count (M := 8) (B := 26) hs he hA
      (by decide) hcount
    subst s
    norm_num [hb, hc] at hcount hfull
    have hcnt : 2 * (a + 1) * (e + 1) ≤ 26 := by nlinarith
    obtain ⟨hcap1, hcap2⟩ := product_exponent_caps ha he hcnt
    have hamax : a ≤ 5 := by omega
    have hemax : e ≤ 2 := by omega
    interval_cases a <;> interval_cases e <;> rcases hpchoice with rfl | rfl <;>
      norm_num at hfull hcount <;> omega

/-- Each nonzero residue modulo 11 is represented by one of the thirteen offsets. -/
theorem offsets_cover_eleven {n : ℕ} (hn : n % 11 ≠ 0) :
    ∃ k ∈ offsets, n % 11 = k % 11 := by
  have hb : n % 11 < 11 := Nat.mod_lt _ (by decide)
  interval_cases hm : n % 11
  · exact False.elim (hn rfl)
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨4, by decide, by norm_num⟩
  · exact ⟨5, by decide, by norm_num⟩
  · exact ⟨6, by decide, by norm_num⟩
  · exact ⟨18, by decide, by norm_num⟩
  · exact ⟨8, by decide, by norm_num⟩
  · exact ⟨9, by decide, by norm_num⟩
  · exact ⟨10, by decide, by norm_num⟩

/-- Each nonzero residue modulo 13 is represented by one of the thirteen offsets. -/
theorem offsets_cover_thirteen {n : ℕ} (hn : n % 13 ≠ 0) :
    ∃ k ∈ offsets, n % 13 = k % 13 := by
  have hb : n % 13 < 13 := Nat.mod_lt _ (by decide)
  interval_cases hm : n % 13
  · exact False.elim (hn rfl)
  · exact ⟨1, by decide, by norm_num⟩
  · exact ⟨2, by decide, by norm_num⟩
  · exact ⟨3, by decide, by norm_num⟩
  · exact ⟨4, by decide, by norm_num⟩
  · exact ⟨5, by decide, by norm_num⟩
  · exact ⟨6, by decide, by norm_num⟩
  · exact ⟨20, by decide, by norm_num⟩
  · exact ⟨8, by decide, by norm_num⟩
  · exact ⟨9, by decide, by norm_num⟩
  · exact ⟨10, by decide, by norm_num⟩
  · exact ⟨24, by decide, by norm_num⟩
  · exact ⟨12, by decide, by norm_num⟩

/-- Every solution above 24 is divisible by 11. -/
theorem eleven_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 11 ∣ n := by
  have hL := two_five_twenty_dvd_of_P h hn
  by_contra hd
  have hm : n % 11 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hd
  obtain ⟨k, hk, hnk⟩ := offsets_cover_eleven hm
  have hk24 : k ≤ 24 := by
    simp only [offsets, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have hkn : k ≤ n := by omega
  have hkd : 11 ∣ n - k := (Nat.modEq_iff_dvd' hkn).mp (show k ≡ n [MOD 11] from hnk.symm)
  exact eleven_thirteen_not_dvd_offset h hn hL hk (Or.inl rfl) hkd

/-- Every solution above 24 is divisible by 13. -/
theorem thirteen_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 13 ∣ n := by
  have hL := two_five_twenty_dvd_of_P h hn
  by_contra hd
  have hm : n % 13 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hd
  obtain ⟨k, hk, hnk⟩ := offsets_cover_thirteen hm
  have hk24 : k ≤ 24 := by
    simp only [offsets, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have hkn : k ≤ n := by omega
  have hkd : 13 ∣ n - k := (Nat.modEq_iff_dvd' hkn).mp (show k ≡ n [MOD 13] from hnk.symm)
  exact eleven_thirteen_not_dvd_offset h hn hL hk (Or.inr rfl) hkd

/-- The full audited necessary divisibility restriction. -/
theorem base_dvd_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 360360 ∣ n := by
  have hL := two_five_twenty_dvd_of_P h hn
  have h11 := eleven_dvd_of_P h hn
  have h13 := thirteen_dvd_of_P h hn
  have hL11 := (show Nat.Coprime 2520 11 by decide).mul_dvd_of_dvd_of_dvd hL h11
  have hfull := (show Nat.Coprime (2520 * 11) 13 by decide).mul_dvd_of_dvd_of_dvd hL11 h13
  simpa using hfull

/-- Version of the full restriction with the original pointwise hypothesis displayed. -/
theorem necessary_base {n : ℕ} (hn : 24 < n)
    (h : ∀ m : ℕ, m < n → m + σ 0 m ≤ n + 2) : 360360 ∣ n :=
  base_dvd_of_P h hn

/-- The finite supremum and pointwise formulations are equivalent, including `n = 0`. -/
theorem P_iff_iSup_le (n : ℕ) : P n ↔
    (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2 := by
  constructor
  · intro h
    by_cases hn : 0 < n
    · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
      exact ciSup_le fun m => h m.val m.isLt
    · have hn0 : n = 0 := by omega
      subst n
      simp
  · intro h m hm
    let f : Fin n → ℕ := fun i => (i : ℕ) + σ 0 (i : ℕ)
    have hle : f ⟨m, hm⟩ ≤ ⨆ i : Fin n, f i :=
      le_ciSup (Set.finite_range f).bddAbove ⟨m, hm⟩
    exact hle.trans h

/-- The full necessary restriction in the supremum formulation, independent of Spec. -/
theorem base_dvd_of_iSup_le {n : ℕ} (hn : 24 < n)
    (h : (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2) : 360360 ∣ n :=
  base_dvd_of_P ((P_iff_iSup_le n).mpr h) hn

/-- The numerical lower bound that follows from the full base restriction. -/
theorem base_le_of_P {n : ℕ} (h : P n) (hn : 24 < n) : 360360 ≤ n :=
  Nat.le_of_dvd (by omega) (base_dvd_of_P h hn)

/-- A general residual divisor-count bound after stripping a smooth part. -/
theorem sigma_zero_le_three_of_count {A r B M : ℕ} (hA : M ≤ A)
    (hB : B < 4 * M) (hcount : A * σ 0 r ≤ B) : σ 0 r ≤ 3 := by
  by_contra ht
  have hh := Nat.mul_le_mul hA (show 4 ≤ σ 0 r by omega)
  nlinarith

/-- A finite quadratic-residue test rules out a prime-square cofactor.
The statement is valid for every square, without a primality hypothesis. -/
theorem square_form_not_lattice {A k L n q : ℕ} (hLpos : 0 < L)
    (hcheck : ∀ r : ℕ, r < L → (A * r ^ 2 + k) % L ≠ 0)
    (hL : L ∣ n) (hn : n = A * q ^ 2 + k) : False := by
  apply hcheck (q % L) (Nat.mod_lt _ hLpos)
  have hm := Nat.mod_eq_zero_of_dvd hL
  rw [hn] at hm
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] using hm

/-- Smooth coefficients for the thirteen prime cofactors and the conditional
(even-quotient-only) offset sixteen. -/
def cofactorCoefficients : ℕ → Finset ℕ
  | 1 => {1}
  | 2 => {2}
  | 3 => {3}
  | 4 => {4}
  | 5 => {5, 25}
  | 6 => {6}
  | 8 => {8, 16}
  | 9 => {9, 27, 81}
  | 10 => {10, 50}
  | 12 => {12}
  | 16 => {16, 32, 64, 128, 256}
  | 18 => {18, 54, 162}
  | 20 => {20, 100}
  | 24 => {24, 48, 96}
  | _ => ∅

/-- A prime residual after stripping the entire 2,3,5-smooth part. -/
def PrimeCofactor (n k : ℕ) : Prop :=
  ∃ A q : ℕ, A ∈ cofactorCoefficients k ∧ q.Prime ∧
    ¬ 2 ∣ q ∧ ¬ 3 ∣ q ∧ ¬ 5 ∣ q ∧ n - k = A * q

set_option maxHeartbeats 4000000 in
/-- The complete thirteen-offset prime-cofactor table.

The smooth part contains *all* powers of 2,3,5. The residual classification
covers the unit, a prime, and a prime square; every square case is either over
the divisor budget or contradicted by an explicit finite quadratic-residue
test. The pure smooth cases are excluded using the already-proved base lower
bound, so no 2520-lattice exception is silently omitted.
-/
theorem prime_cofactor_of_P {n k : ℕ} (h : P n) (hn : 24 < n)
    (hk : k ∈ offsets) : PrimeCofactor n k := by
  have hL := two_five_twenty_dvd_of_P h hn
  have hbase := base_dvd_of_P h hn
  have hnbase := base_le_of_P h hn
  have hk' := hk
  simp only [offsets, Finset.mem_insert, Finset.mem_singleton] at hk'
  have hk0 : 0 < k := by omega
  have hk24 : k ≤ 24 := by omega
  have hkn : k < n := by omega
  obtain ⟨a, b, c, r, hfa, hfb, hfc, hr, h2r, h3r, h5r, hxr, hτxr⟩ :=
    smooth_split (n := n - k) (by omega)
  have hcount : (a + 1) * (b + 1) * (c + 1) * σ 0 r ≤ k + 2 := by
    have ht := offset_bound h hk0 hkn.le
    rwa [hτxr] at ht
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- Offset 1.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 1 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 1) (B := 3)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb, hc] at hxr hcount
      omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      norm_num [cofactorCoefficients, ha, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb, hc] at hcount
      rw [hrq] at hxr
      norm_num [ha, hb, hc] at hxr
      have hquad : n = 1 * q ^ 2 + 1 := by omega
      have hmod : 4 ∣ n := (by decide : 4 ∣ 360360).trans hbase
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)
  · -- Offset 2.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 2 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 2) (B := 4)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb, hc] at hxr hcount
      omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      norm_num [cofactorCoefficients, ha, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb, hc] at hcount
  · -- Offset 3.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 2 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 2) (B := 5)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb, hc] at hxr hcount
      omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      norm_num [cofactorCoefficients, ha, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb, hc] at hcount
  · -- Offset 4.
    have ha : a = 2 := hfa.trans
      (offset_factorization_fixed (v := 2) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 3 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 3) (B := 6)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb, hc] at hxr hcount
      omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      norm_num [cofactorCoefficients, ha, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb, hc] at hcount
  · -- Offset 5.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : 1 ≤ c := by
      rw [hfc]
      exact offset_factorization_lower (v := 1) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num)
    have hA : 2 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 2) (B := 7)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb] at hxr hcount
      have hcmax : c ≤ 6 := by omega
      interval_cases c <;> norm_num at hxr <;> omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      norm_num [ha, hb] at hcount
      have hcmax : c ≤ 2 := by omega
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      interval_cases c <;> norm_num [cofactorCoefficients, ha, hb]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb] at hcount
      have hcexact : c = 1 := by omega
      rw [hrq] at hxr
      norm_num [ha, hb, hcexact] at hxr
      have hquad : n = 5 * q ^ 2 + 5 := by omega
      have hmod : 8 ∣ n := (by decide : 8 ∣ 360360).trans hbase
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)
  · -- Offset 6.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 4 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 4) (B := 8)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb, hc] at hxr hcount
      omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      norm_num [cofactorCoefficients, ha, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb, hc] at hcount
  · -- Offset 8.
    have ha : 3 ≤ a := by
      rw [hfa]
      exact offset_factorization_lower (v := 3) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num)
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 4 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 4) (B := 10)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [hb, hc] at hxr hcount
      have hamax : a ≤ 9 := by omega
      interval_cases a <;> norm_num at hxr <;> omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      norm_num [hb, hc] at hcount
      have hamax : a ≤ 4 := by omega
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      interval_cases a <;> norm_num [cofactorCoefficients, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [hb, hc] at hcount
      omega
  · -- Offset 9.
    have ha : a = 0 := hfa.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : 2 ≤ b := by
      rw [hfb]
      exact offset_factorization_lower (v := 2) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num)
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 3 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 3) (B := 11)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hc] at hxr hcount
      have hbmax : b ≤ 10 := by omega
      interval_cases b <;> norm_num at hxr <;> omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      norm_num [ha, hc] at hcount
      have hbmax : b ≤ 4 := by omega
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      interval_cases b <;> norm_num [cofactorCoefficients, ha, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hc] at hcount
      have hbexact : b = 2 := by omega
      rw [hrq] at hxr
      norm_num [ha, hc, hbexact] at hxr
      have hquad : n = 9 * q ^ 2 + 9 := by omega
      have hmod : 8 ∣ n := (by decide : 8 ∣ 360360).trans hbase
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)
  · -- Offset 10.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : 1 ≤ c := by
      rw [hfc]
      exact offset_factorization_lower (v := 1) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num)
    have hA : 4 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 4) (B := 12)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb] at hxr hcount
      have hcmax : c ≤ 5 := by omega
      interval_cases c <;> norm_num at hxr <;> omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      norm_num [ha, hb] at hcount
      have hcmax : c ≤ 2 := by omega
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      interval_cases c <;> norm_num [cofactorCoefficients, ha, hb]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb] at hcount
      have hcexact : c = 1 := by omega
      rw [hrq] at hxr
      norm_num [ha, hb, hcexact] at hxr
      have hquad : n = 10 * q ^ 2 + 10 := by omega
      have hmod : 8 ∣ n := (by decide : 8 ∣ 360360).trans hbase
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)
  · -- Offset 12.
    have ha : a = 2 := hfa.trans
      (offset_factorization_fixed (v := 2) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 6 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 6) (B := 14)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb, hc] at hxr hcount
      omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      norm_num [cofactorCoefficients, ha, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb, hc] at hcount
  · -- Offset 18.
    have ha : a = 1 := hfa.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : 2 ≤ b := by
      rw [hfb]
      exact offset_factorization_lower (v := 2) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num)
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 6 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 6) (B := 20)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hc] at hxr hcount
      have hbmax : b ≤ 9 := by omega
      interval_cases b <;> norm_num at hxr <;> omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      norm_num [ha, hc] at hcount
      have hbmax : b ≤ 4 := by omega
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      interval_cases b <;> norm_num [cofactorCoefficients, ha, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hc] at hcount
      have hbexact : b = 2 := by omega
      rw [hrq] at hxr
      norm_num [ha, hc, hbexact] at hxr
      have hquad : n = 18 * q ^ 2 + 18 := by omega
      have hmod : 8 ∣ n := (by decide : 8 ∣ 360360).trans hbase
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)
  · -- Offset 20.
    have ha : a = 2 := hfa.trans
      (offset_factorization_fixed (v := 2) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hb : b = 0 := hfb.trans
      (offset_factorization_fixed (v := 0) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : 1 ≤ c := by
      rw [hfc]
      exact offset_factorization_lower (v := 1) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num)
    have hA : 6 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [ha, hb]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 6) (B := 22)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [ha, hb] at hxr hcount
      have hcmax : c ≤ 6 := by omega
      interval_cases c <;> norm_num at hxr <;> omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      norm_num [ha, hb] at hcount
      have hcmax : c ≤ 2 := by omega
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      interval_cases c <;> norm_num [cofactorCoefficients, ha, hb]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [ha, hb] at hcount
      have hcexact : c = 1 := by omega
      rw [hrq] at hxr
      norm_num [ha, hb, hcexact] at hxr
      have hquad : n = 20 * q ^ 2 + 20 := by omega
      have hmod : 3 ∣ n := (by decide : 3 ∣ 360360).trans hbase
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)
  · -- Offset 24.
    have ha : 3 ≤ a := by
      rw [hfa]
      exact offset_factorization_lower (v := 3) (L := 2520) Nat.prime_two
        hkn hL (by norm_num) (by norm_num)
    have hb : b = 1 := hfb.trans
      (offset_factorization_fixed (v := 1) (L := 2520) Nat.prime_three
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hc : c = 0 := hfc.trans
      (offset_factorization_fixed (v := 0) (L := 2520) (by decide : Nat.Prime 5)
        hkn hL (by norm_num) (by norm_num) (by norm_num))
    have hA : 8 ≤ (a + 1) * (b + 1) * (c + 1) := by
      simp only [hb, hc]
      omega
    have hτr := sigma_zero_le_three_of_count (M := 8) (B := 26)
      hA (by decide) hcount
    rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
    · norm_num [hb, hc] at hxr hcount
      have hamax : a ≤ 12 := by omega
      interval_cases a <;> norm_num at hxr <;> omega
    · have hτprime : σ 0 r = 2 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
      rw [hτprime] at hcount
      norm_num [hb, hc] at hcount
      have hamax : a ≤ 5 := by omega
      refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
      interval_cases a <;> norm_num [cofactorCoefficients, hb, hc]
    · have hτsquare : σ 0 (q ^ 2) = 3 := by
        simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
      rw [hrq, hτsquare] at hcount
      norm_num [hb, hc] at hcount
      have haexact : a = 3 := by omega
      rw [hrq] at hxr
      norm_num [hb, hc, haexact] at hxr
      have hquad : n = 24 * q ^ 2 + 24 := by omega
      have hmod : 9 ∣ n := (by decide : 9 ∣ 360360).trans hbase
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)

/-- The largest smooth coefficient in the thirteen-offset table is 162. -/
theorem cofactorCoefficient_le {k A : ℕ} (hk : k ∈ offsets)
    (hA : A ∈ cofactorCoefficients k) : A ≤ 162 := by
  simp only [offsets, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [cofactorCoefficients, Finset.mem_insert, Finset.mem_singleton] at hA
    omega

/-- Every prime cofactor in the table is larger than every sieve prime up to 1999. -/
theorem table_cofactor_gt_1999 {n k A q : ℕ} (h : P n) (hn : 24 < n)
    (hk : k ∈ offsets) (hA : A ∈ cofactorCoefficients k) (hform : n - k = A * q) :
    1999 < q := by
  have hnbase := base_le_of_P h hn
  have hAle := cofactorCoefficient_le hk hA
  have hk24 : k ≤ 24 := by
    simp only [offsets, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  by_contra hq
  have hprod := Nat.mul_le_mul hAle (show q ≤ 1999 by omega)
  norm_num at hprod
  omega

/-- Odd residues modulo four. -/
theorem odd_residues_mod_four {q : ℕ} (hq : q % 2 = 1) : q % 4 = 1 ∨ q % 4 = 3 := by
  omega

/-- Odd residues modulo eight. -/
theorem odd_residues_mod_eight {q : ℕ} (hq : q % 2 = 1) :
    q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
  omega

/-- Lift residue three modulo four to modulo eight. -/
theorem three_mod_four_residues {q : ℕ} (hq : q % 4 = 3) : q % 8 = 3 ∨ q % 8 = 7 := by
  omega

/-- The quotient by 360360 is even, or is 3 modulo 8. -/
theorem quotient_parity_of_P {n d : ℕ} (h : P n) (hn : 24 < n)
    (hnd : n = 360360 * d) : Even d ∨ d % 8 = 3 := by
  by_cases hd : Even d
  · exact Or.inl hd
  · right
    have hdodd : d % 2 = 1 := by
      have hd0 : d % 2 ≠ 0 := by simpa only [Nat.even_iff] using hd
      omega
    obtain ⟨A, q, hA, hq, h2q, h3q, h5q, hx⟩ :=
      prime_cofactor_of_P h hn (k := 8) (by decide)
    have hqodd : q % 2 = 1 := by
      simp only [Nat.dvd_iff_mod_eq_zero] at h2q
      omega
    have hd4 : d % 4 = 3 := by
      simp only [cofactorCoefficients, Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · have hf : 45045 * d = q + 1 := by omega
        have hm := congrArg (fun x : ℕ => x % 2) hf
        norm_num [Nat.mul_mod, Nat.add_mod, hdodd, hqodd] at hm
      · have hf : 45045 * d = 2 * q + 1 := by omega
        have hm := congrArg (fun x : ℕ => x % 4) hf
        rcases odd_residues_mod_four hqodd with hq4 | hq4 <;>
          simpa [Nat.mul_mod, Nat.add_mod, hq4] using hm
    by_contra hd3
    have hd7 : d % 8 = 7 := (three_mod_four_residues hd4).resolve_left hd3
    obtain ⟨B, r, hB, hr, h2r, h3r, h5r, hy⟩ :=
      prime_cofactor_of_P h hn (k := 24) (by decide)
    have hrodd : r % 2 = 1 := by
      simp only [Nat.dvd_iff_mod_eq_zero] at h2r
      omega
    simp only [cofactorCoefficients, Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl | rfl
    · have hf : 15015 * d = r + 1 := by omega
      have hm := congrArg (fun x : ℕ => x % 8) hf
      rcases odd_residues_mod_eight hrodd with hr8 | hr8 | hr8 | hr8 <;>
        norm_num [Nat.mul_mod, Nat.add_mod, hd7, hr8] at hm
    · have hf : 15015 * d = 2 * r + 1 := by omega
      have hm := congrArg (fun x : ℕ => x % 8) hf
      rcases odd_residues_mod_eight hrodd with hr8 | hr8 | hr8 | hr8 <;>
        norm_num [Nat.mul_mod, Nat.add_mod, hd7, hr8] at hm
    · have hf : 15015 * d = 4 * r + 1 := by omega
      have hm := congrArg (fun x : ℕ => x % 8) hf
      rcases odd_residues_mod_eight hrodd with hr8 | hr8 | hr8 | hr8 <;>
        norm_num [Nat.mul_mod, Nat.add_mod, hd7, hr8] at hm

/-- The quotient restriction packaged with the base decomposition. -/
theorem base_decomposition_of_P {n : ℕ} (h : P n) (hn : 24 < n) :
    ∃ d : ℕ, 0 < d ∧ n = 360360 * d ∧ (Even d ∨ d % 8 = 3) := by
  obtain ⟨d, hnd⟩ := base_dvd_of_P h hn
  exact ⟨d, by omega, hnd, quotient_parity_of_P h hn hnd⟩

/-- The offset-sixteen prime restriction is valid only for an even base quotient.
The classification includes every unit and square residual before excluding it. -/
theorem even_sub_sixteen_prime_cofactor {n d : ℕ} (h : P n) (hn : 24 < n)
    (hnd : n = 360360 * d) (hd : Even d) : PrimeCofactor n 16 := by
  have hd2 : 2 ∣ d := even_iff_two_dvd.mp hd
  have hL : 720720 ∣ n := by
    have hm := Nat.mul_dvd_mul_left 360360 hd2
    simpa [← hnd] using hm
  have hnlarge : 720720 ≤ n := Nat.le_of_dvd (by omega) hL
  have hkn : 16 < n := by omega
  obtain ⟨a, b, c, r, hfa, hfb, hfc, hr, h2r, h3r, h5r, hxr, hτxr⟩ :=
    smooth_split (n := n - 16) (by omega)
  have ha : 4 ≤ a := by
    rw [hfa]
    exact offset_factorization_lower (v := 4) (L := 720720) Nat.prime_two
      hkn hL (by norm_num) (by norm_num)
  have hb : b = 0 := hfb.trans
    (offset_factorization_fixed (v := 0) (L := 720720) Nat.prime_three
      hkn hL (by norm_num) (by norm_num) (by norm_num))
  have hc : c = 0 := hfc.trans
    (offset_factorization_fixed (v := 0) (L := 720720) (by decide : Nat.Prime 5)
      hkn hL (by norm_num) (by norm_num) (by norm_num))
  have hcount : (a + 1) * σ 0 r ≤ 18 := by
    have ht := offset_bound h (k := 16) (by decide) hkn.le
    rw [hτxr] at ht
    simpa [hb, hc] using ht
  have hτr := sigma_zero_le_three_of_count (M := 5) (B := 18)
    (show 5 ≤ a + 1 by omega) (by decide) hcount
  rcases sigma_zero_le_three (by omega : r ≠ 0) hτr with rfl | hprime | ⟨q, hq, hrq⟩
  · norm_num [hb, hc] at hxr hcount
    have hamax : a ≤ 17 := by omega
    have hpow : 2 ^ a ≤ 2 ^ 17 := Nat.pow_le_pow_right (by decide : 0 < 2) hamax
    norm_num at hpow
    omega
  · have hτprime : σ 0 r = 2 := by
      simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hprime
    rw [hτprime] at hcount
    have hamax : a ≤ 8 := by omega
    refine ⟨2 ^ a * 3 ^ b * 5 ^ c, r, ?_, hprime, h2r, h3r, h5r, hxr⟩
    interval_cases a <;> norm_num [cofactorCoefficients, hb, hc]
  · have hτsquare : σ 0 (q ^ 2) = 3 := by
      simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 2) hq
    rw [hrq, hτsquare] at hcount
    have ha45 : a = 4 ∨ a = 5 := by omega
    rw [hrq] at hxr
    rcases ha45 with rfl | rfl
    · norm_num [hb, hc] at hxr
      have hquad : n = 16 * q ^ 2 + 16 := by omega
      have hmod : 3 ∣ n := (by decide : 3 ∣ 720720).trans hL
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)
    · norm_num [hb, hc] at hxr
      have hquad : n = 32 * q ^ 2 + 16 := by omega
      have hmod : 5 ∣ n := (by decide : 5 ∣ 720720).trans hL
      exact False.elim (square_form_not_lattice (by decide)
        (by intro t ht; interval_cases t <;> norm_num) hmod hquad)

/-- Offset-sixteen cofactors also exceed 1999 on the even-quotient branch. -/
theorem even_sixteen_cofactor_gt_1999 {n d A q : ℕ} (hn : 24 < n)
    (hnd : n = 360360 * d) (hd : Even d) (hA : A ∈ cofactorCoefficients 16)
    (hform : n - 16 = A * q) : 1999 < q := by
  have hd2 : 2 ∣ d := even_iff_two_dvd.mp hd
  have hL : 720720 ∣ n := by
    have hm := Nat.mul_dvd_mul_left 360360 hd2
    simpa [← hnd] using hm
  have hnlarge : 720720 ≤ n := Nat.le_of_dvd (by omega) hL
  have hAle : A ≤ 256 := by
    simp only [cofactorCoefficients, Finset.mem_insert, Finset.mem_singleton] at hA
    omega
  by_contra hq
  have hprod := Nat.mul_le_mul hAle (show q ≤ 1999 by omega)
  norm_num at hprod
  omega

/-- A single package of the audited necessary structural restrictions.
This is a constraint on a putative solution, not a global nonexistence theorem. -/
theorem structural_certificate_of_P {n : ℕ} (h : P n) (hn : 24 < n) :
    ∃ d : ℕ, 0 < d ∧ n = 360360 * d ∧ (Even d ∨ d % 8 = 3) ∧
      (∀ k ∈ offsets, PrimeCofactor n k) ∧ (Even d → PrimeCofactor n 16) := by
  obtain ⟨d, hd, hnd, hparity⟩ := base_decomposition_of_P h hn
  exact ⟨d, hd, hnd, hparity, fun k hk => prime_cofactor_of_P h hn hk,
    fun he => even_sub_sixteen_prime_cofactor h hn hnd he⟩

end Structural
