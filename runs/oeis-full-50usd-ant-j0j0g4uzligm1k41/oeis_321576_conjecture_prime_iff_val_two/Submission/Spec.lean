import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A321576: $a(n)$ is the smallest $b > 1$ such that $b^n - (b-1)^n$ has all divisors $d \equiv 1 \pmod n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n -- Note: This is natural number subtraction. For n > 1 and b >= 2, b^n > (b-1)^n.
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    -- sInf finds the smallest element of a set in a partial order, which is the minimum for $\mathbb{N}$.
    sInf S_n
  else
    0

/-! ### Supporting lemmas -/

/-- For prime `n` and a prime `q` dividing `2^n - 1`, we have `q ≡ 1 [MOD n]`.
This is because the multiplicative order of `2` modulo `q` divides the prime `n`, is not `1`
(else `q ∣ 1`), so equals `n`; and the order divides `q - 1` by Fermat. -/
theorem primefac_modeq (n q : ℕ) (hn : n.Prime) (hq : q.Prime) (hdvd : q ∣ 2^n - 1) :
    q ≡ 1 [MOD n] := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hn0 : n ≠ 0 := hn.pos.ne'
  have h1le : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : (2 : ZMod q) ^ n = 1 := by
    have hz : ((2 ^ n - 1 : ℕ) : ZMod q) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hdvd
    rw [Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at hz
    exact hz
  have hne : (2 : ZMod q) ≠ 0 := by
    intro h
    have hd2 : q ∣ 2 := by
      have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
      exact (ZMod.natCast_eq_zero_iff 2 q).mp this
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd2
    subst hq2
    have he : 2 ∣ 2^n := dvd_pow_self 2 hn0
    obtain ⟨k, hk⟩ := he
    obtain ⟨j, hj⟩ := hdvd
    omega
  have hord_dvd_n : orderOf (2 : ZMod q) ∣ n := orderOf_dvd_of_pow_eq_one h2
  have hord_ne_one : orderOf (2 : ZMod q) ≠ 1 := by
    intro h
    have h21 : (2 : ZMod q) = 1 := orderOf_eq_one_iff.mp h
    have hcontra : (1 : ZMod q) = 0 := by
      have : (2 : ZMod q) - 1 = 0 := by rw [h21]; ring
      linear_combination this
    exact one_ne_zero hcontra
  have hord_eq : orderOf (2 : ZMod q) = n := by
    rcases (hn.eq_one_or_self_of_dvd _ hord_dvd_n) with h | h
    · exact absurd h hord_ne_one
    · exact h
  have hord_dvd : orderOf (2 : ZMod q) ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hne)
  rw [hord_eq] at hord_dvd
  exact ((Nat.modEq_iff_dvd' hq.one_le).mpr hord_dvd).symm

/-- When `n` is prime, *every* divisor of `2^n - 1` is `≡ 1 [MOD n]`. -/
theorem all_div_modeq (n : ℕ) (hn : n.Prime) :
    ∀ d, d ∣ 2^n - 1 → d ≡ 1 [MOD n] := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases Nat.lt_or_ge d 2 with hlt | hge
    · interval_cases d
      · rw [Nat.zero_dvd] at hd
        have hgt : 1 < 2^n := Nat.one_lt_two_pow hn.pos.ne'
        omega
      · rfl
    · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      have hqdvd : q ∣ 2^n - 1 := hqd.trans hd
      have hq1 : q ≡ 1 [MOD n] := primefac_modeq n q hn hq hqdvd
      obtain ⟨e, he⟩ := hqd
      have hepos : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h | h
        · subst h; simp at he; omega
        · exact h
      have helt : e < d := by nlinarith [hq.two_le]
      have hed : e ∣ d := ⟨q, by rw [he]; ring⟩
      have hedvd : e ∣ 2^n - 1 := dvd_trans hed hd
      have he1 : e ≡ 1 [MOD n] := ih e helt hedvd
      calc d = q * e := he
        _ ≡ 1 * 1 [MOD n] := Nat.ModEq.mul hq1 he1
        _ = 1 := by ring

/-- Membership of `2` in the defining set simplifies to the divisor condition on `2^n - 1`. -/
theorem two_mem_iff (n : ℕ) :
    (2 ∈ { b | b > 1 ∧ ∀ (d : ℕ), d ∣ (b ^ n - (b - 1) ^ n) → d ≡ 1 [MOD n] })
      ↔ (∀ d, d ∣ 2^n - 1 → d ≡ 1 [MOD n]) := by
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, h⟩ d hd; apply h; simpa using hd
  · intro h; exact ⟨by norm_num, fun d hd => h d (by simpa using hd)⟩

/-- `a n = 2` iff every divisor of `2^n - 1` is `≡ 1 [MOD n]`. -/
theorem reduction (n : ℕ) (hn : n > 1) :
    a n = 2 ↔ (∀ d, d ∣ 2^n - 1 → d ≡ 1 [MOD n]) := by
  have hn0 : n > 0 := by omega
  rw [a, dif_pos hn0]
  set S : Set ℕ := { b | b > 1 ∧ ∀ (d : ℕ), d ∣ (b ^ n - (b - 1) ^ n) → d ≡ 1 [MOD n] } with hS
  rw [← two_mem_iff n]
  show sInf S = 2 ↔ 2 ∈ S
  constructor
  · intro h
    have hne : S.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty] at h; simp [Nat.sInf_empty] at h
    have := Nat.sInf_mem hne; rw [h] at this; exact this
  · intro h
    have hle : sInf S ≤ 2 := Nat.sInf_le h
    have hmem := Nat.sInf_mem ⟨2, h⟩
    have hgt : sInf S > 1 := hmem.1
    omega

/-- If a prime `p ∣ n` and a divisor `q ∣ 2^p - 1` has `n ∤ (q - 1)`, then the divisor
condition fails: `q` is a divisor of `2^n - 1` (since `2^p - 1 ∣ 2^n - 1`) but `q ≢ 1 [MOD n]`. -/
theorem bad_prime_lemma (n p q : ℕ) (hpn : p ∣ n) (hqp : q ∣ 2^p - 1)
    (hq1 : 1 ≤ q) (hnq : ¬ (n ∣ (q - 1))) :
    ¬ (∀ d, d ∣ 2^n - 1 → d ≡ 1 [MOD n]) := by
  intro h
  have hdvd : (2^p - 1) ∣ (2^n - 1) := by
    obtain ⟨k, hk⟩ := hpn
    subst hk
    rw [pow_mul]
    exact (nat_sub_dvd_pow_sub_pow (2^p) 1 k).trans (by rw [one_pow])
  exact hnq ((Nat.modEq_iff_dvd' hq1).mp (h q (hqp.trans hdvd)).symm)

theorem coprime_of_not_dvd (n p : ℕ) (hp : p.Prime) (h : ¬ p ∣ n) : Nat.Coprime n p :=
  ((hp.coprime_iff_not_dvd).mpr h).symm

/-- If `n > 1` is composite, `p` is prime, `c` is coprime to `n`, and `n ∣ p * c`, contradiction
(forcing `n ∣ p`, hence `n ∈ {1, p}`). -/
theorem not_dvd_of_coprime (n p c : ℕ) (hp : p.Prime) (hn1 : n > 1) (hnp : ¬ n.Prime)
    (hcop : Nat.Coprime n c) (hd : n ∣ p * c) : False := by
  have hnp' : n ∣ p := Nat.Coprime.dvd_of_dvd_mul_right hcop hd
  rcases (Nat.dvd_prime hp).mp hnp' with h | h
  · omega
  · exact hnp (h ▸ hp)

/-- Composite even `n > 2` fails the divisor condition: `3 ∣ 2^n - 1` (as `n` is even) but
`3 ≢ 1 [MOD n]`. -/
theorem even_composite_bad (n : ℕ) (hev : 2 ∣ n) (hn : n > 2) :
    ¬ (∀ d, d ∣ 2^n - 1 → d ≡ 1 [MOD n]) := by
  intro h
  have h3 : (3 : ℕ) ∣ 2^n - 1 := by
    obtain ⟨m, hm⟩ := hev
    subst hm
    have he : 2^(2*m) - 1 = 4^m - 1 := by rw [pow_mul]; norm_num
    rw [he]
    have hmod : (4:ℕ)^m ≡ 1 [MOD 3] := by
      calc (4:ℕ)^m ≡ 1^m [MOD 3] := Nat.ModEq.pow m (by decide)
        _ = 1 := one_pow m
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod.symm
  have hkey := h 3 h3
  have h1n : (1 : ℕ) % n = 1 := Nat.one_mod_eq_one.mpr (by omega)
  have h3n : (3 : ℕ) % n = 3 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.ModEq, h1n, h3n] at hkey
  omega

/--
Conjecture: If n is prime, then a(n) = 2. Conjecture: If n is composite, then a(n) > 2.
Equivalently, for $n > 1$, $a(n)=2$ if and only if $n$ is prime.
-/
theorem oeis_321576_conjecture_prime_iff_val_two (n : ℕ) (h_n : n > 1) :
  a n = 2 ↔ Nat.Prime n :=
by
  rw [reduction n h_n]
  constructor
  · -- The hard direction: if every divisor of `2^n - 1` is `≡ 1 [MOD n]`, then `n` is prime.
    intro hcond
    by_contra hnp
    -- `n > 1` and `¬ Prime n` means `n` is composite; we exhibit a bad divisor.
    rcases Nat.even_or_odd n with hev | hodd
    · -- Even composite: divisor `3`.
      have h2n : 2 ∣ n := hev.two_dvd
      have hn2 : n > 2 := by
        rcases Nat.lt_or_ge n 3 with h | h
        · interval_cases n
          · exact absurd Nat.prime_two hnp
        · exact h
      exact even_composite_bad n h2n hn2 hcond
    · -- Odd composite.  We split on the least prime factor.
      have hodd2 : ¬ 2 ∣ n := by
        rw [Nat.two_dvd_ne_zero]; rwa [Nat.odd_iff] at hodd
      have hc2 : Nat.Coprime n 2 := coprime_of_not_dvd n 2 (by norm_num) hodd2
      by_cases h3 : 3 ∣ n
      · -- least prime 3: divisor `7` of `2^3 - 1`, and `n ∤ 6`.
        refine (bad_prime_lemma n 3 7 h3 (by decide) (by decide) ?_) hcond
        intro hd
        have hd' : n ∣ 3 * 2 := by
          have e : (7:ℕ) - 1 = 3 * 2 := by norm_num
          rwa [e] at hd
        exact not_dvd_of_coprime n 3 2 (by norm_num) h_n hnp hc2 hd'
      · have hc3 : Nat.Coprime n 3 := coprime_of_not_dvd n 3 (by norm_num) h3
        by_cases h5 : 5 ∣ n
        · -- least prime 5: divisor `31` of `2^5 - 1`, and `n ∤ 30`.
          refine (bad_prime_lemma n 5 31 h5 (by decide) (by decide) ?_) hcond
          intro hd
          have hcop : Nat.Coprime n 6 := by
            have : (6:ℕ) = 2 * 3 := by norm_num
            rw [this]; exact hc2.mul_right hc3
          have hd' : n ∣ 5 * 6 := by
            have e : (31:ℕ) - 1 = 5 * 6 := by norm_num
            rwa [e] at hd
          exact not_dvd_of_coprime n 5 6 (by norm_num) h_n hnp hcop hd'
        · have hc5 : Nat.Coprime n 5 := coprime_of_not_dvd n 5 (by norm_num) h5
          by_cases h7 : 7 ∣ n
          · -- least prime 7: divisor `127` of `2^7 - 1`, and `n ∤ 126`.
            refine (bad_prime_lemma n 7 127 h7 (by decide) (by decide) ?_) hcond
            intro hd
            have hcop : Nat.Coprime n 18 := by
              have : (18:ℕ) = 2 * (3 * 3) := by norm_num
              rw [this]; exact hc2.mul_right (hc3.mul_right hc3)
            have hd' : n ∣ 7 * 18 := by
              have e : (127:ℕ) - 1 = 7 * 18 := by norm_num
              rwa [e] at hd
            exact not_dvd_of_coprime n 7 18 (by norm_num) h_n hnp hcop hd'
          · have hc7 : Nat.Coprime n 7 := coprime_of_not_dvd n 7 (by norm_num) h7
            by_cases h11 : 11 ∣ n
            · -- least prime 11: divisor `23` of `2^11 - 1`, and `n ∤ 22`.
              refine (bad_prime_lemma n 11 23 h11 (by decide) (by decide) ?_) hcond
              intro hd
              have hd' : n ∣ 11 * 2 := by
                have e : (23:ℕ) - 1 = 11 * 2 := by norm_num
                rwa [e] at hd
              exact not_dvd_of_coprime n 11 2 (by norm_num) h_n hnp hc2 hd'
            · by_cases h13 : 13 ∣ n
              · -- least prime 13: divisor `8191` of `2^13 - 1`, and `n ∤ 8190`.
                refine (bad_prime_lemma n 13 8191 h13 (by decide) (by decide) ?_) hcond
                intro hd
                have hcop : Nat.Coprime n 630 := by
                  have : (630:ℕ) = 2 * (3 * (3 * (5 * 7))) := by norm_num
                  rw [this]
                  exact hc2.mul_right (hc3.mul_right (hc3.mul_right (hc5.mul_right hc7)))
                have hd' : n ∣ 13 * 630 := by
                  have e : (8191:ℕ) - 1 = 13 * 630 := by norm_num
                  rwa [e] at hd
                exact not_dvd_of_coprime n 13 630 (by norm_num) h_n hnp hcop hd'
              · -- Remaining case: `n` is composite with least prime factor `≥ 17`.
                -- We first dispatch the *non-pseudoprime* sub-case cleanly: if `n ∤ 2^n - 2`
                -- then the divisor `d = 2^n - 1` of `2^n - 1` is itself bad, since
                -- `2^n - 1 ≡ 1 [MOD n] ↔ n ∣ 2^n - 2`.
                by_cases hP : n ∣ 2 ^ n - 2
                · -- `n` is a base-2 Fermat pseudoprime (a Poulet number) whose least prime
                  -- factor is `≥ 17`.  This is the genuinely hard, *open* kernel of the
                  -- conjecture.  For such `n` one must exhibit a prime factor `q` of `2^n - 1`
                  -- with `q ≢ 1 [MOD n]`.  The elementary "small divisor `2^p - 1`" method used
                  -- above provably *fails* here: e.g. for `n = 4369 = 17 · 257`, every prime
                  -- factor of `2^17 - 1 = 131071` is `≡ 1 mod n`, so the required bad prime can
                  -- only come from `2^257 - 1`, and the obstruction is invisible to congruence
                  -- reasoning (the *product* of the prime factors of `2^257 - 1` *is* `≡ 1 mod
                  -- 17`; only their explicit values, `≡ 2, 7, 11 mod 17`, reveal it).  Worse, for
                  -- `n = p^2` with `p` a Wieferich prime and `2^p - 1` a Mersenne prime, there
                  -- would be *no* bad prime at all, making the conjecture equivalent to the open
                  -- question of whether a Mersenne-prime exponent can be a Wieferich prime.  No
                  -- such `n` is known (the statement holds for every `n` checked), but a complete
                  -- proof is beyond current mathematics.
                  sorry
                · -- `n` is not a base-2 pseudoprime: `2^n - 1` is itself a bad divisor.
                  have h1lt : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
                  have h1le : 1 ≤ 2 ^ n - 1 := by omega
                  have hmod : (2 ^ n - 1) ≡ 1 [MOD n] := hcond (2 ^ n - 1) dvd_rfl
                  have hdvd : n ∣ (2 ^ n - 1) - 1 := (Nat.modEq_iff_dvd' h1le).mp hmod.symm
                  have heq : (2 ^ n - 1) - 1 = 2 ^ n - 2 := by omega
                  rw [heq] at hdvd
                  exact hP hdvd
  · -- The easy direction: if `n` is prime then every divisor of `2^n - 1` is `≡ 1 [MOD n]`.
    exact all_div_modeq n
