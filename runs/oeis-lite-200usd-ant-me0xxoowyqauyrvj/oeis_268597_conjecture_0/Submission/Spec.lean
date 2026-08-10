import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

/-- General deterministic residue construction.  If `c` is coprime to a prime
`p`, the Euler totient satisfies `φ(c) ∣ c`, and `c / φ(c) ≤ p - 1`, then the
number `x = c * p ^ (k+1)` realises the residue `c * p ^ k - 1`.  Indeed
`φ(x) = φ(c) · p^k · (p-1)` and
`c·p^(k+1) - 1 = (c·p^k - 1) + (c/φ(c))·φ(x)` with `c·p^k - 1 < φ(x)`. -/
private theorem residue_smooth_pp (c p k : ℕ) (hp : p.Prime) (hc0 : 0 < c)
    (hcop : Nat.Coprime c p) (hdvd : Nat.totient c ∣ c)
    (hle : c / Nat.totient c ≤ p - 1) :
    (c * p ^ (k + 1) - 1) % Nat.totient (c * p ^ (k + 1)) = c * p ^ k - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  have hφc : 0 < Nat.totient c := Nat.totient_pos.mpr hc0
  have hcoppk : Nat.Coprime c (p ^ (k + 1)) := hcop.pow_right _
  have htot : Nat.totient (c * p ^ (k + 1)) = Nat.totient c * (p ^ k * (p - 1)) := by
    rw [Nat.totient_mul hcoppk, Nat.totient_prime_pow_succ hp]
  rw [htot]
  set D := Nat.totient c * (p ^ k * (p - 1)) with hD
  have hcc : Nat.totient c * (c / Nat.totient c) = c := Nat.mul_div_cancel' hdvd
  have key : c * p ^ (k + 1) - 1 = (c * p ^ k - 1) + (c / Nat.totient c) * D := by
    have e1 : (c / Nat.totient c) * D = c * (p ^ k * (p - 1)) := by
      rw [hD]
      calc (c / Nat.totient c) * (Nat.totient c * (p ^ k * (p - 1)))
          = (Nat.totient c * (c / Nat.totient c)) * (p ^ k * (p - 1)) := by ring
        _ = c * (p ^ k * (p - 1)) := by rw [hcc]
    rw [e1]
    have hadd : c * (p ^ k * (p - 1)) + c * p ^ k = c * p ^ (k + 1) := by
      have hpp : p ^ k * (p - 1) + p ^ k = p ^ k * p := by
        have : p ^ k * (p - 1) + p ^ k = p ^ k * ((p - 1) + 1) := by ring
        rw [this]; congr 1; omega
      calc c * (p ^ k * (p - 1)) + c * p ^ k
          = c * (p ^ k * (p - 1) + p ^ k) := by ring
        _ = c * (p ^ k * p) := by rw [hpp]
        _ = c * p ^ (k + 1) := by ring
    have h1 : 1 ≤ c * p ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hlt : c * p ^ k - 1 < D := by
    have hcD : c * p ^ k ≤ D := by
      rw [hD]
      have hrw : c * p ^ k = Nat.totient c * (c / Nat.totient c) * p ^ k := by rw [hcc]
      rw [hrw]
      calc Nat.totient c * (c / Nat.totient c) * p ^ k
          = Nat.totient c * (p ^ k * (c / Nat.totient c)) := by ring
        _ ≤ Nat.totient c * (p ^ k * (p - 1)) := by
              apply Nat.mul_le_mul_left
              apply Nat.mul_le_mul_left
              exact hle
    have h1 : 1 ≤ c * p ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  rw [key, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- The prime-power special case (`c = 1`): for a prime `p`, the number
`x = p ^ (k+1)` realises the residue `p ^ k - 1`. -/
private theorem residue_prime_pow (p k : ℕ) (hp : p.Prime) :
    (p ^ (k + 1) - 1) % Nat.totient (p ^ (k + 1)) = p ^ k - 1 := by
  have h := residue_smooth_pp 1 p k hp (by norm_num) (Nat.coprime_one_left p)
    (by simp) (by simp only [Nat.totient_one, Nat.div_one]; have := hp.two_le; omega)
  simpa using h

/-- Convenience wrapper: from a decomposition `n + 1 = c * p ^ k` (with the
hypotheses of `residue_smooth_pp`), the witness `x = c * p ^ (k+1)` shows the
defining set of `A268597 n` is nonempty. -/
private theorem nonempty_of_decomp (n c p k : ℕ) (hp : p.Prime) (hc0 : 0 < c)
    (hcop : Nat.Coprime c p) (hdvd : Nat.totient c ∣ c)
    (hle : c / Nat.totient c ≤ p - 1) (heq : c * p ^ k = n + 1) :
    {x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}.Nonempty := by
  refine ⟨c * p ^ (k + 1), Nat.mul_pos hc0 (pow_pos hp.pos _), ?_⟩
  show (c * p ^ (k + 1) - 1) % Nat.totient (c * p ^ (k + 1)) = n
  rw [residue_smooth_pp c p k hp hc0 hcop hdvd hle]
  omega

/-- Whenever `n + 1` is a prime power, the defining set of `A268597 n` is
nonempty (take `x = p ^ (k+1)` where `p ^ k = n + 1`). -/
private theorem nonempty_of_isPrimePow (n : ℕ) (h : IsPrimePow (n + 1)) :
    {x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}.Nonempty := by
  obtain ⟨p, k, hp, hk, hpk⟩ := h
  have hpn : p.Prime := Nat.prime_iff.mpr hp
  refine ⟨p ^ (k + 1), pow_pos hpn.pos _, ?_⟩
  show (p ^ (k + 1) - 1) % Nat.totient (p ^ (k + 1)) = n
  rw [residue_prime_pow p k hpn]; omega

/-- Whenever `n + 1 = 2 ^ a · r` with `r` an (odd) prime power, the defining set
is nonempty (take `x = 2 ^ a · p ^ (j+1)` where `r = p ^ j`; here the core
`c = 2^a` satisfies `φ(c) ∣ c` and `c / φ(c) = 2 ≤ p - 1`). -/
private theorem nonempty_of_two_pow_mul_primePow (n a r : ℕ)
    (hr2 : ¬ (2:ℕ) ∣ r) (hsplit : 2 ^ a * r = n + 1) (h2 : IsPrimePow r)
    (h1 : ¬ IsPrimePow (n + 1)) :
    {x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}.Nonempty := by
  obtain ⟨p, j, hpp, hj, hpj⟩ := h2
  have hpprime : p.Prime := Nat.prime_iff.mpr hpp
  have hpodd : Odd p := by
    rcases hpprime.eq_two_or_odd' with h | h
    · exact absurd (by rw [← hpj, h]; exact dvd_pow_self 2 (by omega : j ≠ 0)) hr2
    · exact h
  have ha1 : a ≠ 0 := by
    intro h
    rw [h, pow_zero, one_mul] at hsplit
    apply h1
    rw [← hsplit, ← hpj]
    exact ⟨p, j, hpp, hj, rfl⟩
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha1
  have htot : Nat.totient (2 ^ (a' + 1)) = 2 ^ a' := by
    rw [Nat.totient_prime_pow_succ Nat.prime_two]; ring
  have hcop : Nat.Coprime (2 ^ (a' + 1)) p :=
    (Nat.coprime_two_left.mpr hpodd).pow_left _
  apply nonempty_of_decomp n (2 ^ (a' + 1)) p j hpprime (by positivity) hcop ?_ ?_ ?_
  · rw [htot]; exact pow_dvd_pow 2 (Nat.le_succ a')
  · rw [htot, Nat.pow_div (Nat.le_succ a') (by norm_num)]
    have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hpodd
    have h2le := hpprime.two_le
    have he : a' + 1 - a' = 1 := by omega
    rw [he, pow_one]; omega
  · rw [hpj]; exact hsplit

/-- Totient of a `2^(a'+1) * 3^(b'+1)` core. -/
private theorem core23_totient (a' b' : ℕ) :
    Nat.totient (2 ^ (a'+1) * 3 ^ (b'+1)) = 2 ^ (a'+1) * 3 ^ b' := by
  have h23 : Nat.Coprime 2 3 := by decide
  have hcop : Nat.Coprime (2 ^ (a'+1)) (3 ^ (b'+1)) := h23.pow (a'+1) (b'+1)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow_succ Nat.prime_two,
      Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 3)]
  ring

private theorem core23_coprime (a' b' p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime (2 ^ (a'+1) * 3 ^ (b'+1)) p := by
  have c2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  have c3 : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).mpr (by omega)
  exact (c2.pow_left _).mul_left (c3.pow_left _)

private theorem core23_dvd (a' b' : ℕ) :
    Nat.totient (2 ^ (a'+1) * 3 ^ (b'+1)) ∣ (2 ^ (a'+1) * 3 ^ (b'+1)) := by
  rw [core23_totient]; exact ⟨3, by ring⟩

private theorem core23_le (a' b' p : ℕ) (hp5 : 5 ≤ p) :
    (2 ^ (a'+1) * 3 ^ (b'+1)) / Nat.totient (2 ^ (a'+1) * 3 ^ (b'+1)) ≤ p - 1 := by
  rw [core23_totient]
  have hpos : 0 < 2 ^ (a'+1) * 3 ^ b' := by positivity
  have h3 : 2 ^ (a'+1) * 3 ^ (b'+1) = 3 * (2 ^ (a'+1) * 3 ^ b') := by ring
  rw [h3, Nat.mul_div_cancel _ hpos]; omega

/-- Whenever `n + 1 = 2^(a'+1) · 3^(b'+1) · p^j` with `p ≥ 5` prime, the defining
set is nonempty (take `x = 2^(a'+1) · 3^(b'+1) · p^(j+1)`; the `3`-smooth core
`c = 2^(a'+1)·3^(b'+1)` satisfies `φ(c) ∣ c` and `c / φ(c) = 3 ≤ p - 1`). -/
private theorem nonempty_of_core23 (n a' b' p j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (heq : 2 ^ (a'+1) * 3 ^ (b'+1) * p ^ j = n + 1) :
    {x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}.Nonempty :=
  nonempty_of_decomp n (2 ^ (a'+1) * 3 ^ (b'+1)) p j hp (by positivity)
    (core23_coprime a' b' p hp hp5) (core23_dvd a' b') (core23_le a' b' p hp5) heq

/-- Residue identity for the family `x = ℓ · q²` (distinct primes `ℓ ≥ 3`,
`q ≥ 5`): `φ(x) = (ℓ-1)·q·(q-1)` and `ℓq² - 1 = (q² + (ℓ-1)q - 1) + φ(x)` with
`q² + (ℓ-1)q - 1 < φ(x)`, so the residue is `q² + (ℓ-1)q - 1`. -/
private theorem residue_ell_qsq (l q : ℕ) (hl : l.Prime) (hq : q.Prime)
    (hl3 : 3 ≤ l) (hq5 : 5 ≤ q) (hlq : l ≠ q) :
    (l * q ^ 2 - 1) % Nat.totient (l * q ^ 2) = q ^ 2 + (l - 1) * q - 1 := by
  have hcop : Nat.Coprime l (q ^ 2) := ((Nat.coprime_primes hl hq).mpr hlq).pow_right _
  have htot : Nat.totient (l * q ^ 2) = (l - 1) * (q * (q - 1)) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hl,
        show q ^ 2 = q ^ (1 + 1) from by ring, Nat.totient_prime_pow_succ hq]
    ring
  rw [htot]
  obtain ⟨A, rfl⟩ : ∃ A, l = A + 3 := ⟨l - 3, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, q = B + 5 := ⟨q - 5, by omega⟩
  set D := (A + 3 - 1) * ((B + 5) * (B + 5 - 1)) with hD
  have hDe : D = (A + 2) * ((B + 5) * (B + 4)) := by
    rw [hD, show A + 3 - 1 = A + 2 from by omega, show B + 5 - 1 = B + 4 from by omega]
  have hge : 1 ≤ (B + 5) ^ 2 + (A + 2) * (B + 5) := by
    have : 0 < (B + 5) ^ 2 + (A + 2) * (B + 5) := by positivity
    omega
  have key : (A + 3) * (B + 5) ^ 2 - 1 = ((B + 5) ^ 2 + (A + 2) * (B + 5) - 1) + D := by
    have hsum : (B + 5) ^ 2 + (A + 2) * (B + 5) + D = (A + 3) * (B + 5) ^ 2 := by
      rw [hDe]; ring
    omega
  have hlt : (B + 5) ^ 2 + (A + 2) * (B + 5) - 1 < D := by
    rw [hDe]
    have h1 : A + B + 7 ≤ (A + 2) * (B + 4) := by nlinarith [Nat.zero_le (A * B)]
    have hle : (B + 5) ^ 2 + (A + 2) * (B + 5) ≤ (A + 2) * ((B + 5) * (B + 4)) := by
      calc (B + 5) ^ 2 + (A + 2) * (B + 5) = (B + 5) * (A + B + 7) := by ring
        _ ≤ (B + 5) * ((A + 2) * (B + 4)) := by gcongr
        _ = (A + 2) * ((B + 5) * (B + 4)) := by ring
    omega
  have hgoal : (B + 5) ^ 2 + (A + 3 - 1) * (B + 5) - 1
      = (B + 5) ^ 2 + (A + 2) * (B + 5) - 1 := by
    rw [show A + 3 - 1 = A + 2 from by omega]
  rw [hgoal, key,
      show ((B + 5) ^ 2 + (A + 2) * (B + 5) - 1) + D
        = ((B + 5) ^ 2 + (A + 2) * (B + 5) - 1) + 1 * D from by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- From a decomposition `n + 1 = q² + (ℓ-1)·q` (distinct primes `ℓ ≥ 3`, `q ≥ 5`),
the witness `x = ℓ · q²` shows the defining set is nonempty. -/
private theorem nonempty_of_ell_qsq (n l q : ℕ) (hl : l.Prime) (hq : q.Prime)
    (hl3 : 3 ≤ l) (hq5 : 5 ≤ q) (hlq : l ≠ q)
    (heq : q ^ 2 + (l - 1) * q = n + 1) :
    {x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}.Nonempty := by
  refine ⟨l * q ^ 2, by positivity, ?_⟩
  show (l * q ^ 2 - 1) % Nat.totient (l * q ^ 2) = n
  rw [residue_ell_qsq l q hl hq hl3 hq5 hlq]
  omega

/-- Detection wrapper for the `x = ℓ·q²` family.  Writing `S = 4(n+1)+(ℓ-1)²`,
the family applies exactly when `S` is a perfect square `s²` with
`q = (s-(ℓ-1))/2` a prime `≥ 5` distinct from `ℓ` (then `n+1 = q² + (ℓ-1)q`). -/
private theorem nonempty_of_sqdetect (n l : ℕ) (hl : l.Prime) (hl3 : 3 ≤ l)
    (hs : (Nat.sqrt (4 * (n + 1) + (l - 1) ^ 2)) ^ 2 = 4 * (n + 1) + (l - 1) ^ 2)
    (hpar : (Nat.sqrt (4 * (n + 1) + (l - 1) ^ 2) - (l - 1)) % 2 = 0)
    (hge : l - 1 ≤ Nat.sqrt (4 * (n + 1) + (l - 1) ^ 2))
    (hq5 : 5 ≤ (Nat.sqrt (4 * (n + 1) + (l - 1) ^ 2) - (l - 1)) / 2)
    (hqp : ((Nat.sqrt (4 * (n + 1) + (l - 1) ^ 2) - (l - 1)) / 2).Prime)
    (hlq : l ≠ (Nat.sqrt (4 * (n + 1) + (l - 1) ^ 2) - (l - 1)) / 2) :
    {x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}.Nonempty := by
  set s := Nat.sqrt (4 * (n + 1) + (l - 1) ^ 2) with hsdef
  set q := (s - (l - 1)) / 2 with hqdef
  have hs2 : s = 2 * q + (l - 1) := by omega
  have hsq : (2 * q + (l - 1)) ^ 2 = 4 * (n + 1) + (l - 1) ^ 2 := by rw [← hs2]; exact hs
  have heq : q ^ 2 + (l - 1) * q = n + 1 := by nlinarith [hsq, hl3]
  exact nonempty_of_ell_qsq n l q hl hqp hl3 hq5 hlq heq

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  have hne : {x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}.Nonempty := by
    by_cases h : IsPrimePow (n + 1)
    · -- Provable case: `n + 1` is a prime power, realised by `x = p^(k+1)`.
      exact nonempty_of_isPrimePow n h
    · by_cases h' : IsPrimePow (ordCompl[2] (n + 1))
      · -- Provable case: `n + 1 = 2^a · p^j` with `p` odd prime;
        -- realised by `x = 2^a · p^(j+1)`.
        exact nonempty_of_two_pow_mul_primePow n ((n + 1).factorization 2)
          (ordCompl[2] (n + 1)) (Nat.not_dvd_ordCompl Nat.prime_two (by omega))
          (Nat.ordProj_mul_ordCompl_eq_self (n + 1) 2) h' h
      · -- Try the `3`-smooth core `c = 2^a · 3^b` (both exponents ≥ 1):
        -- if the part of `n+1` coprime to `6` is a prime power `p^k` (`p ≥ 5`),
        -- realise `n` by `x = 2^a · 3^b · p^(k+1)`.
        by_cases hpp : IsPrimePow (ordCompl[3] (ordCompl[2] (n + 1)))
        · by_cases ha1 : (n + 1).factorization 2 ≠ 0
          · by_cases hb1 : (ordCompl[2] (n + 1)).factorization 3 ≠ 0
            · obtain ⟨p, k, hpprime', hk, hpk⟩ := hpp
              have hpprime : p.Prime := Nat.prime_iff.mpr hpprime'
              have hn1 : n + 1 ≠ 0 := by omega
              have hm1ne : ordCompl[2] (n + 1) ≠ 0 := (Nat.ordCompl_pos 2 hn1).ne'
              have hm2dvdm1 : ordCompl[3] (ordCompl[2] (n + 1)) ∣ ordCompl[2] (n + 1) :=
                Nat.ordCompl_dvd _ 3
              have h2m1 : ¬ (2 : ℕ) ∣ ordCompl[2] (n + 1) :=
                Nat.not_dvd_ordCompl Nat.prime_two hn1
              have h2m2 : ¬ (2 : ℕ) ∣ ordCompl[3] (ordCompl[2] (n + 1)) :=
                fun hd => h2m1 (hd.trans hm2dvdm1)
              have h3m2 : ¬ (3 : ℕ) ∣ ordCompl[3] (ordCompl[2] (n + 1)) :=
                Nat.not_dvd_ordCompl (by norm_num) hm1ne
              have hpdvd : p ∣ ordCompl[3] (ordCompl[2] (n + 1)) :=
                hpk ▸ dvd_pow_self p (by omega : k ≠ 0)
              have hp2 : p ≠ 2 := by rintro rfl; exact h2m2 hpdvd
              have hp3 : p ≠ 3 := by rintro rfl; exact h3m2 hpdvd
              have hp5 : 5 ≤ p := by
                have h2le := hpprime.two_le
                by_contra hlt
                push_neg at hlt
                interval_cases p
                · exact hp2 rfl
                · exact hp3 rfl
                · exact absurd hpprime (by norm_num)
              obtain ⟨a', ha'⟩ := Nat.exists_eq_succ_of_ne_zero ha1
              obtain ⟨b', hb'⟩ := Nat.exists_eq_succ_of_ne_zero hb1
              simp only [Nat.succ_eq_add_one] at ha' hb'
              have e1 : 2 ^ ((n + 1).factorization 2) * ordCompl[2] (n + 1) = n + 1 :=
                Nat.ordProj_mul_ordCompl_eq_self (n + 1) 2
              have e2 : 3 ^ ((ordCompl[2] (n + 1)).factorization 3)
                  * ordCompl[3] (ordCompl[2] (n + 1)) = ordCompl[2] (n + 1) :=
                Nat.ordProj_mul_ordCompl_eq_self (ordCompl[2] (n + 1)) 3
              have heq : 2 ^ (a' + 1) * 3 ^ (b' + 1) * p ^ k = n + 1 := by
                calc 2 ^ (a' + 1) * 3 ^ (b' + 1) * p ^ k
                    = 2 ^ ((n + 1).factorization 2)
                        * 3 ^ ((ordCompl[2] (n + 1)).factorization 3)
                        * ordCompl[3] (ordCompl[2] (n + 1)) := by rw [← ha', ← hb', hpk]
                  _ = 2 ^ ((n + 1).factorization 2)
                        * (3 ^ ((ordCompl[2] (n + 1)).factorization 3)
                          * ordCompl[3] (ordCompl[2] (n + 1))) := by ring
                  _ = 2 ^ ((n + 1).factorization 2) * ordCompl[2] (n + 1) := by rw [e2]
                  _ = n + 1 := e1
              exact nonempty_of_core23 n a' b' p k hpprime hp5 heq
            · -- Vacuous: if `v₃ = 0` then `ordCompl[3](ordCompl[2](n+1)) = ordCompl[2](n+1)`,
              -- so `hpp` contradicts `h'`.
              exfalso
              push_neg at hb1
              have hmm : ordCompl[3] (ordCompl[2] (n + 1)) = ordCompl[2] (n + 1) := by
                rw [hb1]; simp
              rw [hmm] at hpp
              exact h' hpp
          · -- Irreducible case A: `n + 1 = 3^b · p^k` is ODD (`v₂ = 0`) with `b ≥ 1`
            -- and `p ≥ 5`.  No core `c` with `φ(c) ∣ c` is available (`3^b` fails,
            -- since `φ(3^b) = 2·3^(b-1) ∤ 3^b`), so every witness needs a free prime.
            -- E.g. `n = 44` (`45 = 3²·5`): minimal witness `117 = 3²·13`, forcing the
            -- prime `13 = 45/9·… `, i.e. an even cototient `45 = p+q-1` ⇒ Goldbach.
            -- Partial relief: the perfect-square subfamily `n+1 = q(q+2)` (here with
            -- `q ≡ 1 mod 3`) is realised deterministically by `x = 3·q²`.
            by_cases hsq : Nat.sqrt (n + 2) ^ 2 = n + 2 ∧ 6 ≤ Nat.sqrt (n + 2)
                ∧ (Nat.sqrt (n + 2) - 1).Prime
            · obtain ⟨hs, hs6, hsp⟩ := hsq
              set q := Nat.sqrt (n + 2) - 1 with hqdef
              have hq1 : q + 1 = Nat.sqrt (n + 2) := by omega
              have h3 : q ^ 2 + 2 * q + 1 = n + 2 := by
                have h2 : (q + 1) ^ 2 = n + 2 := by rw [hq1]; exact hs
                rw [← h2]; ring
              apply nonempty_of_ell_qsq n 3 q (by norm_num) hsp (by norm_num)
                (by omega) (by omega)
              rw [show (3 : ℕ) - 1 = 2 from rfl]; omega
            · sorry
        · -- Irreducible case B: the part of `n + 1` coprime to `6` is NOT a prime
          -- power, i.e. it has ≥ 2 distinct prime factors `≥ 5`.  Every witness is a
          -- product of *specific* primes (minimal ones are Goldbach semiprimes `p·q`
          -- with `p + q = n + 2`; e.g. `n = 64`, `66 = 5+61 = 7+59 = 13+53 = …`).
          -- This is equivalent in strength to the binary Goldbach conjecture and is
          -- not provable from any tool available in Mathlib.
          -- Partial relief: the perfect-square subfamily `n+1 = q(q+2)` (here with
          -- `q ≡ 2 mod 3`) is realised deterministically by `x = 3·q²`.
          by_cases hsq : Nat.sqrt (n + 2) ^ 2 = n + 2 ∧ 6 ≤ Nat.sqrt (n + 2)
              ∧ (Nat.sqrt (n + 2) - 1).Prime
          · obtain ⟨hs, hs6, hsp⟩ := hsq
            set q := Nat.sqrt (n + 2) - 1 with hqdef
            have hq1 : q + 1 = Nat.sqrt (n + 2) := by omega
            have h3 : q ^ 2 + 2 * q + 1 = n + 2 := by
              have h2 : (q + 1) ^ 2 = n + 2 := by rw [hq1]; exact hs
              rw [← h2]; ring
            apply nonempty_of_ell_qsq n 3 q (by norm_num) hsp (by norm_num)
              (by omega) (by omega)
            rw [show (3 : ℕ) - 1 = 2 from rfl]; omega
          · sorry
  unfold A268597
  exact (Nat.sInf_mem hne).1
