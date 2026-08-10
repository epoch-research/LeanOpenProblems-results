import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

section AuxLemmas

private lemma a_eq (ν : ℕ) (hν : ν ≠ 0) :
    a ν = 2 ^ (ν - 1) * (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1)) / ν ! := by
  rw [a, dif_neg hν]
  rfl

private lemma prod_ne_zero (ν : ℕ) : (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have h2 : 2 ≤ 2 ^ k := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  omega

private lemma prod_odd (ν : ℕ) : ¬ (2:ℕ) ∣ (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) := by
  intro h
  obtain ⟨k, hk, hdvd⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff _).mp h
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have h2 : (2:ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h3 := Nat.dvd_sub h2 hdvd
  rw [Nat.sub_sub_self Nat.one_le_two_pow] at h3
  exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)

/-- For an odd prime `p`, the order `d` of `2` mod `p` divides `p - 1`, is positive,
and `p ∣ 2 ^ d - 1`. -/
private lemma order_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) ∣ p - 1 ∧ 0 < orderOf (2 : ZMod p) ∧
      p ∣ 2 ^ orderOf (2 : ZMod p) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hp.two_le
    omega
  have hdvd : orderOf (2 : ZMod p) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2)
  have hpos : 0 < orderOf (2 : ZMod p) := by
    rcases Nat.eq_zero_or_pos (orderOf (2 : ZMod p)) with h | h
    · rw [h] at hdvd
      have := Nat.eq_zero_of_zero_dvd hdvd
      have := hp.two_le
      omega
    · exact h
  refine ⟨hdvd, hpos, ?_⟩
  have hpow : (2 : ZMod p) ^ orderOf (2 : ZMod p) = 1 := pow_orderOf_eq_one _
  have hcast : ((2 ^ orderOf (2 : ZMod p) - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, hpow, Nat.cast_one,
      sub_self]
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- For an odd prime `p` with `d = orderOf (2 : ZMod p)`, we have
`p ^ ((ν - 1) / d) ∣ ∏_{k=1}^{ν-1} (2^k - 1)`. -/
private lemma pow_dvd_prod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ν : ℕ) :
    p ^ ((ν - 1) / orderOf (2 : ZMod p)) ∣ ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) := by
  obtain ⟨hdvd, hd0, hpd⟩ := order_facts hp hp2
  set d := orderOf (2 : ZMod p) with hd
  set m := (ν - 1) / d with hm
  have h1 : p ^ m = ∏ _j ∈ Finset.Icc 1 m, p := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have h2 : ∀ j ∈ Finset.Icc 1 m, p ∣ 2 ^ (j * d) - 1 := by
    intro j hj
    refine hpd.trans ?_
    have h' : (2:ℕ) ^ d - 1 ^ d ∣ (2 ^ d) ^ j - (1 ^ d) ^ j := Nat.sub_dvd_pow_sub_pow _ _ j
    simpa [← pow_mul, mul_comm d j] using h'
  have h3 : (∏ _j ∈ Finset.Icc 1 m, p) ∣ ∏ j ∈ Finset.Icc 1 m, (2 ^ (j * d) - 1) :=
    Finset.prod_dvd_prod_of_dvd _ _ h2
  have h4 : ∏ j ∈ Finset.Icc 1 m, (2 ^ (j * d) - 1)
      = ∏ k ∈ (Finset.Icc 1 m).image (· * d), (2 ^ k - 1) := by
    rw [Finset.prod_image]
    intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_right hd0 hij
  have h5 : (Finset.Icc 1 m).image (· * d) ⊆ Finset.Ico 1 ν := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_Icc] at hk
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hk
    have hmd : m * d ≤ ν - 1 := Nat.div_mul_le_self _ _
    have hjd : j * d ≤ m * d := Nat.mul_le_mul_right d hj2
    have hpos : 0 < j * d := Nat.mul_pos hj1 hd0
    rw [Finset.mem_Ico]
    omega
  rw [h1]
  exact (h3.trans (h4 ▸ Finset.prod_dvd_prod_of_subset _ _ _ h5))

/-- The division in the definition of `a` is exact. -/
private lemma factorial_dvd (ν : ℕ) :
    ν ! ∣ 2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) := by
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · simp
  have hP0 : (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) ≠ 0 := prod_ne_zero ν
  have hN0 : 2 ^ (ν - 1) * (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hP0
  rw [← Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero ν) hN0, Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  haveI : Fact q.Prime := ⟨hq⟩
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
  by_cases hq2 : q = 2
  · subst hq2
    have h1 : padicValNat 2 (ν !) ≤ ν - 1 := by
      have h' := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 2 hν.ne'
      omega
    have h2 : ν - 1 ≤ padicValNat 2 (2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1)) := by
      rw [← padicValNat_dvd_iff_le hN0]
      exact Dvd.dvd.mul_right dvd_rfl _
    omega
  · have hq1 : 0 < q - 1 := by have := hq.two_le; omega
    have hle1 : padicValNat q (ν !) ≤ (ν - 1) / (q - 1) := by
      have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero q hν.ne'
      rw [Nat.le_div_iff_mul_le hq1, Nat.mul_comm]
      omega
    obtain ⟨hdvd, hd0, _⟩ := order_facts hq hq2
    have hdle : orderOf (2 : ZMod q) ≤ q - 1 := Nat.le_of_dvd hq1 hdvd
    have hle2 : (ν - 1) / (q - 1) ≤ (ν - 1) / orderOf (2 : ZMod q) :=
      Nat.div_le_div_left hdle hd0
    have hle3 : (ν - 1) / orderOf (2 : ZMod q)
        ≤ padicValNat q (2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1)) := by
      rw [← padicValNat_dvd_iff_le hN0]
      exact (pow_dvd_prod hq hq2 ν).trans (dvd_mul_left _ _)
    omega

/-- If `p` is an odd prime and `t ≥ 2`, then `p` divides `a (p * t - 1)`. -/
private lemma odd_prime_dvd_a {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : ℕ} (ht : 2 ≤ t) :
    p ∣ a (p * t - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpt : 6 ≤ p * t := by
    calc (6:ℕ) = 3 * 2 := by norm_num
    _ ≤ p * t := Nat.mul_le_mul hp3 ht
  set ν := p * t - 1 with hν
  have hν0 : ν ≠ 0 := by omega
  have hP0 : (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) ≠ 0 := prod_ne_zero ν
  have hN0 : 2 ^ (ν - 1) * (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hP0
  have hfact := factorial_dvd ν
  have haN : a ν * ν ! = 2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) := by
    rw [a_eq ν hν0]
    exact Nat.div_mul_cancel hfact
  have ha0 : a ν ≠ 0 := by
    intro h'
    rw [h', zero_mul] at haN
    exact hN0 haN.symm
  obtain ⟨hdvd, hd0, _⟩ := order_facts hp hp2
  set d := orderOf (2 : ZMod p) with hd
  have hq1 : 0 < p - 1 := by omega
  have hdle : d ≤ p - 1 := Nat.le_of_dvd hq1 hdvd
  -- `v_p(N) ≥ t + (t - 2) / (p - 1)`
  have hvN : t + (t - 2) / (p - 1)
      ≤ padicValNat p (2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1)) := by
    have e0 : t * (p - 1) + t = t * p := by
      conv_rhs => rw [show p = (p - 1) + 1 by omega]
      rw [Nat.mul_add, Nat.mul_one]
    have e1 : ν - 1 = (t - 2) + t * (p - 1) := by
      have e0' : t * p = p * t := Nat.mul_comm t p
      omega
    have e2 : (ν - 1) / (p - 1) = (t - 2) / (p - 1) + t := by
      rw [e1, Nat.add_mul_div_right _ _ hq1]
    have hle2 : (ν - 1) / (p - 1) ≤ (ν - 1) / d := Nat.div_le_div_left hdle hd0
    have hle3 : (ν - 1) / d
        ≤ padicValNat p (2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1)) := by
      rw [← padicValNat_dvd_iff_le hN0]
      exact (pow_dvd_prod hp hp2 ν).trans (dvd_mul_left _ _)
    omega
  -- `v_p(ν !) = (t - 1) + v_p((t-1)!)`
  have hvD : padicValNat p (ν !) = padicValNat p ((t - 1)!) + (t - 1) := by
    have e0 : p * (t - 1) + p = p * t := by
      conv_rhs => rw [show t = (t - 1) + 1 by omega]
      rw [Nat.mul_add, Nat.mul_one]
    have e2 : ν = p * (t - 1) + (p - 1) := by omega
    rw [e2, padicValNat_factorial_mul_add (t - 1) (by omega : p - 1 < p),
      padicValNat_factorial_mul]
  have hvD_le : padicValNat p ((t - 1)!) ≤ (t - 2) / (p - 1) := by
    have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (show t - 1 ≠ 0 by omega)
    rw [Nat.le_div_iff_mul_le hq1, Nat.mul_comm]
    omega
  by_contra hnd
  have hva : padicValNat p (a ν) = 0 := padicValNat.eq_zero_of_not_dvd hnd
  have hsum : padicValNat p (2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1))
      = padicValNat p (a ν) + padicValNat p (ν !) := by
    rw [← haN, padicValNat.mul ha0 (Nat.factorial_ne_zero ν)]
  omega

/-- `v_2 ((2^v - 1)!) = 2^v - 1 - v`. -/
private lemma padic_two_factorial_pow (v : ℕ) :
    padicValNat 2 ((2 ^ v - 1)!) = 2 ^ v - 1 - v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction v with
  | zero => simp
  | succ v ih =>
    have hv : v < 2 ^ v := Nat.lt_two_pow_self
    have e : 2 ^ (v + 1) - 1 = 2 * (2 ^ v - 1) + 1 := by
      rw [pow_succ]
      omega
    rw [e, padicValNat_factorial_mul_add _ (by norm_num : 1 < 2), padicValNat_factorial_mul, ih]
    omega

/-- The case `n = 2 ^ v`, `v ≥ 2`: the divisibility fails. -/
private lemma not_dvd_pow_two (v : ℕ) (hv : 2 ≤ v) :
    ¬ (2 ^ v ∣ a (2 ^ v - 1) + 2 ^ (2 ^ v - 2)) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvpow : v + 2 ≤ 2 ^ v := by
    clear h
    induction v with
    | zero => omega
    | succ v ih =>
      rcases Nat.lt_or_ge v 2 with h' | h'
      · interval_cases v
        · omega
        · norm_num
      · have := ih (by omega)
        rw [pow_succ]
        omega
  set ν := 2 ^ v - 1 with hν
  have hν0 : ν ≠ 0 := by omega
  have hP0 : (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) ≠ 0 := prod_ne_zero ν
  have hN0 : 2 ^ (ν - 1) * (∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hP0
  have hfact := factorial_dvd ν
  have haN : a ν * ν ! = 2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) := by
    rw [a_eq ν hν0]
    exact Nat.div_mul_cancel hfact
  have ha0 : a ν ≠ 0 := by
    intro h'
    rw [h', zero_mul] at haN
    exact hN0 haN.symm
  have hvN : padicValNat 2 (2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1)) = ν - 1 := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hP0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (prod_odd ν), add_zero]
  have hvD : padicValNat 2 (ν !) = 2 ^ v - 1 - v := padic_two_factorial_pow v
  have hmul : padicValNat 2 (a ν) + padicValNat 2 (ν !) = ν - 1 := by
    rw [← padicValNat.mul ha0 (Nat.factorial_ne_zero ν), haN, hvN]
  have hva : padicValNat 2 (a ν) = v - 1 := by omega
  have hdvdpow : (2:ℕ) ^ v ∣ 2 ^ (2 ^ v - 2) := pow_dvd_pow 2 (by omega)
  have hdvda : 2 ^ v ∣ a ν := by
    have h' := Nat.dvd_sub h hdvdpow
    rwa [Nat.add_sub_cancel] at h'
  have hle : v ≤ padicValNat 2 (a ν) := (padicValNat_dvd_iff_le ha0).mp hdvda
  omega

end AuxLemmas

-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) :=
by
  intro h
  -- Step 1: if an odd prime `p` divides `n`, then `n = p`.
  have hstep1 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → n = p := by
    intro p hp hp2 hpn
    by_contra hne
    obtain ⟨t, rfl⟩ := hpn
    have hp0 := hp.two_le
    have ht2 : 2 ≤ t := by
      rcases Nat.lt_or_ge t 2 with h' | h'
      · interval_cases t
        · omega
        · omega
      · exact h'
    have hdvda : p ∣ a (p * t - 1) := odd_prime_dvd_a hp hp2 ht2
    have hpsum : p ∣ a (p * t - 1) + 2 ^ (p * t - 2) := (dvd_mul_right p t).trans h
    have hpow : p ∣ 2 ^ (p * t - 2) := (Nat.dvd_add_right hdvda).mp hpsum
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hpow
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  -- Step 2: `n` is prime.
  have hprime : n.Prime := by
    by_contra hnp
    have hall : ∀ {q : ℕ}, q.Prime → q ∣ n → q = 2 := by
      intro q hq hqn
      by_contra hq2
      exact hnp (by rw [hstep1 q hq hq2 hqn]; exact hq)
    have hn0 : n ≠ 0 := by omega
    have hpow2 : n = 2 ^ n.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hn0 hall
    set v := n.primeFactorsList.length with hv
    have hv2 : 2 ≤ v := by
      by_contra hvlt
      interval_cases v <;> omega
    rw [hpow2] at h
    exact not_dvd_pow_two v hv2 h
  -- Step 3: `2` is a primitive root mod `n`.
  have hp2 : n ≠ 2 := by omega
  haveI : Fact n.Prime := ⟨hprime⟩
  set ν := n - 1 with hν
  have hν0 : ν ≠ 0 := by omega
  have hnda : ¬ n ∣ a ν := by
    intro hda
    have hpow : n ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hda).mp h
    have h2 : n ∣ 2 := hprime.dvd_of_dvd_pow hpow
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hfact := factorial_dvd ν
  have haN : a ν * ν ! = 2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) := by
    rw [a_eq ν hν0]
    exact Nat.div_mul_cancel hfact
  have hndN : ¬ n ∣ 2 ^ (ν - 1) * ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) := by
    intro hdN
    rw [← haN] at hdN
    rcases (Nat.Prime.dvd_mul hprime).mp hdN with h' | h'
    · exact hnda h'
    · rw [Nat.Prime.dvd_factorial hprime] at h'
      omega
  obtain ⟨hdvd, hd0, hpd⟩ := order_facts hprime hp2
  set d := orderOf (2 : ZMod n) with hd
  have hdeq : d = n - 1 := by
    by_contra hdne
    have hdlt : d < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hdne
    have hmem : d ∈ Finset.Ico 1 ν := Finset.mem_Ico.mpr ⟨hd0, by omega⟩
    have hprod : (2 ^ d - 1 : ℕ) ∣ ∏ k ∈ Finset.Ico 1 ν, (2 ^ k - 1) :=
      Finset.dvd_prod_of_mem _ hmem
    exact hndN ((hpd.trans hprod).trans (dvd_mul_left _ _))
  refine ⟨hprime, ?_⟩
  rw [Nat.totient_prime hprime, ← hdeq]
  exact ⟨pow_orderOf_eq_one _, fun l hl => orderOf_dvd_of_pow_eq_one hl⟩
