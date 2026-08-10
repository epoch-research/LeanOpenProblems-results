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

/-- CORE: many factors of the product are divisible by `p`. -/
lemma core_dvd (p N : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ ((N-1)/(p-1)) ∣ ∏ k ∈ Finset.Ico 1 N, (2^k - 1) := by
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · have := hp.two_le; omega
  have hp1 : 1 ≤ p - 1 := by omega
  set M := (N-1)/(p-1) with hM
  -- coprimality and Fermat
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
  have hfermat : p ∣ 2 ^ (p - 1) - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    exact Nat.pow_card_sub_one_sub_one_mod_card hp hcop
  -- each multiple of (p-1) gives a divisible factor
  have hdvdj : ∀ j : ℕ, p ∣ 2 ^ (j * (p - 1)) - 1 := by
    intro j
    have h1 : (2 ^ (p - 1) - 1) ∣ (2 ^ (p - 1)) ^ j - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 ^ (p - 1)) 1 j
      simpa using this
    have h2 : (2 ^ (p - 1)) ^ j = 2 ^ (j * (p - 1)) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [h2] at h1
    exact dvd_trans hfermat h1
  -- image set
  have hsub : (Finset.Icc 1 M).image (· * (p - 1)) ⊆ Finset.Ico 1 N := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hj1, hjM⟩, rfl⟩ := hx
    rw [Finset.mem_Ico]
    constructor
    · have : 1 ≤ j * (p - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact this
    · have hjle : j * (p - 1) ≤ N - 1 := by
        have hmle : M * (p - 1) ≤ N - 1 := Nat.div_mul_le_self _ _
        calc j * (p - 1) ≤ M * (p - 1) := Nat.mul_le_mul_right _ hjM
          _ ≤ N - 1 := hmle
      -- N ≥ 2 since M ≥ 1
      have hM1 : 1 ≤ M := le_trans hj1 hjM
      have hN2 : 2 ≤ N := by
        by_contra h
        push_neg at h
        interval_cases N <;> simp_all
      omega
  have hinj : Set.InjOn (· * (p - 1)) (↑(Finset.Icc 1 M)) := by
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  -- p^M divides the product over image
  have step1 : p ^ M ∣ ∏ j ∈ Finset.Icc 1 M, (2 ^ (j * (p - 1)) - 1) := by
    have : (∏ _j ∈ Finset.Icc 1 M, p) ∣ ∏ j ∈ Finset.Icc 1 M, (2 ^ (j * (p - 1)) - 1) :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hdvdj j)
    rwa [Finset.prod_const, Nat.card_Icc] at this
    -- now p ^ (M+1-1) = p ^ M
  -- reindex
  have step2 : ∏ j ∈ Finset.Icc 1 M, (2 ^ (j * (p - 1)) - 1)
      = ∏ k ∈ (Finset.Icc 1 M).image (· * (p - 1)), (2 ^ k - 1) := by
    rw [Finset.prod_image hinj]
  have step3 : (∏ k ∈ (Finset.Icc 1 M).image (· * (p - 1)), (2 ^ k - 1))
      ∣ ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  calc p ^ M ∣ ∏ j ∈ Finset.Icc 1 M, (2 ^ (j * (p - 1)) - 1) := step1
    _ = _ := step2
    _ ∣ _ := step3

/-- p-adic valuation of factorial upper bound. -/
lemma padicVal_factorial_le (p m : ℕ) (hp : p.Prime) :
    padicValNat p (m.factorial) ≤ (m - 1) / (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hlt : (p - 1) * padicValNat p (m.factorial) < m :=
      sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
    have hp1 : 0 < p - 1 := by have := hp.two_le; omega
    rw [Nat.le_div_iff_mul_le hp1, Nat.mul_comm]
    omega

/-- Integrality: `N!` divides the numerator of `a N`. -/
lemma fact_dvd (N : ℕ) :
    N.factorial ∣ 2 ^ (N - 1) * ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hpp hpk
  have hp : p.Prime := hpp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hk : k ≤ padicValNat 2 (N.factorial) :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero N)).mp hpk
    have hle : padicValNat 2 (N.factorial) ≤ N - 1 := by
      have h2 : padicValNat 2 (N.factorial) < N :=
        padicValNat_factorial_lt_of_ne_zero 2 (by omega)
      omega
    have : (2:ℕ) ^ k ∣ 2 ^ (N - 1) := pow_dvd_pow 2 (le_trans hk hle)
    exact dvd_mul_of_dvd_left this _
  · have hk : k ≤ padicValNat p (N.factorial) :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero N)).mp hpk
    have hle : padicValNat p (N.factorial) ≤ (N - 1) / (p - 1) :=
      padicVal_factorial_le p N hp
    have hcore : p ^ ((N - 1) / (p - 1)) ∣ ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) :=
      core_dvd p N hp hp2
    have : p ^ k ∣ ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) :=
      dvd_trans (pow_dvd_pow p (le_trans hk hle)) hcore
    exact dvd_mul_of_dvd_right this _

lemma prod_pos (N : ℕ) : 0 < ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  have : 1 ≤ k := hk.1
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
  omega

/-- The defining identity: `a N * N! = 2^(N-1) * (product)`. -/
lemma a_mul (N : ℕ) (hN : N ≠ 0) :
    a N * N.factorial = 2 ^ (N - 1) * ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) := by
  unfold a
  rw [dif_neg hN]
  simp only [Nat.pred_eq_sub_one]
  exact Nat.div_mul_cancel (fact_dvd N)

lemma a_pos (N : ℕ) (hN : N ≠ 0) : 0 < a N := by
  have h := a_mul N hN
  have hrhs : 0 < 2 ^ (N - 1) * ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) :=
    Nat.mul_pos (pow_pos (by norm_num : 0 < 2) _) (prod_pos N)
  rw [← h] at hrhs
  exact Nat.pos_of_mul_pos_left (by rwa [Nat.mul_comm] at hrhs)

/-- Core mechanism: if `p^(v_p(N!)+1)` divides the product, then `p ∣ a N`. -/
lemma p_dvd_a (p N : ℕ) (hp : p.Prime) (hN : N ≠ 0)
    (hBdvd : p ^ (padicValNat p (N.factorial) + 1) ∣ ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1)) :
    p ∣ a N := by
  haveI : Fact p.Prime := ⟨hp⟩
  set V := padicValNat p (N.factorial) with hV
  have hdvdprod : p ^ (V + 1) ∣ 2 ^ (N - 1) * ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) :=
    dvd_trans hBdvd (Dvd.dvd.mul_left dvd_rfl _)
  rw [← a_mul N hN] at hdvdprod
  have hane : a N ≠ 0 := (a_pos N hN).ne'
  have hfne : N.factorial ≠ 0 := Nat.factorial_ne_zero N
  have hle : V + 1 ≤ padicValNat p (a N * N.factorial) :=
    (padicValNat_dvd_iff_le (Nat.mul_ne_zero hane hfne)).mp hdvdprod
  rw [padicValNat.mul hane hfne, ← hV] at hle
  have : 1 ≤ padicValNat p (a N) := by omega
  exact dvd_of_one_le_padicValNat this

/-- Main composite step: for an odd prime `p` and `c ≥ 2`, `p ∣ a (p*c - 1)`. -/
lemma key_p_dvd_a (p c : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hc : 2 ≤ c) :
    p ∣ a (p * c - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · have := hp.two_le; omega
  have hp1 : 0 < p - 1 := by omega
  set N := p * c - 1 with hN
  have hpc : 6 ≤ p * c := le_trans (by norm_num) (Nat.mul_le_mul hp3 hc)
  have hNne : N ≠ 0 := by rw [hN]; omega
  apply p_dvd_a p N hp hNne
  -- arithmetic facts
  have hdiv : (p * c - 1) / p = c - 1 := by
    have key : p * c - 1 = (p - 1) + (c - 1) * p := by
      have h1 : (c - 1) * p = p * c - p := by rw [Nat.sub_one_mul, Nat.mul_comm]
      have h2 : p ≤ p * c := Nat.le_mul_of_pos_right p (by omega)
      omega
    rw [key, Nat.add_mul_div_right _ _ (by omega : 0 < p), Nat.div_eq_of_lt (by omega : p - 1 < p),
      Nat.zero_add]
  -- V = padicValNat p N!
  have hVeq : padicValNat p (N.factorial) = padicValNat p ((c - 1).factorial) + (c - 1) := by
    have h1 := padicValNat_mul_div_factorial (p := p) N
    rw [hN, hdiv] at h1
    rw [← h1, padicValNat_factorial_mul]
  -- M = (N-1)/(p-1)
  have hMeq : (N - 1) / (p - 1) = c + (c - 2) / (p - 1) := by
    have key2 : p * c - 2 = (c - 2) + c * (p - 1) := by
      have h1 : c * (p - 1) = p * c - c := by rw [Nat.mul_sub_one, Nat.mul_comm]
      have h2 : c ≤ p * c := Nat.le_mul_of_pos_left c (by omega)
      omega
    rw [hN, show p * c - 1 - 1 = p * c - 2 by omega, key2,
      Nat.add_mul_div_right _ _ hp1, Nat.add_comm]
  -- factorial bound
  have hfact : padicValNat p ((c - 1).factorial) ≤ (c - 2) / (p - 1) := by
    have := padicVal_factorial_le p (c - 1) hp
    rwa [show c - 1 - 1 = c - 2 by omega] at this
  -- M ≥ V + 1
  have hMV : padicValNat p (N.factorial) + 1 ≤ (N - 1) / (p - 1) := by
    rw [hVeq, hMeq]; omega
  -- conclude
  have hcore : p ^ ((N - 1) / (p - 1)) ∣ ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1) :=
    core_dvd p N hp hp2
  exact dvd_trans (pow_dvd_pow p hMV) hcore

/-- Prime step: a small power-of-2 order gives a divisible factor, hence `p ∣ a (p-1)`. -/
lemma prime_factor_dvd_a (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p - 1)
    (hdvd : p ∣ 2 ^ k - 1) : p ∣ a (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNne : p - 1 ≠ 0 := by have := hp.two_le; omega
  apply p_dvd_a p (p - 1) hp hNne
  have hV0 : padicValNat p ((p - 1).factorial) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [Nat.Prime.dvd_factorial hp]
    omega
  rw [hV0, zero_add, pow_one]
  exact dvd_trans hdvd
    (Finset.dvd_prod_of_mem (fun k => 2 ^ k - 1) (by rw [Finset.mem_Ico]; exact ⟨hk1, hkp⟩))

/-- Digit sum of `2^e - 1` in base 2 is `e`. -/
lemma digits_two_sum (e : ℕ) : (Nat.digits 2 (2 ^ e - 1)).sum = e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpos : 0 < 2 ^ (e + 1) - 1 := by
      have : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
      have : 2 ≤ 2 ^ (e + 1) := by
        calc 2 = 2 ^ 1 := by ring
          _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.digits_def' (by norm_num : 1 < 2) hpos]
    have hmod : (2 ^ (e + 1) - 1) % 2 = 1 := by
      have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      omega
    have hdiv : (2 ^ (e + 1) - 1) / 2 = 2 ^ e - 1 := by
      have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      have : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
      omega
    rw [hmod, hdiv, List.sum_cons, ih]
    omega

/-- Power-of-two case: `2^e ∤ a (2^e - 1)` for `e ≥ 2`. -/
lemma pow2_not_dvd_a (e : ℕ) (he : 2 ≤ e) : ¬ 2 ^ e ∣ a (2 ^ e - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  set N := 2 ^ e - 1 with hN
  have h2e : 4 ≤ 2 ^ e := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hNne : N ≠ 0 := by rw [hN]; omega
  have hNe : e ≤ N := by
    rw [hN]
    have : e < 2 ^ e := Nat.lt_two_pow_self
    omega
  -- product is odd
  have hBodd : ¬ (2 ∣ ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1)) := by
    rw [Nat.prime_two.prime.dvd_finset_prod_iff]
    push_neg
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  -- digit sum
  have hds : (Nat.digits 2 N).sum = e := by rw [hN]; exact digits_two_sum e
  have hF : padicValNat 2 (N.factorial) = N - e := by
    have h := sub_one_mul_padicValNat_factorial (p := 2) N
    rw [hds] at h
    simpa using h
  -- valuation of a N
  have e1 : padicValNat 2 (a N) + padicValNat 2 (N.factorial)
      = (N - 1) + 0 := by
    have heq := a_mul N hNne
    have key : padicValNat 2 (a N * N.factorial)
        = padicValNat 2 (2 ^ (N - 1) * ∏ k ∈ Finset.Ico 1 N, (2 ^ k - 1)) := by rw [heq]
    rw [padicValNat.mul (a_pos N hNne).ne' (Nat.factorial_ne_zero N),
        padicValNat.mul (pow_pos (by norm_num : 0 < 2) _).ne' (prod_pos N).ne',
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hBodd] at key
    exact key
  have hcontr : e ≤ padicValNat 2 (a N) :=
    (padicValNat_dvd_iff_le (a_pos N hNne).ne').mp hdvd
  rw [hF] at e1
  omega

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
  intro hdvd
  -- No odd prime factor of `n` divides `a (n-1)`.
  have noOdd : ∀ p, p.Prime → p ≠ 2 → p ∣ n → ¬ p ∣ a (n - 1) := by
    intro p hp hp2 hpn hpa
    have hps : p ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans hpn hdvd
    have hd2 : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hpa).mp hps
    have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow hd2
    have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2'
    have hge2 : 2 ≤ p := hp.two_le
    omega
  -- Step 1: `n` is prime.
  have hnp : n.Prime := by
    by_contra hnp
    by_cases hodd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ n
    · obtain ⟨p, hp, hp2, hpn⟩ := hodd
      have hpltn : p < n := by
        rcases Nat.lt_or_ge p n with h | h
        · exact h
        · have hle : p ≤ n := Nat.le_of_dvd (by omega) hpn
          have : p = n := by omega
          exact absurd (this ▸ hp) hnp
      have hc : 2 ≤ n / p := by
        rcases Nat.lt_or_ge (n / p) 2 with h | h
        · exfalso
          have h1 : p * (n / p) = n := Nat.mul_div_cancel' hpn
          interval_cases (n / p) <;> omega
        · exact h
      have hkey : p ∣ a (p * (n / p) - 1) := key_p_dvd_a p (n / p) hp hp2 hc
      rw [Nat.mul_div_cancel' hpn] at hkey
      exact noOdd p hp hp2 hpn hkey
    · -- `n` is a power of two
      have hno : ∀ q, q.Prime → q ∣ n → q = 2 := by
        intro q hq hqn
        by_contra hq2
        exact hodd ⟨q, hq, hq2, hqn⟩
      set e := n.factorization 2 with he
      have hsplit : 2 ^ e * ordCompl[2] n = n := Nat.ordProj_mul_ordCompl_eq_self n 2
      have hm1 : ordCompl[2] n = 1 := by
        by_contra hm
        obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm
        have hqn : q ∣ n := dvd_trans hqm (Nat.ordCompl_dvd n 2)
        have hq2 : q = 2 := hno q hq hqn
        rw [hq2] at hqm
        exact Nat.not_dvd_ordCompl Nat.prime_two (by omega) hqm
      have hne : n = 2 ^ e := by rw [← hsplit, hm1, mul_one]
      have he2 : 2 ≤ e := by
        rcases Nat.lt_or_ge e 2 with h | h
        · exfalso; interval_cases e <;> simp only [pow_zero, pow_one] at hne <;> omega
        · exact h
      have hge : e ≤ n - 2 := by
        rw [hne]
        have h1 : e - 1 < 2 ^ (e - 1) := Nat.lt_two_pow_self
        have h2 : 2 * 2 ^ (e - 1) = 2 ^ e := by
          rw [← pow_succ']
          congr 1
          omega
        omega
      have hn2 : (2 : ℕ) ^ e ∣ 2 ^ (n - 2) := pow_dvd_pow 2 hge
      have hsum : 2 ^ e ∣ a (n - 1) := by
        have hps : (2:ℕ) ^ e ∣ a (n - 1) + 2 ^ (n - 2) := hne ▸ hdvd
        have hsub := Nat.dvd_sub hps hn2
        rwa [Nat.add_sub_cancel] at hsub
      rw [hne] at hsum
      exact pow2_not_dvd_a e he2 hsum
  -- Step 2: 2 is a primitive root mod n.
  refine ⟨hnp, ?_⟩
  haveI : Fact n.Prime := ⟨hnp⟩
  rw [Nat.totient_prime hnp, IsPrimitiveRoot.iff_orderOf]
  have h2ne : (2 : ZMod n) ≠ 0 := by
    have h0 : ((2:ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    simpa using h0
  have hferm : (2 : ZMod n) ^ (n - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hfin : IsOfFinOrder (2 : ZMod n) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n - 1, by omega, hferm⟩
  have hpos : 0 < orderOf (2 : ZMod n) := hfin.orderOf_pos
  have hdvd_ord : orderOf (2 : ZMod n) ∣ (n - 1) := orderOf_dvd_of_pow_eq_one hferm
  by_contra hne
  set d := orderOf (2 : ZMod n) with hdo
  have hdlt : d < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd_ord) hne
  have hpow : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
  have hnd : n ∣ 2 ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h1 : (1:ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1]
    rw [hpow, sub_self]
  have hcontr := prime_factor_dvd_a n d hnp hpos hdlt hnd
  exact noOdd n hnp (by omega) (dvd_refl n) hcontr






