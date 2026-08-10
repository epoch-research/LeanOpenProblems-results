import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

namespace A091669Work

/-- F3: for `P ≥ 2`, `(m-1)/(P-1) ≥ m/P`. -/
lemma floor_lemma (m P : ℕ) (hP : 2 ≤ P) : m / P ≤ (m - 1) / (P - 1) := by
  have hP1 : 0 < P - 1 := by omega
  set q := m / P with hq
  have hqP : q * P ≤ m := Nat.div_mul_le_self m P
  have e1 : q * (P - 1) = q * P - q := by rw [Nat.mul_sub_one]
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · rw [hq0]; simp
  · apply (Nat.le_div_iff_mul_le hP1).2
    omega

/-- `M ∣ 2^k - 1 ↔ orderOf (2 : ZMod M) ∣ k`. -/
lemma dvd_pow_sub_one_iff (M k : ℕ) [NeZero M] :
    M ∣ 2 ^ k - 1 ↔ orderOf (2 : ZMod M) ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one]
  rw [← ZMod.natCast_eq_zero_iff (2 ^ k - 1) M]
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.cast_sub h1]
  push_cast
  rw [sub_eq_zero]

/-- `2` is coprime to `p^i` for odd prime `p`. -/
lemma coprime_two_pp (p i : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    Nat.Coprime 2 (p ^ i) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_primes Nat.prime_two hp]
  exact fun h => hodd h.symm

/-- The order of `2` mod `p^i` divides `totient (p^i)`. -/
lemma order_dvd_totient (M : ℕ) (hM : 1 ≤ M) (hcop : Nat.Coprime 2 M) :
    orderOf (2 : ZMod M) ∣ M.totient := by
  apply orderOf_dvd_of_pow_eq_one
  have h := Nat.ModEq.pow_totient hcop
  have : ((2 ^ M.totient : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  push_cast at this
  exact this

lemma order_pos (M : ℕ) (hM : 1 ≤ M) (hcop : Nat.Coprime 2 M) :
    0 < orderOf (2 : ZMod M) :=
  Nat.pos_of_dvd_of_pos (order_dvd_totient M hM hcop) (Nat.totient_pos.2 hM)

lemma order_le (M : ℕ) (hM : 2 ≤ M) (hcop : Nat.Coprime 2 M) :
    orderOf (2 : ZMod M) ≤ M - 1 := by
  have h1 : orderOf (2 : ZMod M) ≤ M.totient :=
    Nat.le_of_dvd (Nat.totient_pos.2 (by omega)) (order_dvd_totient M (by omega) hcop)
  have h2 : M.totient < M := Nat.totient_lt M (by omega)
  omega

lemma pp_ge_two (p i : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hi : 1 ≤ i) : 2 ≤ p ^ i := by
  have hp2 := hp.two_le
  have : 3 ≤ p := by omega
  calc 2 ≤ p := by omega
  _ = p ^ 1 := (pow_one p).symm
  _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi

/-- The count of `k ∈ [1,B]` with `p^i ∣ 2^k-1` equals `B / orderOf(2)`. -/
lemma count_eq (p i B : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hi : 1 ≤ i) :
    #{k ∈ Finset.Ico 1 (B + 1) | p ^ i ∣ 2 ^ k - 1} = B / orderOf (2 : ZMod (p ^ i)) := by
  have hM2 : 2 ≤ p ^ i := pp_ge_two p i hp hodd hi
  haveI : NeZero (p ^ i) := ⟨by omega⟩
  have hcop : Nat.Coprime 2 (p ^ i) := coprime_two_pp p i hp hodd
  have hfilter : {k ∈ Finset.Ico 1 (B + 1) | p ^ i ∣ 2 ^ k - 1}
      = {k ∈ Finset.Ico 1 (B + 1) | orderOf (2 : ZMod (p ^ i)) ∣ k} := by
    apply Finset.filter_congr
    intro k _
    rw [dvd_pow_sub_one_iff (p ^ i) k]
  rw [hfilter]
  have hset : Finset.Ico 1 (B + 1) = Finset.Ioc 0 B := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div B _]

/-- Key count bound: at least `(B+1)/p^i` values `k ∈ [1,B]` have `p^i ∣ 2^k - 1`. -/
lemma count_ge (p i B : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hi : 1 ≤ i) :
    (B + 1) / p ^ i ≤ #{k ∈ Finset.Ico 1 (B + 1) | p ^ i ∣ 2 ^ k - 1} := by
  have hM2 : 2 ≤ p ^ i := pp_ge_two p i hp hodd hi
  have hcop : Nat.Coprime 2 (p ^ i) := coprime_two_pp p i hp hodd
  have hdpos : 0 < orderOf (2 : ZMod (p ^ i)) := order_pos _ (by omega) hcop
  have hdle : orderOf (2 : ZMod (p ^ i)) ≤ p ^ i - 1 := order_le _ hM2 hcop
  rw [count_eq p i B hp hodd hi]
  calc (B + 1) / p ^ i ≤ B / (p ^ i - 1) := by
        have := floor_lemma (B + 1) (p ^ i) hM2
        simpa using this
    _ ≤ B / _ := Nat.div_le_div_left hdle hdpos

/-- Strict count bound at `i = 1` used for composite `n = p*t`. -/
lemma count_strict (p t : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (ht : 2 ≤ t) :
    (p * t - 1) / p + 1 ≤ #{k ∈ Finset.Ico 1 (p * t - 1) | p ∣ 2 ^ k - 1} := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpt0 : 6 ≤ p * t := by
    calc 6 = 3 * 2 := by norm_num
    _ ≤ p * t := Nat.mul_le_mul (by omega) ht
  -- write Ico 1 (p*t-1) as Ico 1 ((p*t-2)+1)
  have hB : p * t - 1 = (p * t - 2) + 1 := by omega
  have hcount : #{k ∈ Finset.Ico 1 (p * t - 1) | p ∣ 2 ^ k - 1}
      = (p * t - 2) / orderOf (2 : ZMod (p ^ 1)) := by
    rw [hB]
    have := count_eq p 1 (p * t - 2) hp hodd (le_refl 1)
    simpa [pow_one] using this
  rw [hcount, pow_one]
  have hcop : Nat.Coprime 2 p := by
    have := coprime_two_pp p 1 hp hodd; simpa [pow_one] using this
  have hdpos : 0 < orderOf (2 : ZMod p) := by
    have := order_pos p (by omega) hcop; simpa using this
  have hdle : orderOf (2 : ZMod p) ≤ p - 1 := by
    have := order_le p (by omega) hcop; simpa using this
  have hple : p ≤ p * t := Nat.le_mul_of_pos_right p (by omega)
  have hpt : p * (t - 1) + p = p * t := by rw [Nat.mul_sub_one]; omega
  -- (p*t-1)/p = t - 1
  have hdiv1 : (p * t - 1) / p = t - 1 := by
    have key : p * t - 1 = (p - 1) + p * (t - 1) := by omega
    rw [key, Nat.add_mul_div_left _ _ (show 0 < p by omega), Nat.div_eq_of_lt (by omega)]
    omega
  -- t ≤ (p*t-2)/(p-1)
  have hstep1 : t ≤ (p * t - 2) / (p - 1) := by
    apply (Nat.le_div_iff_mul_le (show 0 < p - 1 by omega)).2
    have : t * (p - 1) = p * t - t := by rw [Nat.mul_sub_one]; ring_nf
    omega
  have hstep2 : (p * t - 2) / (p - 1) ≤ (p * t - 2) / orderOf (2 : ZMod p) :=
    Nat.div_le_div_left hdle hdpos
  rw [hdiv1]
  omega

/-- Fubini representation of the `p`-adic valuation of the product. -/
lemma prod_factorization_eq (p M c : ℕ) (hp : p.Prime)
    (hc : ∀ k ∈ Finset.Ico 1 M, 2 ^ k - 1 < p ^ c) :
    (∏ k ∈ Finset.Ico 1 M, (2 ^ k - 1)).factorization p
      = ∑ i ∈ Finset.Ico 1 c, #{k ∈ Finset.Ico 1 M | p ^ i ∣ 2 ^ k - 1} := by
  have hf : ∀ k ∈ Finset.Ico 1 M, (2 ^ k - 1) ≠ 0 := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
    omega
  rw [Nat.factorization_prod hf]
  simp only [Finsupp.finset_sum_apply]
  -- LHS = ∑ k, (2^k-1).factorization p
  have hstep : ∀ k ∈ Finset.Ico 1 M, (2 ^ k - 1).factorization p
      = #{i ∈ Finset.Ico 1 c | p ^ i ∣ 2 ^ k - 1} := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hpos : 0 < 2 ^ k - 1 := by
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
      omega
    exact Nat.factorization_eq_card_pow_dvd_of_lt hp hpos (hc k (by simp [Finset.mem_Ico]; omega))
  rw [Finset.sum_congr rfl hstep]
  -- now swap the two sums
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- For odd prime `p` and `M ≥ 1`, `v_p(M!) ≤ v_p(∏_{k<M}(2^k-1))`. -/
lemma factorial_factorization_le (p M : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hM : 1 ≤ M) :
    (M ! ).factorization p ≤ (∏ k ∈ Finset.Ico 1 M, (2 ^ k - 1)).factorization p := by
  have hlog : Nat.log p M < M := Nat.log_lt_self p (by omega)
  have hbound : ∀ k ∈ Finset.Ico 1 M, 2 ^ k - 1 < p ^ M := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have h1 : 2 ^ k ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (le_of_lt hk.2)
    have h2 : 2 ^ M ≤ p ^ M := Nat.pow_le_pow_left hp.two_le M
    have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  rw [Nat.factorization_factorial hp hlog, prod_factorization_eq p M M hp hbound]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Finset.mem_Ico] at hi
  have hge := count_ge p i (M - 1) hp hodd hi.1
  rwa [Nat.sub_add_cancel hM] at hge

/-- Integrality of the numerator: `M ! ∣ 2^(M-1) * ∏_{k<M}(2^k-1)`. -/
lemma factorial_dvd_numerator (M : ℕ) (hM : 1 ≤ M) :
    M ! ∣ 2 ^ (M - 1) * ∏ k ∈ Finset.Ico 1 M, (2 ^ k - 1) := by
  have hprodpos : 0 < ∏ k ∈ Finset.Ico 1 M, (2 ^ k - 1) := by
    apply Finset.prod_pos
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
    omega
  set N := 2 ^ (M - 1) * ∏ k ∈ Finset.Ico 1 M, (2 ^ k - 1) with hN
  have hNpos : 0 < N := by positivity
  rw [← Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero M) (by omega)]
  rw [Finsupp.le_iff]
  intro p hp_mem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  -- factorization of N at p
  have hNfact : N.factorization p
      = (2 ^ (M - 1)).factorization p + (∏ k ∈ Finset.Ico 1 M, (2 ^ k - 1)).factorization p := by
    rw [hN, Nat.factorization_mul (by positivity) (by omega)]
    rfl
  rcases eq_or_ne p 2 with hp2 | hp2
  · -- p = 2
    subst hp2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfac : (M !).factorization 2 < M := by
      rw [Nat.factorization_def _ Nat.prime_two]
      exact padicValNat_factorial_lt_of_ne_zero 2 (by omega)
    have h2pow : (2 ^ (M - 1)).factorization 2 = M - 1 :=
      Nat.factorization_pow_self Nat.prime_two
    rw [hNfact, h2pow]
    omega
  · -- p odd
    have hzero : (2 ^ (M - 1)).factorization p = 0 := by
      rw [Nat.factorization_pow, Nat.Prime.factorization Nat.prime_two]
      simp [Finsupp.single_apply, Ne.symm hp2]
    rw [hNfact, hzero, zero_add]
    exact factorial_factorization_le p M hp hp2 hM

noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_pred : ℕ := n.pred
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)
    let denominator : ℕ := n.factorial
    numerator / denominator

/-- For `n ≥ 1`, `a n = numerator / n!`. -/
lemma a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = (2 ^ (n - 1) * ∏ k ∈ Finset.Ico 1 n, (2 ^ k - 1)) / n ! := by
  rw [a]
  rw [dif_neg (by omega)]
  simp only [Nat.pred_eq_sub_one]

/-- Key identity: `a n * n! = 2^(n-1) * ∏_{k<n}(2^k-1)`. -/
lemma a_mul_factorial (n : ℕ) (hn : 1 ≤ n) :
    a n * n ! = 2 ^ (n - 1) * ∏ k ∈ Finset.Ico 1 n, (2 ^ k - 1) := by
  rw [a_eq n hn]
  exact Nat.div_mul_cancel (factorial_dvd_numerator n hn)

/-- Sum inequality with one strict term. -/
lemma sum_strict {s : Finset ℕ} {f g : ℕ → ℕ} (j : ℕ) (hj : j ∈ s)
    (hle : ∀ i ∈ s, g i ≤ f i) (hstrict : g j + 1 ≤ f j) :
    (∑ i ∈ s, g i) + 1 ≤ ∑ i ∈ s, f i := by
  rw [← Finset.add_sum_erase s f hj, ← Finset.add_sum_erase s g hj]
  have : ∑ i ∈ s.erase j, g i ≤ ∑ i ∈ s.erase j, f i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hle i (Finset.mem_of_mem_erase hi)
  omega

/-- Strict composite valuation bound: for `p ∣ n`, `p` odd, `n ≥ 2p`,
`v_p((n-1)!) + 1 ≤ v_p(∏_{k<n-1}(2^k-1))`. -/
lemma comp_factorization_strict (n p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hpn : p ∣ n) (hn : 2 * p ≤ n) :
    ((n - 1)! ).factorization p + 1
      ≤ (∏ k ∈ Finset.Ico 1 (n - 1), (2 ^ k - 1)).factorization p := by
  obtain ⟨t, rfl⟩ := hpn
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have ht : 2 ≤ t := by
    by_contra h
    have : t ≤ 1 := by omega
    nlinarith
  have hpt6 : 6 ≤ p * t := by
    calc 6 = 3 * 2 := by norm_num
    _ ≤ p * t := Nat.mul_le_mul (by omega) ht
  -- Legendre and prod representation with c = p*t - 1
  set M := p * t - 1 with hM
  have hMpos : 1 ≤ M := by simp only [hM]; omega
  have hlog : Nat.log p M < M := Nat.log_lt_self p (by omega)
  have hbound : ∀ k ∈ Finset.Ico 1 M, 2 ^ k - 1 < p ^ M := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have h1 : 2 ^ k ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (le_of_lt hk.2)
    have h2 : 2 ^ M ≤ p ^ M := Nat.pow_le_pow_left hp.two_le M
    have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  rw [Nat.factorization_factorial hp hlog, prod_factorization_eq p M M hp hbound]
  -- apply sum_strict with j = 1
  apply sum_strict 1
  · simp only [Finset.mem_Ico]; omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    have hge := count_ge p i (M - 1) hp hodd hi.1
    rwa [Nat.sub_add_cancel hMpos] at hge
  · -- strict at i = 1
    have hcs := count_strict p t hp hodd ht
    rw [pow_one]
    simpa [hM] using hcs

lemma a_pos (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  have h := a_mul_factorial n hn
  have hpos : 0 < 2 ^ (n - 1) * ∏ k ∈ Finset.Ico 1 n, (2 ^ k - 1) := by
    apply Nat.mul_pos (pow_pos (by norm_num) _)
    apply Finset.prod_pos
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
    omega
  rw [← h] at hpos
  exact Nat.pos_of_mul_pos_left (by rwa [Nat.mul_comm] at hpos)

/-- For composite `n` with odd prime factor `p` (and `n ≥ 2p`), `p ∣ a (n-1)`. -/
lemma p_dvd_a (n p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hpn : p ∣ n) (hn : 2 * p ≤ n) :
    p ∣ a (n - 1) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hn2 : 2 ≤ n := by omega
  set m := n - 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmeq : m - 1 = n - 2 := by omega
  have key := a_mul_factorial m hm1
  -- factorization at p of both sides
  have hane : a m ≠ 0 := (a_pos m hm1).ne'
  have hfacne : m ! ≠ 0 := Nat.factorial_ne_zero m
  have hprodpos : 0 < ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1) := by
    apply Finset.prod_pos
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
    omega
  have hzero : (2 ^ (m - 1)).factorization p = 0 := by
    rw [Nat.factorization_pow, Nat.Prime.factorization Nat.prime_two]
    simp [Ne.symm hodd]
  -- take factorization p of key
  have hL : (a m * m !).factorization p = (a m).factorization p + (m !).factorization p :=
    Nat.factorization_mul hane hfacne ▸ rfl
  have hR : (2 ^ (m - 1) * ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)).factorization p
      = (∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)).factorization p := by
    rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply, hzero, zero_add]
  rw [key] at hL
  rw [hR] at hL
  -- comp strict bound
  have hstrict : (m !).factorization p + 1
      ≤ (∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)).factorization p := by
    have := comp_factorization_strict n p hp hodd hpn hn
    rwa [← hmdef] at this
  -- conclude a m factorization ≥ 1
  apply Nat.dvd_of_factorization_pos
  omega

/-- The binary digit sum of `2^k - 1` is `k`. -/
lemma digitsum_two_pow_sub_one (k : ℕ) : (Nat.digits 2 (2 ^ k - 1)).sum = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    set x := 2 ^ k with hx
    have hx1 : 1 ≤ x := Nat.one_le_two_pow
    have hNpos : 0 < 2 ^ (k + 1) - 1 := by omega
    rw [Nat.digits_def' (by norm_num : 1 < 2) hNpos]
    have hmod : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hdiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
    rw [hmod, hdiv]
    simp only [List.sum_cons]
    rw [ih]; omega

/-- For `n = 2^k` with `k ≥ 2`, `n` does not divide `a(n-1) + 2^(n-2)`. -/
lemma pow2_case (k : ℕ) (hk : 2 ≤ k) :
    ¬ ((2 ^ k) ∣ a (2 ^ k - 1) + 2 ^ (2 ^ k - 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbig : k + 2 ≤ 2 ^ k := by
    have h1 : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]; ring
    omega
  set m := 2 ^ k - 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmgek : k ≤ m := by omega
  have hmk : m - 1 = 2 ^ k - 2 := by omega
  have hprodne : (∏ j ∈ Finset.Ico 1 m, (2 ^ j - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj.1
    omega
  -- valuation of m!
  have hvfac : (m ! ).factorization 2 = m - k := by
    have h := sub_one_mul_padicValNat_factorial (p := 2) m
    rw [Nat.factorization_def _ Nat.prime_two]
    simp only [Nat.sub_self, Nat.reduceSub, one_mul] at h
    rw [hmdef, digitsum_two_pow_sub_one] at h
    omega
  -- valuation of numerator 2^(m-1) * ∏
  have hprodfact : (∏ j ∈ Finset.Ico 1 m, (2 ^ j - 1)).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    rw [Prime.dvd_finset_prod_iff Nat.prime_two.prime _] at hdvd
    obtain ⟨j, hj, hjdvd⟩ := hdvd
    simp only [Finset.mem_Ico] at hj
    have h2j : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj.1
    omega
  have hvnum : (2 ^ (m - 1) * ∏ j ∈ Finset.Ico 1 m, (2 ^ j - 1)).factorization 2 = m - 1 := by
    rw [Nat.factorization_mul (by positivity) hprodne, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, hprodfact, add_zero]
  -- combine via a_mul_factorial
  have hane : a m ≠ 0 := (a_pos m hm1).ne'
  have key := a_mul_factorial m hm1
  have hmul : (a m).factorization 2 + (m ! ).factorization 2
      = (2 ^ (m - 1) * ∏ j ∈ Finset.Ico 1 m, (2 ^ j - 1)).factorization 2 := by
    rw [← key, Nat.factorization_mul hane (Nat.factorial_ne_zero m), Finsupp.add_apply]
  rw [hvnum, hvfac] at hmul
  have hva : (a m).factorization 2 = k - 1 := by omega
  -- 2^k ∤ a m
  have hnotdvd : ¬ (2 ^ k ∣ a m) := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hane, hva]
    omega
  -- conclude
  intro hdvd
  apply hnotdvd
  have hpow : 2 ^ k ∣ 2 ^ (2 ^ k - 2) := pow_dvd_pow 2 (by omega)
  have hdvd' : 2 ^ k ∣ 2 ^ (2 ^ k - 2) + a m := by rwa [Nat.add_comm] at hdvd
  exact (Nat.dvd_add_right hpow).mp hdvd'

/-- Odd prime factor case: if odd prime `p ∣ n` and `n ≥ 2p` then `n ∤ a(n-1)+2^(n-2)`. -/
lemma odd_factor_not_dvd (n p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hpn : p ∣ n)
    (hn2p : 2 * p ≤ n) : ¬ (n ∣ a (n - 1) + 2 ^ (n - 2)) := by
  intro hS
  have hpa : p ∣ a (n - 1) := p_dvd_a n p hp hodd hpn hn2p
  have hpS : p ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans hpn hS
  have hp2pow : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right hpa).mp hpS
  have hp2 : p ∣ 2 := hp.prime.dvd_of_dvd_pow hp2pow
  have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
  have := hp.two_le
  omega

/-- Composite `n > 2` never divides `a(n-1)+2^(n-2)`. -/
lemma not_prime_not_dvd (n : ℕ) (hn : 2 < n) (hnp : ¬ n.Prime) :
    ¬ (n ∣ a (n - 1) + 2 ^ (n - 2)) := by
  obtain ⟨k, m, hm_odd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hnm
    have hk2 : 2 ≤ k := by
      by_contra h
      interval_cases k <;> omega
    rw [hnm]
    exact pow2_case k hk2
  · have hp : (m.minFac).Prime := Nat.minFac_prime hm1
    have hpm : m.minFac ∣ m := Nat.minFac_dvd m
    have hpn : m.minFac ∣ n := by rw [hnm]; exact hpm.mul_left _
    have hodd : m.minFac ≠ 2 := by
      intro h
      rw [h] at hpm
      rcases hm_odd with ⟨t, ht⟩
      omega
    -- 2 * minFac ≤ n
    obtain ⟨c, hc⟩ := id hpn
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc; omega
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [mul_one] at hc
      rw [hc] at hnp
      exact hnp hp
    have hn2p : 2 * m.minFac ≤ n := by
      rw [hc]
      have h2c : 2 ≤ c := by omega
      calc 2 * m.minFac = m.minFac * 2 := by ring
      _ ≤ m.minFac * c := Nat.mul_le_mul_left _ h2c
    exact odd_factor_not_dvd n m.minFac hp hodd hpn hn2p

/-- Cast of the product to `ZMod n`. -/
lemma prod_cast (n M : ℕ) :
    ((∏ k ∈ Finset.Ico 1 M, (2 ^ k - 1) : ℕ) : ZMod n)
      = ∏ k ∈ Finset.Ico 1 M, ((2 : ZMod n) ^ k - 1) := by
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.cast_sub h1]
  push_cast
  ring

/-- Prime case: `n` prime and `n ∣ a(n-1)+2^(n-2)` implies `2` is a primitive root. -/
lemma prime_case (n : ℕ) (hn : 2 < n) (hp : n.Prime)
    (hS : n ∣ a (n - 1) + 2 ^ (n - 2)) :
    IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  haveI : Fact n.Prime := ⟨hp⟩
  have hn1 : 1 ≤ n - 1 := by omega
  -- The key identity cast into ZMod n.
  have key := a_mul_factorial (n - 1) hn1
  have hsub : (n - 1) - 1 = n - 2 := by omega
  rw [hsub] at key
  -- cast key to ZMod n
  have keyZ : ((a (n - 1) : ℕ) : ZMod n) * ((n - 1)! : ZMod n)
      = (2 : ZMod n) ^ (n - 2) * ∏ k ∈ Finset.Ico 1 (n - 1), ((2 : ZMod n) ^ k - 1) := by
    have hc := congrArg (Nat.cast : ℕ → ZMod n) key
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, prod_cast] at hc
    push_cast at hc
    exact hc
  -- Wilson
  have hWilson : ((n - 1)! : ZMod n) = -1 := ZMod.wilsons_lemma n
  -- hS gives a(n-1) ≡ -2^(n-2)
  have hScast : ((a (n - 1) : ℕ) : ZMod n) = -(2 : ZMod n) ^ (n - 2) := by
    have h0 : ((a (n - 1) + 2 ^ (n - 2) : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hS
    push_cast at h0
    linear_combination h0
  -- 2 ≠ 0 in ZMod n
  have h2ne : (2 : ZMod n) ≠ 0 := by
    intro h
    have : (n : ℕ) ∣ 2 := by
      have := (ZMod.natCast_eq_zero_iff 2 n).1 (by exact_mod_cast h)
      exact this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h2powne : (2 : ZMod n) ^ (n - 2) ≠ 0 := pow_ne_zero _ h2ne
  -- derive product = 1
  rw [hWilson, hScast] at keyZ
  have hProd1 : ∏ k ∈ Finset.Ico 1 (n - 1), ((2 : ZMod n) ^ k - 1) = 1 := by
    have hcalc : (2 : ZMod n) ^ (n - 2) * 1
        = (2 : ZMod n) ^ (n - 2) * ∏ k ∈ Finset.Ico 1 (n - 1), ((2 : ZMod n) ^ k - 1) := by
      rw [mul_one]; linear_combination keyZ
    exact (mul_left_cancel₀ h2powne hcalc).symm
  -- orderOf divides n-1
  have hferm : (2 : ZMod n) ^ (n - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hd_dvd : orderOf (2 : ZMod n) ∣ n - 1 := orderOf_dvd_of_pow_eq_one hferm
  have hd_pos : 0 < orderOf (2 : ZMod n) := by
    apply orderOf_pos_iff.2
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n - 1, by omega, hferm⟩
  -- conclude orderOf = totient n
  rw [IsPrimitiveRoot.iff_orderOf, Nat.totient_prime hp]
  -- show orderOf = n - 1
  have hd_le : orderOf (2 : ZMod n) ≤ n - 1 := Nat.le_of_dvd (by omega) hd_dvd
  by_contra hne
  have hd_lt : orderOf (2 : ZMod n) < n - 1 := by omega
  -- then the factor at k = orderOf is zero
  have hmem : orderOf (2 : ZMod n) ∈ Finset.Ico 1 (n - 1) := by
    simp only [Finset.mem_Ico]
    exact ⟨hd_pos, hd_lt⟩
  have hzero : (2 : ZMod n) ^ orderOf (2 : ZMod n) - 1 = 0 := by
    rw [pow_orderOf_eq_one]; ring
  have hprodzero : ∏ k ∈ Finset.Ico 1 (n - 1), ((2 : ZMod n) ^ k - 1) = 0 :=
    Finset.prod_eq_zero hmem hzero
  rw [hProd1] at hprodzero
  exact one_ne_zero hprodzero

theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
    n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdvd
  have hp : n.Prime := by
    by_contra hnp
    exact not_prime_not_dvd n hn hnp hdvd
  exact ⟨hp, prime_case n hn hp hdvd⟩
