import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A265709: $a(n) = \mathrm{numerator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
$\sigma(d)$ is the sum of the divisors of $d$, $\sigma(d) = \sum_{k|d} k$.
-/
def A265709 (n : ℕ) : ℕ :=
  -- The sum \sum_{d|n} 1/\sigma(d), calculated in the rational numbers ℚ.
  let sum_of_reciprocals : ℚ :=
    n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)

  -- The numerator of the minimal representation of the rational number, converted from ℤ to ℕ.
  sum_of_reciprocals.num.toNat

/-- Reciprocal of `σ` as an arithmetic function. -/
def invSigma : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else (1 : ℚ) / (sigma 1 n : ℚ), by simp⟩

lemma invSigma_apply {n : ℕ} (hn : n ≠ 0) :
    invSigma n = (1 : ℚ) / (sigma 1 n : ℚ) :=
  dif_neg hn

lemma isMultiplicative_invSigma : IsMultiplicative invSigma := by
  refine ⟨?_, ?_⟩
  · simp [invSigma, sigma_one]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
    have hσ : (sigma 1 (m * n) : ℚ) = (sigma 1 m : ℚ) * (sigma 1 n : ℚ) := by
      rw [isMultiplicative_sigma.map_mul_of_coprime hmn]
      push_cast
      rfl
    rw [invSigma_apply hmn0, invSigma_apply hm, invSigma_apply hn, hσ]
    have hmσ : (sigma 1 m : ℚ) ≠ 0 := by exact_mod_cast (sigma_pos 1 m hm).ne'
    have hnσ : (sigma 1 n : ℚ) ≠ 0 := by exact_mod_cast (sigma_pos 1 n hn).ne'
    field_simp

/-- The sum `∑_{d∣n} 1/σ(d)`. -/
def fSum : ArithmeticFunction ℚ := invSigma * (zeta : ArithmeticFunction ℚ)

lemma fSum_apply (n : ℕ) :
    fSum n = n.divisors.sum fun d => (1 : ℚ) / (sigma 1 d : ℚ) := by
  unfold fSum
  rw [coe_mul_zeta_apply]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (pos_of_mem_divisors hd).ne'
  rw [invSigma_apply hd0]

lemma fSum_pos {n : ℕ} (hn : n ≠ 0) : 0 < fSum n := by
  rw [fSum_apply]
  refine Finset.sum_pos ?_ ⟨1, one_mem_divisors.mpr hn⟩
  intro d hd
  have hd0 : d ≠ 0 := (pos_of_mem_divisors hd).ne'
  have : (0 : ℚ) < (sigma 1 d : ℚ) := by exact_mod_cast sigma_pos 1 d hd0
  positivity

lemma fSum_ne_zero {n : ℕ} (hn : n ≠ 0) : fSum n ≠ 0 := (fSum_pos hn).ne'

lemma fSum_one : fSum 1 = 1 := by
  simp [fSum_apply, divisors_one, sigma_one]

lemma isMultiplicative_fSum : IsMultiplicative fSum :=
  isMultiplicative_invSigma.mul (isMultiplicative_zeta.natCast)

lemma fSum_mul {m n : ℕ} (hmn : Nat.Coprime m n) : fSum (m * n) = fSum m * fSum n :=
  isMultiplicative_fSum.map_mul_of_coprime hmn

lemma sigma_eq_geom {p k : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ k) = ∑ j ∈ range (k + 1), p ^ j :=
  sigma_one_apply_prime_pow hp

lemma sigma_mul_pred {p k : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ k) * (p - 1) = p ^ (k + 1) - 1 := by
  rw [sigma_eq_geom hp]
  exact geom_sum_mul_of_one_le hp.one_le (k + 1)

lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_eq_geom hp, sum_range_succ, sum_range_one, pow_zero, pow_one]
  ac_rfl

lemma fSum_prime_pow {p a : ℕ} (hp : p.Prime) :
    fSum (p ^ a) = ∑ k ∈ range (a + 1), (1 : ℚ) / (sigma 1 (p ^ k) : ℚ) := by
  rw [fSum_apply, divisors_prime_pow hp, sum_map]
  simp

lemma fSum_prime {p : ℕ} (hp : p.Prime) :
    fSum p = ((p : ℚ) + 2) / ((p : ℚ) + 1) := by
  have h := fSum_prime_pow (p := p) (a := 1) hp
  rw [sum_range_succ, sum_range_one, pow_zero, pow_one, sigma_one, sigma_prime hp] at h
  have hp1 : (p : ℚ) + 1 ≠ 0 := by
    have : (0 : ℚ) < (p : ℚ) + 1 := by positivity
    exact this.ne'
  rw [h]
  field_simp
  norm_cast
  ring

lemma fSum_two : fSum 2 = (4 : ℚ) / 3 := by
  rw [fSum_prime Nat.prime_two]
  norm_num

lemma fSum_three : fSum 3 = (5 : ℚ) / 4 := by
  rw [fSum_prime Nat.prime_three]
  norm_num

/-! ## 2-adic valuations of `σ` and `fSum` -/

lemma not_two_dvd_of_odd {n : ℕ} (h : Odd n) : ¬ 2 ∣ n := by
  rw [← even_iff_two_dvd]
  exact Nat.not_even_iff_odd.mpr h

lemma padicValNat_odd_eq_zero {n : ℕ} (h : Odd n) : padicValNat 2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (not_two_dvd_of_odd h)

/-- For odd `p` and odd `n`, `∑_{i<n} p^i` is odd. -/
lemma odd_geom_sum {p n : ℕ} (hp : Odd p) (hn : Odd n) :
    Odd (∑ i ∈ range n, p ^ i) := by
  have hmod : (∑ i ∈ range n, p ^ i) % 2 = n % 2 := by
    rw [Finset.sum_nat_mod]
    have hterm : ∀ i ∈ range n, p ^ i % 2 = 1 := fun i _ =>
      Nat.odd_iff.mp (hp.pow)
    refine Eq.trans (congrArg (· % 2) (sum_congr rfl fun i hi => hterm i hi)) ?_
    simp
  rwa [Nat.odd_iff, hmod, ← Nat.odd_iff]

lemma padicValNat_two_pow_sub_one_of_odd {p n : ℕ}
    (hp : Odd p) (h1p : 1 < p) (hn : Odd n) (hn0 : n ≠ 0) :
    padicValNat 2 (p ^ n - 1) = padicValNat 2 (p - 1) := by
  have hmul : (∑ i ∈ range n, p ^ i) * (p - 1) = p ^ n - 1 :=
    geom_sum_mul_of_one_le (le_of_lt h1p) n
  have hgeom_pos : 0 < ∑ i ∈ range n, p ^ i :=
    Finset.sum_pos (fun i _ => pow_pos (lt_trans Nat.zero_lt_one h1p) i)
      (nonempty_range_iff.mpr hn0)
  have hpred_pos : 0 < p - 1 := tsub_pos_of_lt h1p
  have hoddg : Odd (∑ i ∈ range n, p ^ i) := odd_geom_sum hp hn
  have := padicValNat.mul (p := 2) (a := ∑ i ∈ range n, p ^ i) (b := p - 1)
    hgeom_pos.ne' hpred_pos.ne'
  rw [hmul] at this
  rw [this, padicValNat_odd_eq_zero hoddg, zero_add]

lemma padicValNat_two_sigma_odd_prime_pow {p k : ℕ}
    (hp : p.Prime) (hodd : Odd p) :
    padicValNat 2 (sigma 1 (p ^ k)) =
      if Even (k + 1) then
        padicValNat 2 (p + 1) + padicValNat 2 (k + 1) - 1
      else 0 := by
  have hp1 : 1 < p := hp.one_lt
  have hp_not2 : ¬ 2 ∣ p := not_two_dvd_of_odd hodd
  have hσpos : sigma 1 (p ^ k) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
  have hpred : p - 1 ≠ 0 := (tsub_pos_of_lt hp1).ne'
  have hmul := sigma_mul_pred (k := k) hp
  have hleft : padicValNat 2 (sigma 1 (p ^ k) * (p - 1)) =
      padicValNat 2 (sigma 1 (p ^ k)) + padicValNat 2 (p - 1) :=
    padicValNat.mul hσpos hpred
  have hboth : padicValNat 2 (sigma 1 (p ^ k)) + padicValNat 2 (p - 1) =
      padicValNat 2 (p ^ (k + 1) - 1) := by
    rw [← hleft, hmul]
  by_cases hEven : Even (k + 1)
  · have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    have hLTE : padicValNat 2 (p ^ (k + 1) - 1) + 1 =
        padicValNat 2 (p + 1) + padicValNat 2 (p - 1) + padicValNat 2 (k + 1) :=
      padicValNat.pow_two_sub_one hp1 hp_not2 hk0 hEven
    have : padicValNat 2 (sigma 1 (p ^ k)) =
        padicValNat 2 (p + 1) + padicValNat 2 (k + 1) - 1 := by omega
    simpa [hEven] using this
  · have hoddn : Odd (k + 1) := Nat.not_even_iff_odd.mp hEven
    have hv : padicValNat 2 (p ^ (k + 1) - 1) = padicValNat 2 (p - 1) :=
      padicValNat_two_pow_sub_one_of_odd hodd hp1 hoddn (Nat.succ_ne_zero k)
    have : padicValNat 2 (sigma 1 (p ^ k)) = 0 := by omega
    simpa [hEven] using this

lemma padicValRat_inv_nat (q n : ℕ) [Fact q.Prime] :
    padicValRat q ((1 : ℚ) / (n : ℚ)) = - (padicValNat q n : ℤ) := by
  rw [one_div, padicValRat.inv, padicValRat.of_nat]

lemma two_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma padicValNat_two_pow (t : ℕ) : padicValNat 2 (2 ^ t) = t := by
  haveI := two_fact
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, padicValNat.mul (pow_ne_zero t two_ne_zero) two_ne_zero, ih, padicValNat_self]

/-- If `1 ≤ m ≤ N` and `m ≠ 2^{log₂ N}`, then `v₂(m) < log₂ N`. -/
lemma padicValNat_two_lt_log {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N)
    (hne : m ≠ 2 ^ Nat.log 2 N) :
    padicValNat 2 m < Nat.log 2 N := by
  haveI := two_fact
  by_contra hge
  have hge' : Nat.log 2 N ≤ padicValNat 2 m := by omega
  have hdiv : 2 ^ Nat.log 2 N ∣ m := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hm.ne']
    exact_mod_cast hge'
  obtain ⟨t, ht⟩ := hdiv
  have ht0 : 0 < t := Nat.pos_of_mul_pos_left (ht ▸ hm)
  have hltN : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by decide) N
  have ht1 : t = 1 := by
    by_contra htne
    have h2t : 2 ≤ t := by omega
    have : 2 ^ (Nat.log 2 N + 1) ≤ m := by
      rw [pow_succ, ht]
      exact Nat.mul_le_mul_left _ h2t
    omega
  exact hne (by rw [ht, ht1, mul_one])

lemma v2_term_odd_prime {p k : ℕ} (hp : p.Prime) (hodd : Odd p) :
    padicValRat 2 ((1 : ℚ) / (sigma 1 (p ^ k) : ℚ)) =
      - (padicValNat 2 (sigma 1 (p ^ k)) : ℤ) := by
  haveI := two_fact
  exact padicValRat_inv_nat 2 _

/-- The 2-valuation of `fSum (p^a)` for an odd prime `p` and `a ≥ 1`. -/
lemma padicValRat_two_fSum_odd_prime_pow {p a : ℕ}
    (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a) :
    padicValRat 2 (fSum (p ^ a)) =
      (1 : ℤ) - padicValNat 2 (p + 1) - Nat.log 2 (a + 1) := by
  haveI := two_fact
  have ha1 : 1 ≤ a + 1 := by omega
  have ha2 : 2 ≤ a + 1 := by omega
  set N := a + 1
  set ℓ := Nat.log 2 N
  set k0 := 2 ^ ℓ - 1
  have hpow_le : 2 ^ ℓ ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hpow_pos : 1 ≤ 2 ^ ℓ := Nat.one_le_pow _ _ (by decide)
  have hk0_le : k0 ≤ a := by
    have : 2 ^ ℓ ≤ a + 1 := hpow_le
    omega
  have hk0_mem : k0 ∈ range (a + 1) := by
    simp [k0]; omega
  -- v2(σ(p^k0)) is maximal and unique
  have hk0_succ : k0 + 1 = 2 ^ ℓ := Nat.sub_add_cancel hpow_pos
  have hℓpos : 1 ≤ ℓ := Nat.log_pos (by decide) ha2
  have hEven0 : Even (k0 + 1) := by
    rw [hk0_succ]
    exact even_pow.mpr ⟨even_two, by omega⟩
  have hv0 : padicValNat 2 (sigma 1 (p ^ k0)) =
      padicValNat 2 (p + 1) + ℓ - 1 := by
    rw [padicValNat_two_sigma_odd_prime_pow hp hodd, if_pos hEven0, hk0_succ,
      padicValNat_two_pow]
  -- For every other k, the valuation of the term is strictly larger
  have hv2p : 1 ≤ padicValNat 2 (p + 1) :=
    one_le_padicValNat_of_dvd (by omega)
      (even_iff_two_dvd.mp (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)))
  have hstrict : ∀ k ∈ range (a + 1), k ≠ k0 →
      padicValRat 2 ((1 : ℚ) / (sigma 1 (p ^ k) : ℚ)) >
        padicValRat 2 ((1 : ℚ) / (sigma 1 (p ^ k0) : ℚ)) := by
    intro k hk hkne
    rw [v2_term_odd_prime hp hodd, v2_term_odd_prime hp hodd]
    rw [gt_iff_lt, neg_lt_neg_iff, Nat.cast_lt]
    have hv0' : padicValNat 2 (sigma 1 (p ^ k0)) = padicValNat 2 (p + 1) + ℓ - 1 := hv0
    rw [padicValNat_two_sigma_odd_prime_pow hp hodd]
    by_cases hEk : Even (k + 1)
    · rw [if_pos hEk, hv0']
      have hlt : padicValNat 2 (k + 1) < ℓ := by
        apply padicValNat_two_lt_log (N := N) (by omega) (by omega)
        · have : k < a + 1 := mem_range.mp hk
          omega
        · intro heq
          have : k + 1 = k0 + 1 := by rw [heq, hk0_succ]
          exact hkne (Nat.succ_injective this)
      have : padicValNat 2 (p + 1) + padicValNat 2 (k + 1) - 1
          < padicValNat 2 (p + 1) + ℓ - 1 := by
        have h1 : 1 ≤ padicValNat 2 (p + 1) + padicValNat 2 (k + 1) := by omega
        have h2 : 1 ≤ padicValNat 2 (p + 1) + ℓ := by omega
        omega
      exact this
    · rw [if_neg hEk, hv0']
      have : 0 < padicValNat 2 (p + 1) + ℓ - 1 := by omega
      exact this
  -- now apply ultrametric
  rw [fSum_prime_pow hp]
  set F : ℕ → ℚ := fun k => (1 : ℚ) / (sigma 1 (p ^ k) : ℚ)
  have hFpos : ∀ k, 0 < F k := fun k => by
    have : (0 : ℚ) < (sigma 1 (p ^ k) : ℚ) := by
      exact_mod_cast sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)
    positivity
  have hsum0 : (∑ k ∈ range (a + 1), F k) ≠ 0 := by
    exact (Finset.sum_pos (fun k _ => hFpos k) (nonempty_range_iff.mpr (by omega))).ne'
  -- split off k0
  have hsplit : ∑ k ∈ range (a + 1), F k = F k0 + ∑ k ∈ (range (a + 1)).erase k0, F k :=
    (add_sum_erase (range (a + 1)) F hk0_mem).symm
  rw [hsplit]
  have hrest_ne : F k0 + ∑ k ∈ (range (a + 1)).erase k0, F k ≠ 0 := by
    rwa [← hsplit]
  -- if the rest is empty (only happens if a=0, excluded)
  by_cases hrest : ((range (a + 1)).erase k0).Nonempty
  · have hlt_rest : padicValRat 2 (F k0) <
        padicValRat 2 (∑ k ∈ (range (a + 1)).erase k0, F k) := by
      apply padicValRat.lt_sum_of_lt (j := k0) (F := F) hrest
      · intro i hi
        exact hstrict i (mem_of_mem_erase hi) (ne_of_mem_erase hi)
      · exact fun i => hFpos i
    have : padicValRat 2 (F k0 + ∑ k ∈ (range (a + 1)).erase k0, F k) =
        padicValRat 2 (F k0) :=
      padicValRat.add_eq_of_lt hrest_ne (hFpos k0).ne'
        (Finset.sum_pos (fun i _ => hFpos i) hrest).ne' hlt_rest
    rw [this, show F k0 = (1 : ℚ) / (sigma 1 (p ^ k0) : ℚ) from rfl]
    rw [v2_term_odd_prime hp hodd, hv0]
    have hle1 : 1 ≤ padicValNat 2 (p + 1) + ℓ := by omega
    have hcast : ((padicValNat 2 (p + 1) + ℓ - 1 : ℕ) : ℤ) =
        (padicValNat 2 (p + 1) : ℤ) + ↑ℓ - 1 := by
      rw [Nat.cast_sub hle1, Nat.cast_add, Nat.cast_one]
    rw [hcast]
    simp [ℓ, N]
    ring
  · -- rest empty: range (a+1) = {k0}, so a+1 = 1, a = 0, contradiction
    have : range (a + 1) = {k0} := by
      simpa [erase_eq_empty_iff] using hrest
    have : a + 1 = 1 := by
      have := congrArg card this
      simp at this
      omega
    omega



lemma den_ne_one_of_neg_padic {p : ℕ} [Fact p.Prime] {q : ℚ}
    (h : padicValRat p q < 0) : q.den ≠ 1 := by
  intro hd
  have : 0 ≤ padicValRat p q := by
    rw [padicValRat, hd]
    simp
  omega

lemma sigma_two_pow (k : ℕ) : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  simpa using sigma_mul_pred Nat.prime_two (k := k)

lemma odd_two_pow_sub_one (k : ℕ) : Odd (2 ^ (k + 1) - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow
    (even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩) odd_one

lemma v2_term_two (k : ℕ) :
    padicValRat 2 ((1 : ℚ) / (sigma 1 (2 ^ k) : ℚ)) = 0 := by
  haveI := two_fact
  rw [padicValRat_inv_nat, sigma_two_pow, padicValNat_odd_eq_zero (odd_two_pow_sub_one k)]
  simp

lemma fSum_factorization {n : ℕ} (hn : n ≠ 0) :
    fSum n = n.factorization.prod fun p k => fSum (p ^ k) :=
  IsMultiplicative.multiplicative_factorization fSum isMultiplicative_fSum hn

lemma padicValRat_prod {ι : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq ι]
    (s : Finset ι) (g : ι → ℚ) (hg : ∀ i ∈ s, g i ≠ 0) :
    padicValRat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValRat p (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [prod_insert has, sum_insert has]
    rw [padicValRat.mul (hg a (mem_insert_self _ _))
      (prod_ne_zero_iff.mpr fun i hi => hg i (mem_insert_of_mem hi))]
    rw [ih fun i hi => hg i (mem_insert_of_mem hi)]

lemma padicValRat_two_fSum_eq_sum {n : ℕ} (hn : n ≠ 0) :
    padicValRat 2 (fSum n) =
      ∑ p ∈ n.primeFactors, padicValRat 2 (fSum (p ^ n.factorization p)) := by
  haveI := two_fact
  rw [fSum_factorization hn]
  have hs : n.factorization.support ⊆ n.primeFactors := by
    simp [n.support_factorization]
  rw [Finsupp.prod_of_support_subset n.factorization hs (fun p k => fSum (p ^ k))
      (fun p _ => by simp [fSum_one])]
  exact padicValRat_prod n.primeFactors _ (fun p hp =>
    fSum_ne_zero (pow_ne_zero _ (prime_of_mem_primeFactors hp).ne_zero))

lemma padicValRat_two_fSum_odd_prime_pow_neg {p a : ℕ}
    (hp : p.Prime) (hodd : Odd p) (ha : 1 ≤ a) :
    padicValRat 2 (fSum (p ^ a)) < 0 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_odd_prime_pow hp hodd ha]
  have h1 : 1 ≤ padicValNat 2 (p + 1) :=
    one_le_padicValNat_of_dvd (by omega)
      (even_iff_two_dvd.mp (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)))
  have h2 : 1 ≤ Nat.log 2 (a + 1) := Nat.log_pos (by decide) (by omega)
  omega

lemma factorization_pos_of_mem_primeFactors {n p : ℕ} (hp : p ∈ n.primeFactors) :
    1 ≤ n.factorization p := by
  have : n.factorization p ≠ 0 := by
    rwa [← Finsupp.mem_support_iff, n.support_factorization]
  omega

lemma padicValRat_two_fSum_odd {n : ℕ} (hodd : Odd n) (hn : 1 < n) :
    padicValRat 2 (fSum n) < 0 := by
  haveI := two_fact
  have hn0 : n ≠ 0 := by omega
  have h2n : 2 ∉ n.primeFactors := by
    intro h
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (dvd_of_mem_primeFactors h))
  rw [padicValRat_two_fSum_eq_sum hn0]
  have hne : n.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    omega
  have hneg : ∀ p ∈ n.primeFactors,
      padicValRat 2 (fSum (p ^ n.factorization p)) < 0 := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_primeFactors hp
    have hpo : Odd p := hpp.odd_of_ne_two (ne_of_mem_of_not_mem hp h2n)
    exact padicValRat_two_fSum_odd_prime_pow_neg hpp hpo
      (factorization_pos_of_mem_primeFactors hp)
  have h0 : (∑ p ∈ n.primeFactors, padicValRat 2 (fSum (p ^ n.factorization p))) <
      ∑ p ∈ n.primeFactors, (0 : ℤ) :=
    Finset.sum_lt_sum (fun p hp => (hneg p hp).le) (let ⟨p, hp⟩ := hne; ⟨p, hp, hneg p hp⟩)
  simpa using h0

/-! ## Integers, bounds, and the even case -/

lemma den_ne_one_of_mem_Ioo {q : ℚ} (h1 : 1 < q) (h2 : q < 2) : q.den ≠ 1 := by
  intro hd
  have hq : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hd
  rw [← hq] at h1 h2
  have h1z : (1 : ℤ) < q.num := by exact_mod_cast h1
  have h2z : (q.num : ℤ) < 2 := by exact_mod_cast h2
  omega

lemma fSum_two_pow_eq (a : ℕ) :
    fSum (2 ^ a) =
      ∑ k ∈ range (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
  rw [fSum_prime_pow Nat.prime_two]
  refine sum_congr rfl fun k _ => ?_
  rw [sigma_two_pow]

lemma fSum_two_pow_gt_one {a : ℕ} (ha : 1 ≤ a) : 1 < fSum (2 ^ a) := by
  rw [fSum_two_pow_eq]
  have hmem : 0 ∈ range (a + 1) := by simp
  have hsplit := (add_sum_erase (range (a + 1))
    (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) hmem).symm
  rw [hsplit]
  have h0 : (1 : ℚ) / ((2 ^ (0 + 1) - 1 : ℕ) : ℚ) = 1 := by norm_num
  rw [h0]
  have hpos : 0 < ∑ k ∈ (range (a + 1)).erase 0,
      (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
    refine Finset.sum_pos (fun k hk => ?_) ?_
    · have : 0 < 2 ^ (k + 1) - 1 :=
        Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero _))
      positivity
    · refine ⟨1, ?_⟩
      simp [mem_erase]
      omega
  linarith

lemma sum_half_pow (a : ℕ) :
    ∑ k ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (k + 1) =
      1 - (1 : ℚ) / (2 : ℚ) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, ih]
    field_simp
    ring

lemma mersenne_recip_lt {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) <
      (1 : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
  have hpos : (0 : ℚ) < ((2 ^ k : ℕ) : ℚ) := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
  refine one_div_lt_one_div_of_lt hpos ?_
  have hltN : 2 ^ k < 2 ^ (k + 1) - 1 := by
    have hx : 2 ≤ 2 ^ k := by
      exact le_trans (by decide : 2 ≤ 2 ^ 1) (pow_le_pow_right₀ (by decide : 1 ≤ 2) hk)
    have : ∀ n : ℕ, 2 ≤ n → n < 2 * n - 1 := fun n hn => by omega
    have := this (2 ^ k) hx
    rwa [← pow_succ' 2 k] at this
  exact_mod_cast hltN

lemma fSum_two_pow_lt_two {a : ℕ} (ha : 1 ≤ a) : fSum (2 ^ a) < 2 := by
  rw [fSum_two_pow_eq]
  have hmem : 0 ∈ range (a + 1) := by simp
  have hsplit := (add_sum_erase (range (a + 1))
    (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) hmem).symm
  rw [hsplit]
  have h0 : (1 : ℚ) / ((2 ^ (0 + 1) - 1 : ℕ) : ℚ) = 1 := by norm_num
  rw [h0]
  have hlt : ∑ k ∈ (range (a + 1)).erase 0,
      (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) < 1 := by
    have hsubset : (range (a + 1)).erase 0 ⊆ image Nat.succ (range a) := by
      intro k hk
      simp [mem_erase] at hk
      refine mem_image.mpr ⟨k - 1, ?_, ?_⟩
      · simp; omega
      · omega
    -- compare termwise with 1/2^k
    have hcmp : ∑ k ∈ (range (a + 1)).erase 0,
        (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≤
        ∑ k ∈ range a, (1 : ℚ) / ((2 ^ (k + 1) : ℕ) : ℚ) := by
      -- reindex: erase 0 = {1,...,a}
      have heq : (range (a + 1)).erase 0 = Ico 1 (a + 1) := by
        ext k
        simp [mem_erase, mem_Ico, mem_range]
        omega
      have himg : Ico 1 (a + 1) = image Nat.succ (range a) := by
        ext k
        simp [mem_Ico, mem_range]
        constructor
        · intro ⟨hk1, hka⟩
          exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨i, hi, rfl⟩
          constructor
          · exact Nat.succ_pos i
          · exact Nat.succ_le_iff.mpr hi
      rw [heq, himg, sum_image (fun _ _ _ _ h => Nat.succ_injective h)]
      refine sum_le_sum fun i _ => ?_
      have : (1 : ℚ) / ((2 ^ (i + 1 + 1) - 1 : ℕ) : ℚ) <
          (1 : ℚ) / ((2 ^ (i + 1) : ℕ) : ℚ) :=
        mersenne_recip_lt (Nat.succ_le_succ (Nat.zero_le _))
      exact this.le
    have hcast : ∑ k ∈ range a, (1 : ℚ) / ((2 ^ (k + 1) : ℕ) : ℚ) =
        ∑ k ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (k + 1) := by
      refine sum_congr rfl fun k _ => ?_
      congr 1
      rw [Nat.cast_pow, Nat.cast_ofNat]
    have hgeom : ∑ k ∈ range a, (1 : ℚ) / (2 : ℚ) ^ (k + 1) < 1 := by
      rw [sum_half_pow]
      have : (0 : ℚ) < (1 : ℚ) / (2 : ℚ) ^ a := by positivity
      linarith
    linarith
  linarith

lemma fSum_two_pow_not_int {a : ℕ} (ha : 1 ≤ a) : (fSum (2 ^ a)).den ≠ 1 :=
  den_ne_one_of_mem_Ioo (fSum_two_pow_gt_one ha) (fSum_two_pow_lt_two ha)

lemma fSum_eq_mul_odd_part {n : ℕ} (hn : n ≠ 0) :
    fSum n = fSum (2 ^ n.factorization 2) * fSum (ordCompl[2] n) := by
  have hdecomp : 2 ^ n.factorization 2 * ordCompl[2] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ n.factorization 2) (ordCompl[2] n) :=
    (Nat.coprime_ordCompl Nat.prime_two hn).pow_left _
  conv_lhs => rw [← hdecomp]
  exact fSum_mul hcop

lemma odd_ordCompl (n : ℕ) (hn : n ≠ 0) : Odd (ordCompl[2] n) :=
  Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))

def twoPowDen (a : ℕ) : ℕ := ∏ k ∈ range (a + 1), (2 ^ (k + 1) - 1)

def twoPowNum (a : ℕ) : ℕ :=
  ∑ k ∈ range (a + 1), twoPowDen a / (2 ^ (k + 1) - 1)

lemma twoPowDen_pos (a : ℕ) : 0 < twoPowDen a :=
  Finset.prod_pos fun k _ => Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero _))

lemma odd_mul {m n : ℕ} (hm : Odd m) (hn : Odd n) : Odd (m * n) :=
  hm.mul hn

lemma odd_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [prod_insert has]
    exact (hf a (mem_insert_self a s)).mul
      (ih fun i hi => hf i (mem_insert_of_mem hi))

lemma twoPowDen_odd (a : ℕ) : Odd (twoPowDen a) :=
  odd_prod _ _ (fun k _ => odd_two_pow_sub_one k)

lemma twoPowDen_dvd (a k : ℕ) (hk : k ∈ range (a + 1)) :
    (2 ^ (k + 1) - 1) ∣ twoPowDen a :=
  dvd_prod_of_mem _ hk

lemma odd_div_of_odd {m n : ℕ} (hm : Odd m) (hdvd : n ∣ m) : Odd (m / n) := by
  refine Nat.not_even_iff_odd.mp ?_
  intro h
  have : Even m := by
    rw [even_iff_two_dvd] at h ⊢
    have hm' : m = m / n * n := (Nat.div_mul_cancel hdvd).symm
    rw [hm']
    exact dvd_mul_of_dvd_left h n
  exact Nat.not_even_iff_odd.mpr hm this

lemma twoPowNum_term_odd (a k : ℕ) (hk : k ∈ range (a + 1)) :
    Odd (twoPowDen a / (2 ^ (k + 1) - 1)) :=
  odd_div_of_odd (twoPowDen_odd a) (twoPowDen_dvd a k hk)

lemma twoPowNum_mod_two (a : ℕ) : twoPowNum a % 2 = (a + 1) % 2 := by
  have h := Finset.sum_nat_mod (s := range (a + 1))
    (f := fun k => twoPowDen a / (2 ^ (k + 1) - 1)) 2
  have : ∀ k ∈ range (a + 1),
      (twoPowDen a / (2 ^ (k + 1) - 1)) % 2 = 1 :=
    fun k hk => Nat.odd_iff.mp (twoPowNum_term_odd a k hk)
  rw [twoPowNum, h, sum_congr rfl this]
  simp [card_range]

lemma twoPowNum_odd_of_even {a : ℕ} (he : Even a) : Odd (twoPowNum a) := by
  rw [Nat.odd_iff, twoPowNum_mod_two, ← Nat.odd_iff]
  exact he.add_odd odd_one

lemma twoPowNum_even_of_odd {a : ℕ} (ho : Odd a) : Even (twoPowNum a) := by
  rw [Nat.even_iff, twoPowNum_mod_two, ← Nat.even_iff]
  exact ho.add_odd odd_one

lemma twoPowNum_pos (a : ℕ) : 0 < twoPowNum a :=
  Finset.sum_pos (fun k hk =>
    Nat.div_pos (Nat.le_of_dvd (twoPowDen_pos a) (twoPowDen_dvd a k hk))
      (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero _))))
    (nonempty_range_iff.mpr (Nat.succ_ne_zero a))

lemma fSum_two_pow_as_frac (a : ℕ) :
    fSum (2 ^ a) = (twoPowNum a : ℚ) / (twoPowDen a : ℚ) := by
  rw [fSum_two_pow_eq]
  have hVpos : (twoPowDen a : ℚ) ≠ 0 := by exact_mod_cast (twoPowDen_pos a).ne'
  apply (eq_div_iff hVpos).mpr
  rw [twoPowNum, Nat.cast_sum, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  have hdvd := twoPowDen_dvd a k hk
  have hnzN : (2 ^ (k + 1) - 1 : ℕ) ≠ 0 :=
    (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero k))).ne'
  have hcast := Nat.cast_div (m := twoPowDen a) (n := 2 ^ (k + 1) - 1) hdvd
    (mod_cast hnzN : ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≠ 0)
  rw [hcast]
  have hdenQ : ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnzN
  field_simp

lemma padicValRat_two_fSum_two_pow (a : ℕ) :
    padicValRat 2 (fSum (2 ^ a)) = padicValNat 2 (twoPowNum a) := by
  haveI := two_fact
  rw [fSum_two_pow_as_frac, div_eq_mul_inv]
  have hU : (twoPowNum a : ℚ) ≠ 0 := by exact_mod_cast (twoPowNum_pos a).ne'
  have hV : (twoPowDen a : ℚ) ≠ 0 := by exact_mod_cast (twoPowDen_pos a).ne'
  rw [padicValRat.mul hU (inv_ne_zero hV), padicValRat.inv,
    padicValRat.of_nat, padicValRat.of_nat]
  simp [padicValNat_odd_eq_zero (twoPowDen_odd a)]

lemma v2_fSum_two_pow_of_even {a : ℕ} (he : Even a) :
    padicValRat 2 (fSum (2 ^ a)) = 0 := by
  rw [padicValRat_two_fSum_two_pow, Nat.cast_eq_zero]
  exact padicValNat_odd_eq_zero (twoPowNum_odd_of_even he)

lemma v2_fSum_two_pow_of_odd {a : ℕ} (ho : Odd a) :
    1 ≤ padicValRat 2 (fSum (2 ^ a)) := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  exact_mod_cast one_le_padicValNat_of_dvd (twoPowNum_pos a).ne'
    (even_iff_two_dvd.mp (twoPowNum_even_of_odd ho))

lemma factorization_two_pos_of_even {n : ℕ} (he : Even n) (hn : n ≠ 0) :
    1 ≤ n.factorization 2 :=
  (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).mp (even_iff_two_dvd.mp he)

lemma twoPowDen_succ (a : ℕ) :
    twoPowDen (a + 1) = twoPowDen a * (2 ^ (a + 2) - 1) := by
  simp [twoPowDen, prod_range_succ, Nat.add_assoc]

lemma two_pow_ge_two_zmod4 (t : ℕ) (ht : 2 ≤ t) : ((2 ^ t : ℕ) : ZMod 4) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
  rw [show t = 2 + k from hk, pow_add, Nat.cast_mul]
  have : ((2 ^ 2 : ℕ) : ZMod 4) = 0 := by decide
  rw [this, zero_mul]

lemma mersenne_zmod4 (k : ℕ) :
    ((2 ^ (k + 1) - 1 : ℕ) : ZMod 4) = if k = 0 then (1 : ZMod 4) else 3 := by
  cases k with
  | zero =>
    decide
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k)]
    have hle : 1 ≤ 2 ^ (k.succ + 1) := Nat.one_le_two_pow
    rw [Nat.cast_sub hle]
    have : ((2 ^ (k.succ + 1) : ℕ) : ZMod 4) = 0 :=
      two_pow_ge_two_zmod4 _ (by omega)
    rw [this]
    decide

lemma twoPowDen_zmod4 (a : ℕ) : (twoPowDen a : ZMod 4) = (3 : ZMod 4) ^ a := by
  induction a with
  | zero =>
    simp [twoPowDen]
  | succ a ih =>
    rw [twoPowDen_succ, Nat.cast_mul, ih]
    have hm : ((2 ^ (a + 1 + 1) - 1 : ℕ) : ZMod 4) = 3 := by
      simpa [mersenne_zmod4] using
        (mersenne_zmod4 (a + 1)).trans (if_neg (Nat.succ_ne_zero a))
    rw [show a + 2 = a + 1 + 1 from rfl, hm, pow_succ]

lemma nat_div_zmod4 {V d : ℕ} (hdvd : d ∣ V) {u : ZMod 4}
    (hinv : (d : ZMod 4) * u = 1) :
    ((V / d : ℕ) : ZMod 4) = (V : ZMod 4) * u := by
  have hV : ((V / d : ℕ) : ZMod 4) * (d : ZMod 4) = (V : ZMod 4) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  calc
    ((V / d : ℕ) : ZMod 4) = ((V / d : ℕ) : ZMod 4) * 1 := by rw [mul_one]
    _ = ((V / d : ℕ) : ZMod 4) * ((d : ZMod 4) * u) := by rw [hinv]
    _ = (((V / d : ℕ) : ZMod 4) * (d : ZMod 4)) * u := by ring
    _ = (V : ZMod 4) * u := by rw [hV]

lemma twoPowNum_term_zmod4 (a k : ℕ) (hk : k ∈ range (a + 1)) :
    ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 4) =
      if k = 0 then (3 : ZMod 4) ^ a else (3 : ZMod 4) ^ (a + 1) := by
  have hdvd := twoPowDen_dvd a k hk
  have hV : (twoPowDen a : ZMod 4) = (3 : ZMod 4) ^ a := twoPowDen_zmod4 a
  by_cases hk0 : k = 0
  · subst hk0
    have hd : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 4) = 1 := by decide
    have hinv : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 4) * 1 = 1 := by rw [hd, mul_one]
    rw [if_pos rfl, nat_div_zmod4 hdvd hinv, hV, mul_one]
  · have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 4) = 3 := by
      simpa [mersenne_zmod4, hk0] using mersenne_zmod4 k
    have hinv : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 4) * 3 = 1 := by
      rw [hd]; decide
    rw [if_neg hk0, nat_div_zmod4 hdvd hinv, hV, pow_succ]

lemma twoPowNum_zmod4 (a : ℕ) :
    (twoPowNum a : ZMod 4) = (3 : ZMod 4) ^ a * (1 + 3 * a) := by
  rw [twoPowNum, Nat.cast_sum]
  have hterms : ∀ k ∈ range (a + 1),
      ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 4) =
        if k = 0 then (3 : ZMod 4) ^ a else (3 : ZMod 4) ^ (a + 1) :=
    fun k hk => twoPowNum_term_zmod4 a k hk
  rw [sum_congr rfl hterms]
  have h0 : 0 ∈ range (a + 1) := by simp
  rw [← add_sum_erase _ _ h0, if_pos rfl]
  have herase : ∀ k ∈ (range (a + 1)).erase 0,
      (if k = 0 then (3 : ZMod 4) ^ a else (3 : ZMod 4) ^ (a + 1)) =
        (3 : ZMod 4) ^ (a + 1) := by
    intro k hk
    have hk0 : k ≠ 0 := (mem_erase.mp hk).1
    rw [if_neg hk0]
  rw [sum_congr rfl herase]
  have hcard : ((range (a + 1)).erase 0).card = a := by
    rw [card_erase_of_mem h0, card_range, Nat.add_sub_cancel]
  rw [sum_const, hcard, nsmul_eq_mul]
  rw [pow_succ]
  push_cast
  ring

lemma three_pow_odd_zmod4 {a : ℕ} (hodd : Odd a) : (3 : ZMod 4) ^ a = 3 := by
  have : (3 : ZMod 4) = -1 := by decide
  rw [this, hodd.neg_one_pow]

lemma twoPowNum_zmod4_of_mod4_three {a : ℕ} (h : a ≡ 3 [MOD 4]) :
    twoPowNum a % 4 = 2 := by
  have ha : (a : ZMod 4) = (3 : ℕ) := (ZMod.natCast_eq_natCast_iff a 3 4).mpr h
  have hodd : Odd a := by
    rw [Nat.odd_iff]
    have : a % 4 = 3 := by simpa [Nat.ModEq] using h
    omega
  have heq : (twoPowNum a : ZMod 4) = (2 : ℕ) := by
    rw [twoPowNum_zmod4, three_pow_odd_zmod4 hodd, ha]
    decide
  have hval := congrArg ZMod.val heq
  rw [ZMod.val_natCast, ZMod.val_natCast] at hval
  simpa using hval

lemma twoPowNum_zmod4_of_mod4_one {a : ℕ} (h : a ≡ 1 [MOD 4]) :
    twoPowNum a % 4 = 0 := by
  have ha : (a : ZMod 4) = (1 : ℕ) := (ZMod.natCast_eq_natCast_iff a 1 4).mpr h
  have hodd : Odd a := by
    rw [Nat.odd_iff]
    have : a % 4 = 1 := by simpa [Nat.ModEq] using h
    omega
  have heq : (twoPowNum a : ZMod 4) = (0 : ℕ) := by
    rw [twoPowNum_zmod4, three_pow_odd_zmod4 hodd, ha]
    decide
  have hval := congrArg ZMod.val heq
  rw [ZMod.val_natCast, ZMod.val_natCast] at hval
  simpa using hval

lemma v2_fSum_two_pow_mod4_three {a : ℕ} (h : a ≡ 3 [MOD 4]) :
    padicValRat 2 (fSum (2 ^ a)) = 1 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 4 = 2 := twoPowNum_zmod4_of_mod4_three h
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have hdiv2 : 2 ∣ twoPowNum a := Nat.dvd_of_mod_eq_zero (by omega)
  have hndiv4 : ¬ 4 ∣ twoPowNum a := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hle : 1 ≤ padicValNat 2 (twoPowNum a) :=
    one_le_padicValNat_of_dvd hpos hdiv2
  have hlt : padicValNat 2 (twoPowNum a) < 2 := by
    by_contra hge
    have : 2 ^ 2 ∣ twoPowNum a := by
      have : 2 ≤ padicValNat 2 (twoPowNum a) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv4 (by simpa using this)
  have : padicValNat 2 (twoPowNum a) = 1 := by omega
  exact_mod_cast this

lemma nat_div_cast_mul_inv {n V d : ℕ} [NeZero n] (hdvd : d ∣ V)
    {u : ZMod n} (hu : (d : ZMod n) * u = 1) :
    ((V / d : ℕ) : ZMod n) = (V : ZMod n) * u := by
  have hV : ((V / d : ℕ) : ZMod n) * (d : ZMod n) = (V : ZMod n) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  calc
    ((V / d : ℕ) : ZMod n) = ((V / d : ℕ) : ZMod n) * 1 := by rw [mul_one]
    _ = ((V / d : ℕ) : ZMod n) * ((d : ZMod n) * u) := by rw [hu]
    _ = (((V / d : ℕ) : ZMod n) * (d : ZMod n)) * u := by ring
    _ = (V : ZMod n) * u := by rw [hV]

lemma two_pow_ge_three_zmod8 (t : ℕ) (ht : 3 ≤ t) : ((2 ^ t : ℕ) : ZMod 8) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
  rw [show t = 3 + k from hk, pow_add, Nat.cast_mul]
  have : ((2 ^ 3 : ℕ) : ZMod 8) = 0 := by decide
  rw [this, zero_mul]

lemma mersenne_zmod8_of_ge_two {k : ℕ} (hk : 2 ≤ k) :
    ((2 ^ (k + 1) - 1 : ℕ) : ZMod 8) = 7 := by
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [Nat.cast_sub hle]
  have : ((2 ^ (k + 1) : ℕ) : ZMod 8) = 0 :=
    two_pow_ge_three_zmod8 (k + 1) (by omega)
  rw [this]
  decide

lemma even_pred_of_odd {a : ℕ} (h : Odd a) : Even (a - 1) := by
  rw [Nat.even_iff, Nat.odd_iff] at *
  omega

lemma twoPowDen_zmod8_of_mod8_one {a : ℕ} (h : a ≡ 1 [MOD 8]) :
    (twoPowDen a : ZMod 8) = 3 := by
  have ha : a % 8 = 1 := by simpa [Nat.ModEq] using h
  have hodd : Odd a := by rw [Nat.odd_iff]; omega
  rw [twoPowDen]
  have h0 : 0 ∈ range (a + 1) := by simp
  rw [← mul_prod_erase _ _ h0, Nat.cast_mul]
  have hd0 : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 8) = 1 := by decide
  rw [hd0, one_mul]
  cases le_or_gt a 1 with
  | inl hle =>
    have : a = 1 := by omega
    subst this
    decide
  | inr hgt =>
    have h1 : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← mul_prod_erase _ _ h1, Nat.cast_mul]
    have hd1 : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 8) = 3 := by decide
    rw [hd1]
    have hrest : ∀ k ∈ ((range (a + 1)).erase 0).erase 1,
        ((2 ^ (k + 1) - 1 : ℕ) : ZMod 8) = 7 := by
      intro k hk
      have hk2 : 2 ≤ k := by simp [mem_erase] at hk; omega
      exact mersenne_zmod8_of_ge_two hk2
    have hcard : (((range (a + 1)).erase 0).erase 1).card = a - 1 := by
      rw [card_erase_of_mem h1, card_erase_of_mem h0, card_range]; omega
    have heven : Even (a - 1) := even_pred_of_odd hodd
    have hprod1 : ((∏ k ∈ ((range (a + 1)).erase 0).erase 1,
        (2 ^ (k + 1) - 1) : ℕ) : ZMod 8) = 1 := by
      rw [Nat.cast_prod, prod_congr rfl hrest, prod_const, hcard]
      have : (7 : ZMod 8) = -1 := by decide
      rw [this, heven.neg_one_pow]
    rw [hprod1, mul_one]

lemma twoPowNum_zmod8_of_mod8_one {a : ℕ} (h : a ≡ 1 [MOD 8]) :
    twoPowNum a % 8 = 4 := by
  have ha : a % 8 = 1 := by simpa [Nat.ModEq] using h
  have hodd : Odd a := by rw [Nat.odd_iff]; omega
  have hV : (twoPowDen a : ZMod 8) = 3 := twoPowDen_zmod8_of_mod8_one h
  have h0 : 0 ∈ range (a + 1) := by simp
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 8) = 3 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 8) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hsum : (twoPowNum a : ZMod 8) = 4 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    cases le_or_gt a 1 with
    | inl hle =>
      have : a = 1 := by omega
      subst this
      decide
    | inr hgt =>
      have h1mem : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
      have h1range : 1 ∈ range (a + 1) := by simp; omega
      have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 8) = 1 := by
        have hdvd := twoPowDen_dvd a 1 h1range
        have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 8) * 3 = 1 := by decide
        rw [nat_div_cast_mul_inv hdvd hu, hV]
        decide
      rw [← add_sum_erase _ _ h1mem, hterm1]
      have htermk : ∀ k ∈ ((range (a + 1)).erase 0).erase 1,
          ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 8) = 5 := by
        intro k hk
        have hk2 : 2 ≤ k := by simp [mem_erase] at hk; omega
        have hkmem : k ∈ range (a + 1) :=
          mem_of_mem_erase (mem_of_mem_erase hk)
        have hdvd := twoPowDen_dvd a k hkmem
        have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 8) = 7 :=
          mersenne_zmod8_of_ge_two hk2
        have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 8) * 7 = 1 := by
          rw [hd]; decide
        rw [nat_div_cast_mul_inv hdvd hu, hV]
        decide
      rw [sum_congr rfl htermk, sum_const]
      have hcard : (((range (a + 1)).erase 0).erase 1).card = a - 1 := by
        rw [card_erase_of_mem h1mem, card_erase_of_mem h0, card_range]; omega
      rw [hcard, nsmul_eq_mul]
      have ha1 : ((a - 1 : ℕ) : ZMod 8) = 0 := by
        have hdiv : 8 ∣ a - 1 := by
          omega
        rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff]
        simpa [Nat.ModEq] using Nat.modEq_zero_iff_dvd.mpr hdiv
      rw [ha1]
      decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (4 : ZMod 8).val = 4 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod8_one {a : ℕ} (h : a ≡ 1 [MOD 8]) :
    padicValRat 2 (fSum (2 ^ a)) = 2 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 8 = 4 := twoPowNum_zmod8_of_mod8_one h
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have hdiv4 : 4 ∣ twoPowNum a :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hndiv8 : ¬ 8 ∣ twoPowNum a := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hle : 2 ≤ padicValNat 2 (twoPowNum a) := by
    have : 2 ^ 2 ∣ twoPowNum a := by simpa using hdiv4
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 (twoPowNum a) < 3 := by
    by_contra hge
    have : 2 ^ 3 ∣ twoPowNum a := by
      have : 3 ≤ padicValNat 2 (twoPowNum a) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv8 (by simpa using this)
  have : padicValNat 2 (twoPowNum a) = 2 := by omega
  exact_mod_cast this

lemma v2_fSum_two_pow_mod4_one {a : ℕ} (h : a ≡ 1 [MOD 4]) :
    2 ≤ padicValRat 2 (fSum (2 ^ a)) := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 4 = 0 := twoPowNum_zmod4_of_mod4_one h
  have hdiv : 4 ∣ twoPowNum a := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have : 2 ^ 2 ∣ twoPowNum a := by simpa using hdiv
  have : 2 ≤ padicValNat 2 (twoPowNum a) := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  exact_mod_cast this

lemma fSum_two_pow_six :
    fSum (2 ^ 6) = (1982837 : ℚ) / 1240155 := by
  rw [fSum_two_pow_eq]
  simp [sum_range_succ]
  norm_num

lemma geom_sum_half_lt (n : ℕ) :
    ∑ i ∈ range n, (1 / 2 : ℚ) ^ i < 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℚ) ≠ 1)]
  have hpos : (0 : ℚ) < (1 / 2 : ℚ) ^ n := by positivity
  have : ((1 / 2 : ℚ) ^ n - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℚ) ^ n) := by
    field_simp; ring
  rw [this]
  linarith

lemma fSum_two_pow_lt_13_8 (a : ℕ) : fSum (2 ^ a) < (13 : ℚ) / 8 := by
  cases lt_or_ge a 7 with
  | inl hlt =>
    interval_cases a <;> (rw [fSum_two_pow_eq]; simp [sum_range_succ]; norm_num)
  | inr hge =>
    have h7 : 7 ≤ a + 1 := by omega
    have hsplit :
        fSum (2 ^ a) =
          fSum (2 ^ 6) +
            ∑ k ∈ Ico 7 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
      rw [fSum_two_pow_eq, fSum_two_pow_eq]
      simpa using
        (sum_range_add_sum_Ico
          (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) h7).symm
    have htail :
        ∑ k ∈ Ico 7 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) <
          (1 : ℚ) / 64 := by
      have hle :
          ∑ k ∈ Ico 7 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≤
            ∑ k ∈ Ico 7 (a + 1), (1 / 2 : ℚ) ^ k := by
        refine sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := by
          have : 7 ≤ k := (mem_Ico.mp hk).1
          omega
        have hcmp := (mersenne_recip_lt hk1).le
        have hcast : ((2 ^ k : ℕ) : ℚ) = (2 : ℚ) ^ k := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
        have : (1 : ℚ) / ((2 ^ k : ℕ) : ℚ) = (1 / 2 : ℚ) ^ k := by
          rw [hcast, div_pow, one_pow]
        rw [this] at hcmp
        exact hcmp
      have hgeom :
          ∑ k ∈ Ico 7 (a + 1), (1 / 2 : ℚ) ^ k < (1 : ℚ) / 64 := by
        rw [sum_Ico_eq_sum_range]
        have hfac :
            ∑ i ∈ range (a + 1 - 7), (1 / 2 : ℚ) ^ (7 + i) =
              (1 / 2 : ℚ) ^ 7 *
                ∑ i ∈ range (a + 1 - 7), (1 / 2 : ℚ) ^ i := by
          refine (sum_congr rfl fun i _ => ?_).trans (mul_sum _ _ _).symm
          rw [pow_add]
        rw [hfac]
        have hgs := geom_sum_half_lt (a + 1 - 7)
        have : (1 / 2 : ℚ) ^ 7 = 1 / 128 := by norm_num
        nlinarith
      linarith
    have h6 := fSum_two_pow_six
    have : (1982837 : ℚ) / 1240155 + 1 / 64 < 13 / 8 := by norm_num
    linarith

lemma sigma_gt_pow {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    p ^ j < sigma 1 (p ^ j) := by
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.one_lt
  have hdecomp : p ^ j * (p - 1) + p ^ j = p ^ (j + 1) := by
    have : (p - 1).succ = p := Nat.succ_pred_eq_of_pos hp.pos
    rw [← Nat.mul_succ, this, pow_succ]
  have hlt : p ^ j * (p - 1) + 1 < p ^ (j + 1) := by
    rw [← hdecomp]
    exact Nat.add_lt_add_left hpj _
  have hmul : p ^ j * (p - 1) < sigma 1 (p ^ j) * (p - 1) := by
    rw [sigma_mul_pred hp]
    exact Nat.lt_sub_of_add_lt hlt
  exact Nat.lt_of_mul_lt_mul_right hmul

lemma inv_sigma_lt_pow {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    (1 : ℚ) / (sigma 1 (p ^ j) : ℚ) < (1 : ℚ) / (p : ℚ) ^ j := by
  have hpos : (0 : ℚ) < (p : ℚ) ^ j :=
    pow_pos (Nat.cast_pos.mpr hp.pos) _
  refine one_div_lt_one_div_of_lt hpos ?_
  exact_mod_cast sigma_gt_pow hp hj

lemma inv_sigma_le_five_pow {p j : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hj : 2 ≤ j) :
    (1 : ℚ) / (sigma 1 (p ^ j) : ℚ) ≤ (1 / 5 : ℚ) ^ j := by
  have hlt := (inv_sigma_lt_pow hp (by omega : 1 ≤ j)).le
  have hle : (1 : ℚ) / (p : ℚ) ^ j ≤ (1 / 5 : ℚ) ^ j := by
    have hp5 : (5 : ℚ) ≤ p := by exact_mod_cast h5
    rw [← one_div_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ j
    exact one_div_le_one_div_of_le (by norm_num) hp5
  exact hlt.trans hle

lemma geom_sum_five_from_two {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ Icc 2 n, (1 / 5 : ℚ) ^ j < 1 / 20 := by
  have heq : Icc 2 n = image (· + 2) (range (n - 1)) := by
    ext j
    simp only [mem_Icc, mem_image, mem_range]
    constructor
    · intro ⟨h2, hjn⟩
      refine ⟨j - 2, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [heq, sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)]
  have hpow : ∀ i, (1 / 5 : ℚ) ^ (i + 2) = (1 / 25 : ℚ) * (1 / 5 : ℚ) ^ i := by
    intro i
    rw [pow_add, pow_two]
    ring
  rw [sum_congr rfl (fun i _ => hpow i), ← mul_sum]
  have hgs : ∑ i ∈ range (n - 1), (1 / 5 : ℚ) ^ i < 5 / 4 := by
    rw [geom_sum_eq (by norm_num : (1 / 5 : ℚ) ≠ 1)]
    have hden : (0 : ℚ) < 1 - 1 / 5 := by norm_num
    have hrewrite :
        ((1 / 5 : ℚ) ^ (n - 1) - 1) / (1 / 5 - 1) =
          (1 - (1 / 5 : ℚ) ^ (n - 1)) / (1 - 1 / 5) := by
      field_simp; ring
    rw [hrewrite]
    have hlt : (1 - (1 / 5 : ℚ) ^ (n - 1)) / (1 - 1 / 5) <
        1 / (1 - 1 / 5) := by
      rw [div_lt_div_iff₀ hden hden]
      nlinarith [show (0 : ℚ) < (1 / 5 : ℚ) ^ (n - 1) by positivity]
    have : (1 : ℚ) / (1 - 1 / 5) = 5 / 4 := by norm_num
    linarith
  nlinarith

lemma fSum_prime_pow_lt_73_60 (p k : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    fSum (p ^ k) < (73 : ℚ) / 60 := by
  rw [fSum_prime_pow hp]
  cases lt_or_ge k 2 with
  | inl hk =>
    interval_cases k
    · simp [sigma_one]; norm_num
    · rw [sum_range_succ, sum_range_one, pow_zero, pow_one, sigma_one, sigma_prime hp]
      push_cast
      have hle : (1 : ℚ) / ((p : ℚ) + 1) ≤ 1 / 6 := by
        refine one_div_le_one_div_of_le (by norm_num) ?_
        exact_mod_cast (by omega : 6 ≤ p + 1)
      have : (1 : ℚ) + 1 / 6 < 73 / 60 := by norm_num
      linarith
  | inr hk =>
    have h0mem : 0 ∈ range (k + 1) := by simp
    have h1mem : 1 ∈ (range (k + 1)).erase 0 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h0mem]
    have hterm0 : (1 : ℚ) / (sigma 1 (p ^ 0) : ℚ) = 1 := by
      simp [sigma_one]
    rw [hterm0]
    rw [← add_sum_erase _ _ h1mem]
    have hterm1 : (1 : ℚ) / (sigma 1 (p ^ 1) : ℚ) ≤ 1 / 6 := by
      rw [pow_one, sigma_prime hp]
      refine one_div_le_one_div_of_le (by norm_num) ?_
      exact_mod_cast (by omega : 6 ≤ p + 1)
    have hset : ((range (k + 1)).erase 0).erase 1 = Icc 2 k := by
      ext j
      simp [mem_erase, mem_range, mem_Icc]
      omega
    rw [hset]
    have hrest :
        ∑ j ∈ Icc 2 k, (1 : ℚ) / (sigma 1 (p ^ j) : ℚ) ≤
          ∑ j ∈ Icc 2 k, (1 / 5 : ℚ) ^ j :=
      sum_le_sum fun j hj => inv_sigma_le_five_pow hp h5 (mem_Icc.mp hj).1
    have htail := geom_sum_five_from_two hk
    have : (1 : ℚ) + 1 / 6 + 1 / 20 = 73 / 60 := by norm_num
    linarith

lemma fSum_two_pow_mul_prime_lt_two {a p k : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) :
    fSum (2 ^ a) * fSum (p ^ k) < 2 := by
  have h1 := fSum_two_pow_lt_13_8 a
  have h2 := fSum_prime_pow_lt_73_60 p k hp h5
  have hp1 : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hp2 : 0 < fSum (p ^ k) := fSum_pos (pow_ne_zero k hp.ne_zero)
  have : (13 : ℚ) / 8 * (73 / 60) < 2 := by norm_num
  nlinarith

lemma fSum_gt_one {n : ℕ} (hn : 1 < n) : 1 < fSum n := by
  have hn0 : n ≠ 0 := by omega
  rw [fSum_apply]
  have h1 : (1 : ℚ) / (sigma 1 1 : ℚ) = 1 := by simp
  have hmem : 1 ∈ n.divisors := one_mem_divisors.mpr hn0
  have hsplit := (add_sum_erase n.divisors
    (fun d => (1 : ℚ) / (sigma 1 d : ℚ)) hmem).symm
  rw [hsplit, h1]
  have : 0 < ∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (sigma 1 d : ℚ) := by
    have hnmem : n ∈ n.divisors := mem_divisors_self n hn0
    have hne : n ≠ 1 := by omega
    refine Finset.sum_pos (fun d hd => ?_) ⟨n, mem_erase.mpr ⟨hne, hnmem⟩⟩
    have hd0 : d ≠ 0 := (pos_of_mem_divisors (mem_of_mem_erase hd)).ne'
    have : (0 : ℚ) < (sigma 1 d : ℚ) := by exact_mod_cast sigma_pos 1 d hd0
    positivity
  linarith

lemma padicValNat_two_add_one_of_mod4_three {p : ℕ} (hp : Odd p)
    (h : p ≡ 3 [MOD 4]) : 2 ≤ padicValNat 2 (p + 1) := by
  haveI := two_fact
  have hmod : (p + 1) % 4 = 0 := by
    have : p % 4 = 3 := by simpa [Nat.ModEq] using h
    omega
  have hdiv : 4 ∣ p + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hpos : p + 1 ≠ 0 := by omega
  have : 2 ^ 2 ∣ p + 1 := by simpa using hdiv
  have : 2 ≤ padicValNat 2 (p + 1) := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  exact this

lemma v2_fSum_odd_prime_pow_mod4_three {p k : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : p ≡ 3 [MOD 4]) (hk : 1 ≤ k) :
    padicValRat 2 (fSum (p ^ k)) ≤ -2 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_odd_prime_pow hp hodd hk]
  have h1 : 2 ≤ padicValNat 2 (p + 1) := padicValNat_two_add_one_of_mod4_three hodd h
  have h2 : 1 ≤ Nat.log 2 (k + 1) := Nat.log_pos (by decide) (by omega)
  omega

lemma eq_pow_of_primeFactors_subset_singleton {m q : ℕ} (hm : m ≠ 0)
    (hq : q.Prime) (h : m.primeFactors ⊆ ({q} : Finset ℕ)) :
    m = q ^ m.factorization q := by
  rw [Finset.subset_singleton_iff] at h
  rcases h with h | h
  · have : m = 1 := by
      have := (Nat.primeFactors_eq_empty).mp h
      omega
    subst this
    simp
  · have hip : IsPrimePow m :=
      isPrimePow_iff_card_primeFactors_eq_one.mpr (by simp [h])
    have hmin : m.minFac = q := by
      have : m.minFac ∈ m.primeFactors :=
        mem_primeFactors.mpr ⟨minFac_prime (by
          intro hm1; subst hm1; simp at h), minFac_dvd m, hm⟩
      simpa [h] using this
    have heq := hip.minFac_pow_factorization_eq
    rw [hmin] at heq
    exact heq.symm

lemma eq_minFac_pow_of_card_primeFactors_eq_one {m : ℕ} (hm : 1 < m)
    (h : m.primeFactors.card = 1) :
    m = m.minFac ^ m.factorization m.minFac :=
  (isPrimePow_iff_card_primeFactors_eq_one.mpr h).minFac_pow_factorization_eq.symm

lemma v2_fSum_odd_le_neg_omega {m : ℕ} (hodd : Odd m) (hm : 1 < m) :
    padicValRat 2 (fSum m) ≤ - (m.primeFactors.card : ℤ) := by
  haveI := two_fact
  have hm0 : m ≠ 0 := by omega
  rw [padicValRat_two_fSum_eq_sum hm0]
  have hle : ∀ p ∈ m.primeFactors,
      padicValRat 2 (fSum (p ^ m.factorization p)) ≤ -1 := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_primeFactors hp
    have h2 : 2 ∉ m.primeFactors := by
      intro h
      exact Nat.not_even_iff_odd.mpr hodd
        (even_iff_two_dvd.mpr (dvd_of_mem_primeFactors h))
    have hpo : Odd p := hpp.odd_of_ne_two (ne_of_mem_of_not_mem hp h2)
    have := padicValRat_two_fSum_odd_prime_pow_neg hpp hpo
      (factorization_pos_of_mem_primeFactors hp)
    linarith
  have : (∑ p ∈ m.primeFactors,
      padicValRat 2 (fSum (p ^ m.factorization p))) ≤
      ∑ p ∈ m.primeFactors, (-1 : ℤ) :=
    sum_le_sum hle
  simpa using this

lemma fSum_strict_mono_two {a b : ℕ} (h : a < b) :
    fSum (2 ^ a) < fSum (2 ^ b) := by
  rw [fSum_two_pow_eq, fSum_two_pow_eq]
  have hle : a + 1 ≤ b + 1 := by omega
  have hsplit := sum_range_add_sum_Ico
    (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) hle
  rw [← hsplit]
  have hpos : 0 < ∑ k ∈ Ico (a + 1) (b + 1),
      (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
    refine Finset.sum_pos (fun k hk => ?_) ?_
    · have : 0 < 2 ^ (k + 1) - 1 :=
        Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero _))
      positivity
    · refine ⟨a + 1, ?_⟩
      simp [mem_Ico]
      omega
  linarith

lemma fSum_strict_mono_prime_pow {p a b : ℕ} (hp : p.Prime) (h : a < b) :
    fSum (p ^ a) < fSum (p ^ b) := by
  rw [fSum_prime_pow hp, fSum_prime_pow hp]
  have hle : a + 1 ≤ b + 1 := by omega
  have hsplit := sum_range_add_sum_Ico
    (fun k => (1 : ℚ) / (sigma 1 (p ^ k) : ℚ)) hle
  rw [← hsplit]
  have hpos : 0 < ∑ k ∈ Ico (a + 1) (b + 1),
      (1 : ℚ) / (sigma 1 (p ^ k) : ℚ) := by
    refine Finset.sum_pos (fun k hk => ?_) ?_
    · have hk0 : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
      have : 0 < (sigma 1 (p ^ k) : ℚ) := by exact_mod_cast sigma_pos 1 _ hk0
      positivity
    · refine ⟨a + 1, ?_⟩
      simp [mem_Ico]
      omega
  linarith


lemma inv_sigma_three_lt_pow {j : ℕ} (hj : 1 ≤ j) :
    (1 : ℚ) / (sigma 1 (3 ^ j) : ℚ) < (1 / 3 : ℚ) ^ j := by
  calc (1 : ℚ) / (sigma 1 (3 ^ j) : ℚ)
      < (1 : ℚ) / (3 : ℚ) ^ j := inv_sigma_lt_pow Nat.prime_three hj
    _ = (1 / 3 : ℚ) ^ j := (one_div_pow (3 : ℚ) j).symm

lemma fSum_three_pow_lt_three_halves (k : ℕ) :
    fSum (3 ^ k) < (3 : ℚ) / 2 := by
  rw [fSum_prime_pow Nat.prime_three]
  have h0 : (1 : ℚ) / (sigma 1 (3 ^ 0) : ℚ) = 1 := by simp [sigma_one]
  cases eq_or_ne k 0 with
  | inl hk =>
    subst hk
    simp [sigma_one]; norm_num
  | inr hk =>
    have h0mem : 0 ∈ range (k + 1) := by simp
    rw [← add_sum_erase _ _ h0mem, h0]
    have hrest :
        ∑ j ∈ (range (k + 1)).erase 0, (1 : ℚ) / (sigma 1 (3 ^ j) : ℚ) <
          (1 : ℚ) / 2 := by
      have hset : (range (k + 1)).erase 0 = Icc 1 k := by
        ext j; simp [mem_erase, mem_range, mem_Icc]; omega
      rw [hset]
      have hle : ∑ j ∈ Icc 1 k, (1 : ℚ) / (sigma 1 (3 ^ j) : ℚ) ≤
          ∑ j ∈ Icc 1 k, (1 / 3 : ℚ) ^ j :=
        sum_le_sum fun j hj => (inv_sigma_three_lt_pow (mem_Icc.mp hj).1).le
      have heq : Icc 1 k = image Nat.succ (range k) := by
        ext j
        simp [mem_Icc, mem_range]
        constructor
        · intro ⟨h1, hk'⟩
          exact ⟨j - 1, by omega, by omega⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨Nat.succ_pos _, Nat.succ_le_iff.mpr hi⟩
      have hgeom : ∑ j ∈ Icc 1 k, (1 / 3 : ℚ) ^ j < 1 / 2 := by
        rw [heq, sum_image (fun _ _ _ _ h => Nat.succ_injective h)]
        have hpow : ∀ i, (1 / 3 : ℚ) ^ (i + 1) = (1 / 3 : ℚ) * (1 / 3 : ℚ) ^ i :=
          fun i => pow_succ' (1 / 3 : ℚ) i
        rw [sum_congr rfl (fun i _ => hpow i), ← mul_sum]
        have hgs : ∑ i ∈ range k, (1 / 3 : ℚ) ^ i < 3 / 2 := by
          rw [geom_sum_eq (by norm_num)]
          have hden : (0 : ℚ) < 1 - 1 / 3 := by norm_num
          have : ((1 / 3 : ℚ) ^ k - 1) / (1 / 3 - 1) =
              (1 - (1 / 3 : ℚ) ^ k) / (1 - 1 / 3) := by field_simp; ring
          rw [this]
          have : (1 - (1 / 3 : ℚ) ^ k) / (1 - 1 / 3) < 1 / (1 - 1 / 3) := by
            rw [div_lt_div_iff₀ hden hden]
            nlinarith [show (0 : ℚ) < (1 / 3 : ℚ) ^ k by positivity]
          have : (1 : ℚ) / (1 - 1 / 3) = 3 / 2 := by norm_num
          linarith
        nlinarith
      linarith
    linarith

lemma fSum_two_six_lt_eight_five : fSum (2 ^ 6) < (8 : ℚ) / 5 := by
  rw [fSum_two_pow_six]; norm_num

lemma fSum_two_pow_seven :
    fSum (2 ^ 7) = (33790906 : ℚ) / 21082635 := by
  rw [fSum_two_pow_eq]
  simp [sum_range_succ]
  norm_num

lemma fSum_two_seven_gt_eight_five : (8 : ℚ) / 5 < fSum (2 ^ 7) := by
  rw [fSum_two_pow_seven]
  norm_num

lemma fSum_eight : fSum (2 ^ 3) = (54 : ℚ) / 35 := by
  rw [fSum_two_pow_eq]; simp [sum_range_succ]; norm_num

lemma fSum_nine : fSum (3 ^ 2) = (69 : ℚ) / 52 := by
  rw [fSum_prime_pow Nat.prime_three, sum_range_succ, sum_range_succ, sum_range_one]
  rw [pow_zero, sigma_one, pow_one, sigma_prime Nat.prime_three]
  have hs : sigma 1 (3 ^ 2) = 13 := by
    rw [sigma_eq_geom Nat.prime_three]
    simp [sum_range_succ]
  rw [hs]
  norm_num

lemma fSum_eight_mul_nine_gt_two : 2 < fSum (2 ^ 3) * fSum (3 ^ 2) := by
  rw [fSum_eight, fSum_nine]
  norm_num

lemma fSum_two_pow_ne_eight_five (a : ℕ) : fSum (2 ^ a) ≠ (8 : ℚ) / 5 := by
  cases lt_or_ge a 7 with
  | inl hlt =>
    have hle : fSum (2 ^ a) ≤ fSum (2 ^ 6) := by
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with
      | inl h => exact (fSum_strict_mono_two h).le
      | inr h => rw [h]
    exact ne_of_lt (lt_of_le_of_lt hle fSum_two_six_lt_eight_five)
  | inr hge =>
    have hge' : fSum (2 ^ 7) ≤ fSum (2 ^ a) := by
      cases Nat.lt_or_eq_of_le hge with
      | inl h => exact (fSum_strict_mono_two h).le
      | inr h => rw [h]
    exact ne_of_gt (lt_of_lt_of_le fSum_two_seven_gt_eight_five hge')

lemma fSum_four : fSum (2 ^ 2) = (31 : ℚ) / 21 := by
  rw [fSum_two_pow_eq]; simp [sum_range_succ]; norm_num

lemma sigma_three_pow : ∀ n : ℕ, sigma 1 (3 ^ n) = (3 ^ (n + 1) - 1) / 2 := by
  intro n
  have h := sigma_mul_pred Nat.prime_three (k := n)
  have : (3 - 1 : ℕ) = 2 := rfl
  rw [this] at h
  rw [mul_comm] at h
  exact Nat.eq_div_of_mul_eq_right (by decide) h

lemma fSum_three_pow_three : fSum (3 ^ 3) = (703 : ℚ) / 520 := by
  rw [fSum_prime_pow Nat.prime_three, sum_range_succ, sum_range_succ, sum_range_succ,
    sum_range_one]
  rw [pow_zero, sigma_one, pow_one, sigma_prime Nat.prime_three]
  rw [sigma_three_pow 2, sigma_three_pow 3]
  norm_num

lemma fSum_three_pow_four : fSum (3 ^ 4) = (85583 : ℚ) / 62920 := by
  rw [fSum_prime_pow Nat.prime_three, sum_range_succ, sum_range_succ, sum_range_succ,
    sum_range_succ, sum_range_one]
  rw [pow_zero, sigma_one, pow_one, sigma_prime Nat.prime_three]
  rw [sigma_three_pow 2, sigma_three_pow 3, sigma_three_pow 4]
  norm_num

lemma den_ne_one_of_mem_Ioo_ne_two {q : ℚ}
    (h1 : 1 < q) (h3 : q < 3) (hne : q ≠ 2) : q.den ≠ 1 := by
  intro hd
  have hq : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hd
  rw [← hq] at h1 h3 hne
  have h1z : (1 : ℤ) < q.num := by exact_mod_cast h1
  have h3z : (q.num : ℤ) < 3 := by exact_mod_cast h3
  have hne2 : q.num ≠ 2 := by
    intro h
    apply hne
    exact_mod_cast h
  omega

lemma fSum_two_pow_mul_three_pow_not_int (a k : ℕ) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    (fSum (2 ^ a) * fSum (3 ^ k)).den ≠ 1 := by
  have hgt : 1 < fSum (2 ^ a) * fSum (3 ^ k) := by
    have h1 := fSum_two_pow_gt_one ha
    have h2 : 1 < fSum (3 ^ k) := fSum_gt_one (Nat.one_lt_pow (by omega) (by decide))
    nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
      fSum_pos (pow_ne_zero k (by decide : 3 ≠ 0))]
  have h3lt := fSum_three_pow_lt_three_halves k
  have h2lt := fSum_two_pow_lt_13_8 a
  have hprod_lt3 : fSum (2 ^ a) * fSum (3 ^ k) < 3 := by
    have : (13 : ℚ) / 8 * (3 / 2) < 3 := by norm_num
    nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
      fSum_pos (pow_ne_zero k (by decide : 3 ≠ 0))]
  have hne2 : fSum (2 ^ a) * fSum (3 ^ k) ≠ 2 := by
    cases lt_or_ge a 3 with
    | inl ha3 =>
      have ha12 : a = 1 ∨ a = 2 := by omega
      cases ha12 with
      | inl h =>
        subst h
        have h2eq : fSum (2 ^ 1) = (4 : ℚ) / 3 := by rw [pow_one, fSum_two]
        rw [h2eq]
        have : (4 : ℚ) / 3 * fSum (3 ^ k) < 2 := by nlinarith
        exact ne_of_lt this
      | inr h =>
        subst h
        have h4 := fSum_four
        intro heq
        have hsk : fSum (3 ^ k) = (42 : ℚ) / 31 := by
          rw [h4] at heq
          field_simp at heq
          linarith
        cases lt_or_ge k 4 with
        | inl hk4 =>
          interval_cases k
          · have : fSum (3 ^ 1) = (5 : ℚ) / 4 := by rw [pow_one, fSum_three]
            rw [this] at hsk; norm_num at hsk
          · rw [fSum_nine] at hsk; norm_num at hsk
          · rw [fSum_three_pow_three] at hsk; norm_num at hsk
        | inr hk4 =>
          have hgt' : (42 : ℚ) / 31 < fSum (3 ^ 4) := by
            rw [fSum_three_pow_four]; norm_num
          have hmono : fSum (3 ^ 4) ≤ fSum (3 ^ k) := by
            cases Nat.lt_or_eq_of_le hk4 with
            | inl hlt => exact (fSum_strict_mono_prime_pow Nat.prime_three hlt).le
            | inr heq' => rw [heq']
          exact (not_le_of_gt hgt' (hsk ▸ hmono)).elim
    | inr ha3 =>
      cases lt_or_ge k 2 with
      | inl hk2 =>
        have : k = 1 := by omega
        subst this
        intro heq
        have : fSum (2 ^ a) = (8 : ℚ) / 5 := by
          rw [pow_one, fSum_three] at heq
          field_simp at heq
          linarith
        exact fSum_two_pow_ne_eight_five a this
      | inr hk2 =>
        intro heq
        have h8 : fSum (2 ^ 3) ≤ fSum (2 ^ a) := by
          cases Nat.lt_or_eq_of_le ha3 with
          | inl h => exact (fSum_strict_mono_two h).le
          | inr h => rw [h]
        have h9 : fSum (3 ^ 2) ≤ fSum (3 ^ k) := by
          cases Nat.lt_or_eq_of_le hk2 with
          | inl h => exact (fSum_strict_mono_prime_pow Nat.prime_three h).le
          | inr h => rw [h]
        have : 2 < fSum (2 ^ a) * fSum (3 ^ k) := by
          nlinarith [fSum_eight_mul_nine_gt_two,
            fSum_pos (pow_ne_zero a two_ne_zero),
            fSum_pos (pow_ne_zero k (by decide : 3 ≠ 0)),
            fSum_pos (pow_ne_zero (3 : ℕ) two_ne_zero),
            fSum_pos (show (3 : ℕ) ^ 2 ≠ 0 by decide)]
        linarith
  exact den_ne_one_of_mem_Ioo_ne_two hgt hprod_lt3 hne2

lemma odd_mod4 {n : ℕ} (h : Odd n) : n ≡ 1 [MOD 4] ∨ n ≡ 3 [MOD 4] := by
  have h2 : n % 2 = 1 := Nat.odd_iff.mp h
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by decide)
  have : n % 4 = 1 ∨ n % 4 = 3 := by omega
  cases this with
  | inl h => exact Or.inl (by simpa [Nat.ModEq] using h)
  | inr h => exact Or.inr (by simpa [Nat.ModEq] using h)

lemma padicValNat_two_add_one_of_mod4_one {p : ℕ} (hodd : Odd p)
    (h : p ≡ 1 [MOD 4]) : padicValNat 2 (p + 1) = 1 := by
  haveI := two_fact
  have hmod : (p + 1) % 4 = 2 := by
    have : p % 4 = 1 := by simpa [Nat.ModEq] using h
    omega
  have hdiv2 : 2 ∣ p + 1 := by omega
  have hndiv4 : ¬ 4 ∣ p + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hpos : p + 1 ≠ 0 := by omega
  have hle : 1 ≤ padicValNat 2 (p + 1) :=
    one_le_padicValNat_of_dvd hpos hdiv2
  have hlt : padicValNat 2 (p + 1) < 2 := by
    by_contra hge
    have : 2 ^ 2 ∣ p + 1 := by
      have : 2 ≤ padicValNat 2 (p + 1) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv4 (by simpa using this)
  omega

lemma log_two_of_ge_four {n : ℕ} (h : 4 ≤ n) : 2 ≤ Nat.log 2 n := by
  have : Nat.log 2 4 = 2 := by decide
  have : Nat.log 2 4 ≤ Nat.log 2 n := Nat.log_mono_right h
  omega

lemma v2_fSum_odd_prime_pow_mod4_one_small {p k : ℕ}
    (hp : p.Prime) (hodd : Odd p) (h : p ≡ 1 [MOD 4])
    (hk : k = 1 ∨ k = 2) :
    padicValRat 2 (fSum (p ^ k)) = -1 := by
  haveI := two_fact
  have hk1 : 1 ≤ k := by omega
  rw [padicValRat_two_fSum_odd_prime_pow hp hodd hk1]
  have hv : padicValNat 2 (p + 1) = 1 :=
    padicValNat_two_add_one_of_mod4_one hodd h
  have hlog : Nat.log 2 (k + 1) = 1 := by
    cases hk with
    | inl h => subst h; decide
    | inr h => subst h; decide
  omega

lemma v2_fSum_odd_prime_pow_exp_ge_three {p k : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hk : 3 ≤ k) :
    padicValRat 2 (fSum (p ^ k)) ≤ -2 := by
  haveI := two_fact
  have hk1 : 1 ≤ k := by omega
  rw [padicValRat_two_fSum_odd_prime_pow hp hodd hk1]
  have h1 : 1 ≤ padicValNat 2 (p + 1) :=
    one_le_padicValNat_of_dvd (by omega)
      (even_iff_two_dvd.mp (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)))
  have h2 : 2 ≤ Nat.log 2 (k + 1) := log_two_of_ge_four (by omega)
  omega

lemma eq_mul_prime_pows_of_card_eq_two {m : ℕ} (hm : m ≠ 0)
    (h : m.primeFactors.card = 2) :
    ∃ p q : ℕ, p ≠ q ∧ p.Prime ∧ q.Prime ∧
      m.primeFactors = {p, q} ∧
      m = p ^ m.factorization p * q ^ m.factorization q := by
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h
  have hp : p.Prime :=
    prime_of_mem_primeFactors (hs ▸ mem_insert_self p {q})
  have hq : q.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp [hpq])
  refine ⟨p, q, hpq, hp, hq, hs, ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Finsupp.prod, Nat.support_factorization, hs]
  rw [prod_insert (by simp [hpq]), prod_singleton]

lemma fSum_prime_sq {p : ℕ} (hp : p.Prime) :
    fSum (p ^ 2) =
      (1 : ℚ) + 1 / ((p : ℚ) + 1) + 1 / ((p : ℚ) ^ 2 + (p : ℚ) + 1) := by
  rw [fSum_prime_pow hp, sum_range_succ, sum_range_succ, sum_range_one]
  rw [pow_zero, sigma_one, pow_one, sigma_prime hp]
  have hs : sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    rw [sigma_eq_geom hp]
    simp [sum_range_succ, pow_zero, pow_one]
  rw [hs]
  push_cast
  ring

lemma fSum_prime_sq_anti {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≤ q) :
    fSum (q ^ 2) ≤ fSum (p ^ 2) := by
  rw [fSum_prime_sq hp, fSum_prime_sq hq]
  have hp0 : (0 : ℚ) < (p : ℚ) + 1 := by positivity
  have hq0 : (0 : ℚ) < (q : ℚ) + 1 := by positivity
  have h1 : (1 : ℚ) / ((q : ℚ) + 1) ≤ 1 / ((p : ℚ) + 1) := by
    refine one_div_le_one_div_of_le hp0 ?_
    linarith [show (p : ℚ) ≤ (q : ℚ) by exact_mod_cast h]
  have hsq : (p : ℚ) ^ 2 + (p : ℚ) + 1 ≤ (q : ℚ) ^ 2 + (q : ℚ) + 1 := by
    have hpq : (p : ℚ) ≤ q := by exact_mod_cast h
    nlinarith [sq_nonneg ((p : ℚ)), sq_nonneg ((q : ℚ)),
      show (0 : ℚ) ≤ p by exact_mod_cast (Nat.zero_le p)]
  have hp2 : (0 : ℚ) < (p : ℚ) ^ 2 + (p : ℚ) + 1 := by positivity
  have h2 : (1 : ℚ) / ((q : ℚ) ^ 2 + (q : ℚ) + 1) ≤
      1 / ((p : ℚ) ^ 2 + (p : ℚ) + 1) :=
    one_div_le_one_div_of_le hp2 hsq
  linarith

lemma fSum_le_sq_of_exp_le_two {p k : ℕ} (hp : p.Prime)
    (hk : k = 1 ∨ k = 2) : fSum (p ^ k) ≤ fSum (p ^ 2) := by
  cases hk with
  | inl h =>
    subst h
    simpa [pow_one] using
      (fSum_strict_mono_prime_pow hp (by decide : (1 : ℕ) < 2)).le
  | inr h =>
    subst h
    exact le_rfl

lemma fSum_five : fSum 5 = (7 : ℚ) / 6 := by
  rw [fSum_prime (show Nat.Prime 5 by decide)]
  norm_num

lemma fSum_thirteen : fSum 13 = (15 : ℚ) / 14 := by
  rw [fSum_prime (show Nat.Prime 13 by decide)]
  norm_num

lemma fSum_seventeen : fSum 17 = (19 : ℚ) / 18 := by
  rw [fSum_prime (show Nat.Prime 17 by decide)]
  norm_num

lemma fSum_five_sq : fSum (5 ^ 2) = (223 : ℚ) / 186 := by
  rw [fSum_prime_sq (show Nat.Prime 5 by decide)]
  norm_num

lemma fSum_thirteen_sq : fSum (13 ^ 2) = (2759 : ℚ) / 2562 := by
  rw [fSum_prime_sq (show Nat.Prime 13 by decide)]
  norm_num

lemma fSum_seventeen_sq : fSum (17 ^ 2) = (5851 : ℚ) / 5526 := by
  rw [fSum_prime_sq (show Nat.Prime 17 by decide)]
  norm_num

lemma fSum_twenty_nine_sq : fSum (29 ^ 2) = (27031 : ℚ) / 26130 := by
  rw [fSum_prime_sq (show Nat.Prime 29 by decide)]
  norm_num

lemma fSum_two_pow_five : fSum (2 ^ 5) = (15536 : ℚ) / 9765 := by
  rw [fSum_two_pow_eq]
  simp [sum_range_succ]
  norm_num

lemma fSum_two_pow_lt_161_100 (a : ℕ) : fSum (2 ^ a) < (161 : ℚ) / 100 := by
  cases lt_or_ge a 8 with
  | inl hlt =>
    have hle : fSum (2 ^ a) ≤ fSum (2 ^ 7) := by
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with
      | inl h => exact (fSum_strict_mono_two h).le
      | inr h => rw [h]
    have h7lt : fSum (2 ^ 7) < (161 : ℚ) / 100 := by
      rw [fSum_two_pow_seven]; norm_num
    exact lt_of_le_of_lt hle h7lt
  | inr hge =>
    have h8 : 8 ≤ a + 1 := by omega
    have hsplit :
        fSum (2 ^ a) =
          fSum (2 ^ 7) +
            ∑ k ∈ Ico 8 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
      rw [fSum_two_pow_eq, fSum_two_pow_eq]
      simpa using
        (sum_range_add_sum_Ico
          (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) h8).symm
    have hsplit2 :
        ∑ k ∈ Ico 8 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) =
          (1 : ℚ) / ((2 ^ 9 - 1 : ℕ) : ℚ) +
            ∑ k ∈ Ico 9 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
      have : Ico 8 (a + 1) = insert 8 (Ico 9 (a + 1)) := by
        ext x; simp [mem_Ico]; omega
      rw [this, sum_insert (by simp [mem_Ico])]
    have htail :
        ∑ k ∈ Ico 9 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) <
          (1 : ℚ) / 256 := by
      have hle :
          ∑ k ∈ Ico 9 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≤
            ∑ k ∈ Ico 9 (a + 1), (1 / 2 : ℚ) ^ k := by
        refine sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := by
          have : 9 ≤ k := (mem_Ico.mp hk).1
          omega
        have hcmp := (mersenne_recip_lt hk1).le
        have hcast : ((2 ^ k : ℕ) : ℚ) = (2 : ℚ) ^ k := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
        have : (1 : ℚ) / ((2 ^ k : ℕ) : ℚ) = (1 / 2 : ℚ) ^ k := by
          rw [hcast, div_pow, one_pow]
        rw [this] at hcmp
        exact hcmp
      have hgeom :
          ∑ k ∈ Ico 9 (a + 1), (1 / 2 : ℚ) ^ k < (1 : ℚ) / 256 := by
        rw [sum_Ico_eq_sum_range]
        have hfac :
            ∑ i ∈ range (a + 1 - 9), (1 / 2 : ℚ) ^ (9 + i) =
              (1 / 2 : ℚ) ^ 9 *
                ∑ i ∈ range (a + 1 - 9), (1 / 2 : ℚ) ^ i := by
          refine (sum_congr rfl fun i _ => ?_).trans (mul_sum _ _ _).symm
          rw [pow_add]
        rw [hfac]
        have hgs := geom_sum_half_lt (a + 1 - 9)
        have : (1 / 2 : ℚ) ^ 9 = 1 / 512 := by norm_num
        nlinarith
      linarith
    have h7 := fSum_two_pow_seven
    have : (33790906 : ℚ) / 21082635 + 1 / 511 + 1 / 256 < (161 : ℚ) / 100 := by
      norm_num
    have hterm : (1 : ℚ) / ((2 ^ 9 - 1 : ℕ) : ℚ) = 1 / 511 := by norm_num
    linarith

lemma prime_one_mod_four_cases {q : ℕ} (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) :
    q = 5 ∨ q = 13 ∨ q = 17 ∨ 29 ≤ q := by
  have h2 : q ≠ 2 := by
    intro h
    have : (2 : ℕ) % 4 = 1 := by simpa [h, Nat.ModEq] using h1
    norm_num at this
  have h3 : q ≠ 3 := by
    intro h
    have : (3 : ℕ) % 4 = 1 := by simpa [h, Nat.ModEq] using h1
    norm_num at this
  have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three h2 h3
  by_cases h29 : 29 ≤ q
  · exact Or.inr (Or.inr (Or.inr h29))
  · have : q < 29 := by omega
    interval_cases q
    · exact Or.inl rfl -- 5
    · exact absurd hq (by decide) -- 6
    · simp [Nat.ModEq] at h1 -- 7
    · exact absurd hq (by decide) -- 8
    · exact absurd hq (by decide) -- 9
    · exact absurd hq (by decide) -- 10
    · simp [Nat.ModEq] at h1 -- 11
    · exact absurd hq (by decide) -- 12
    · exact Or.inr (Or.inl rfl) -- 13
    · exact absurd hq (by decide) -- 14
    · exact absurd hq (by decide) -- 15
    · exact absurd hq (by decide) -- 16
    · exact Or.inr (Or.inr (Or.inl rfl)) -- 17
    · exact absurd hq (by decide) -- 18
    · simp [Nat.ModEq] at h1 -- 19
    · exact absurd hq (by decide) -- 20
    · exact absurd hq (by decide) -- 21
    · exact absurd hq (by decide) -- 22
    · simp [Nat.ModEq] at h1 -- 23
    · exact absurd hq (by decide) -- 24
    · exact absurd hq (by decide) -- 25
    · exact absurd hq (by decide) -- 26
    · exact absurd hq (by decide) -- 27
    · exact absurd hq (by decide) -- 28

lemma fSum_two_mul_two_prime_pows_lt_three {a p k q l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) :
    fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) < 3 := by
  have h1 := fSum_two_pow_lt_13_8 a
  have h2 := fSum_prime_pow_lt_73_60 p k hp hp5
  have h3 := fSum_prime_pow_lt_73_60 q l hq hq5
  have hp1 : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hp2 : 0 < fSum (p ^ k) := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hp3 : 0 < fSum (q ^ l) := fSum_pos (pow_ne_zero l hq.ne_zero)
  have h12 : fSum (2 ^ a) * fSum (p ^ k) < (13 : ℚ) / 8 * (73 / 60) :=
    mul_lt_mul'' h1 h2 hp1.le hp2.le
  have h123 : fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) <
      (13 : ℚ) / 8 * (73 / 60) * (73 / 60) :=
    mul_lt_mul'' h12 h3 (mul_nonneg hp1.le hp2.le) hp3.le
  have : (13 : ℚ) / 8 * (73 / 60) * (73 / 60) < 3 := by norm_num
  linarith

lemma fSum_two_mul_two_prime_pows_gt_one {a p k q l : ℕ}
    (ha : 1 ≤ a) (hp : p.Prime) (hq : q.Prime) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    1 < fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) := by
  have h1 := fSum_two_pow_gt_one ha
  have h2 : 1 < fSum (p ^ k) := fSum_gt_one (Nat.one_lt_pow (by omega) hp.one_lt)
  have h3 : 1 < fSum (q ^ l) := fSum_gt_one (Nat.one_lt_pow (by omega) hq.one_lt)
  have hp1 : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hp2 : 0 < fSum (p ^ k) := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hp3 : 0 < fSum (q ^ l) := fSum_pos (pow_ne_zero l hq.ne_zero)
  have h12 : 1 < fSum (2 ^ a) * fSum (p ^ k) := by nlinarith
  nlinarith

lemma mul3_lt_of {A B C X Y Z : ℚ}
    (hAX : A < X) (hBY : B ≤ Y) (hCZ : C ≤ Z)
    (hB : 0 < B) (hX : 0 ≤ X) (hC : 0 < C) (hXY : 0 ≤ X * Y) :
    A * B * C < X * Y * Z := by
  have hAB : A * B < X * Y := mul_lt_mul hAX hBY hB hX
  exact mul_lt_mul hAB hCZ hC hXY

lemma mul3_gt_of {A B C X Y Z : ℚ}
    (hXA : X ≤ A) (hYB : Y ≤ B) (hZC : Z ≤ C)
    (hY : 0 ≤ Y) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hAB : 0 ≤ A * B) :
    X * Y * Z ≤ A * B * C := by
  have hXY : X * Y ≤ A * B := mul_le_mul hXA hYB hY hA
  exact mul_le_mul hXY hZC hZ hAB

lemma five_le_of_mod4_one {p : ℕ} (hp : p.Prime) (h1 : p ≡ 1 [MOD 4]) : 5 ≤ p := by
  have h2 : p ≠ 2 := by
    intro h; have : (2 : ℕ) % 4 = 1 := by simpa [h, Nat.ModEq] using h1
    norm_num at this
  have h3 : p ≠ 3 := by
    intro h; have : (3 : ℕ) % 4 = 1 := by simpa [h, Nat.ModEq] using h1
    norm_num at this
  exact hp.five_le_of_ne_two_of_ne_three h2 h3

lemma fSum_ge_prime {p k : ℕ} (hp : p.Prime) (hk : k = 1 ∨ k = 2) :
    fSum p ≤ fSum (p ^ k) := by
  cases hk with
  | inl h => subst h; rw [pow_one]
  | inr h =>
    subst h
    simpa [pow_one] using
      (fSum_strict_mono_prime_pow hp (by decide : (1 : ℕ) < 2)).le

lemma fSum_two_pow_mul_two_mod4_one_ne_two {a p k q l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp1 : p ≡ 1 [MOD 4]) (hq1 : q ≡ 1 [MOD 4])
    (hpk : k = 1 ∨ k = 2) (hql : l = 1 ∨ l = 2)
    (ha5 : a ≡ 5 [MOD 8]) :
    fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) ≠ 2 := by
  have hp5 : 5 ≤ p := five_le_of_mod4_one hp hp1
  have hq5 : 5 ≤ q := five_le_of_mod4_one hq hq1
  have hpcases := prime_one_mod_four_cases hp hp1
  have hqcases := prime_one_mod_four_cases hq hq1
  have hbound := fSum_two_pow_lt_161_100 a
  have hple : fSum (p ^ k) ≤ fSum (p ^ 2) := fSum_le_sq_of_exp_le_two hp hpk
  have hqle : fSum (q ^ l) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hql
  have hppos : 0 < fSum (p ^ k) := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hqpos : 0 < fSum (q ^ l) := fSum_pos (pow_ne_zero l hq.ne_zero)
  have h2pos : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have h5P : Nat.Prime 5 := by decide
  have h13P : Nat.Prime 13 := by decide
  have h17P : Nat.Prime 17 := by decide
  have h29P : Nat.Prime 29 := by decide
  have ha_mod : a % 8 = 5 := by simpa [Nat.ModEq] using ha5
  have ha5le : 5 ≤ a := by omega
  have hge13 : 13 ≤ p → 13 ≤ q →
      fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) < 2 := by
    intro hp13 hq13
    have hpair : fSum (p ^ 2) * fSum (q ^ 2) ≤ fSum (13 ^ 2) * fSum (17 ^ 2) := by
      cases lt_or_gt_of_ne hpq with
      | inl hlt =>
        have hq17 : 17 ≤ q := by omega
        exact mul_le_mul
          (fSum_prime_sq_anti h13P hp hp13)
          (fSum_prime_sq_anti h17P hq hq17)
          (fSum_pos (pow_ne_zero 2 hq.ne_zero)).le
          (fSum_pos (pow_ne_zero 2 h13P.ne_zero)).le
      | inr hgt =>
        have hp17 : 17 ≤ p := by omega
        have := mul_le_mul
          (fSum_prime_sq_anti h13P hq hq13)
          (fSum_prime_sq_anti h17P hp hp17)
          (fSum_pos (pow_ne_zero 2 hp.ne_zero)).le
          (fSum_pos (pow_ne_zero 2 h13P.ne_zero)).le
        linarith
    have hXYZ : (161 : ℚ) / 100 * fSum (13 ^ 2) * fSum (17 ^ 2) < 2 := by
      rw [fSum_thirteen_sq, fSum_seventeen_sq]; norm_num
    have hBC : fSum (p ^ k) * fSum (q ^ l) ≤ fSum (13 ^ 2) * fSum (17 ^ 2) :=
      le_trans (mul_le_mul hple hqle hqpos.le
        (fSum_pos (pow_ne_zero 2 hp.ne_zero)).le) hpair
    have hmul : fSum (2 ^ a) * (fSum (p ^ k) * fSum (q ^ l)) <
        (161 : ℚ) / 100 * (fSum (13 ^ 2) * fSum (17 ^ 2)) :=
      mul_lt_mul hbound hBC (mul_pos hppos hqpos) (by positivity)
    have hassoc : fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) =
        fSum (2 ^ a) * (fSum (p ^ k) * fSum (q ^ l)) := by ring
    have hassoc' : (161 : ℚ) / 100 * fSum (13 ^ 2) * fSum (17 ^ 2) =
        (161 : ℚ) / 100 * (fSum (13 ^ 2) * fSum (17 ^ 2)) := by ring
    linarith
  have hfive_left : ∀ (q k l : ℕ), q.Prime → q ≡ 1 [MOD 4] → q ≠ 5 →
      (k = 1 ∨ k = 2) → (l = 1 ∨ l = 2) →
      fSum (2 ^ a) * fSum (5 ^ k) * fSum (q ^ l) ≠ 2 := by
    intro q k l hq' hq1' hqne hk' hl'
    have hqcases' := prime_one_mod_four_cases hq' hq1'
    rcases hqcases' with hq5eq | hq13eq | hq17eq | hq29
    · exact (hqne hq5eq).elim
    · subst hq13eq
      cases lt_or_ge a 13 with
      | inl halt =>
        have haeq : a = 5 := by omega
        subst haeq
        cases hk' with
        | inl hk1 =>
          subst hk1
          have hlt : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (13 ^ l) < 2 := by
            have hC : fSum (13 ^ l) ≤ fSum (13 ^ 2) :=
              fSum_le_sq_of_exp_le_two h13P hl'
            rw [pow_one, fSum_two_pow_five, fSum_five]
            have hXYZ' : (15536 : ℚ) / 9765 * (7 / 6) * fSum (13 ^ 2) < 2 := by
              rw [fSum_thirteen_sq]; norm_num
            have : (15536 : ℚ) / 9765 * (7 / 6) * fSum (13 ^ l) ≤
                (15536 : ℚ) / 9765 * (7 / 6) * fSum (13 ^ 2) :=
              mul_le_mul_of_nonneg_left hC (by positivity)
            linarith
          exact ne_of_lt hlt
        | inr hk2 =>
          subst hk2
          have hgt : 2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (13 ^ l) := by
            have hC : fSum 13 ≤ fSum (13 ^ l) := fSum_ge_prime h13P hl'
            have hXYZ : 2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 13 := by
              rw [fSum_two_pow_five, fSum_five_sq, fSum_thirteen]; norm_num
            have hle := mul3_gt_of le_rfl le_rfl hC
              (fSum_pos (pow_ne_zero 2 h5P.ne_zero)).le
              (fSum_pos (pow_ne_zero 5 two_ne_zero)).le
              (fSum_pos (show (13 : ℕ) ≠ 0 by decide)).le
              (mul_nonneg (fSum_pos (pow_ne_zero 5 two_ne_zero)).le
                (fSum_pos (pow_ne_zero 2 h5P.ne_zero)).le)
            linarith
          exact ne_of_gt hgt
      | inr hage =>
        have h27 : fSum (2 ^ 7) ≤ fSum (2 ^ a) :=
          (fSum_strict_mono_two (by omega : (7 : ℕ) < a)).le
        have h5le : fSum 5 ≤ fSum (5 ^ k) := fSum_ge_prime h5P hk'
        have h13le : fSum 13 ≤ fSum (13 ^ l) := fSum_ge_prime h13P hl'
        have hXYZ : 2 < fSum (2 ^ 7) * fSum 5 * fSum 13 := by
          have := fSum_two_seven_gt_eight_five
          rw [fSum_five, fSum_thirteen]
          have h12 : (8 : ℚ) / 5 * (7 / 6) < fSum (2 ^ 7) * (7 / 6) :=
            mul_lt_mul this le_rfl (by positivity) (by positivity)
          have : (8 : ℚ) / 5 * (7 / 6) * (15 / 14) = 2 := by norm_num
          have h123 : (8 : ℚ) / 5 * (7 / 6) * (15 / 14) <
              fSum (2 ^ 7) * (7 / 6) * (15 / 14) :=
            mul_lt_mul h12 le_rfl (by positivity) (by positivity)
          linarith
        have hle := mul3_gt_of h27 h5le h13le
          (fSum_pos (show (5 : ℕ) ≠ 0 by decide)).le
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (show (13 : ℕ) ≠ 0 by decide)).le
          (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
            (fSum_pos (pow_ne_zero k (show (5 : ℕ) ≠ 0 by decide))).le)
        exact ne_of_gt (lt_of_lt_of_le hXYZ hle)
    · subst hq17eq
      cases hk' with
      | inl hk1 =>
        subst hk1
        have hC : fSum (17 ^ l) ≤ fSum (17 ^ 2) :=
          fSum_le_sq_of_exp_le_two h17P hl'
        have hXYZ : (161 : ℚ) / 100 * fSum 5 * fSum (17 ^ 2) < 2 := by
          rw [fSum_five, fSum_seventeen_sq]; norm_num
        have hmul : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ l) <
            (161 : ℚ) / 100 * fSum 5 * fSum (17 ^ 2) := by
          rw [pow_one]
          exact mul3_lt_of hbound le_rfl hC
            (fSum_pos (show (5 : ℕ) ≠ 0 by decide))
            (by norm_num)
            (fSum_pos (pow_ne_zero l hq'.ne_zero))
            (mul_nonneg (by norm_num) (fSum_pos (show (5 : ℕ) ≠ 0 by decide)).le)
        exact ne_of_lt (hXYZ.trans_le' hmul.le)
      | inr hk2 =>
        subst hk2
        have h25 : fSum (2 ^ 5) ≤ fSum (2 ^ a) := by
          cases Nat.lt_or_eq_of_le ha5le with
          | inl h => exact (fSum_strict_mono_two h).le
          | inr h => rw [h]
        have h17le : fSum 17 ≤ fSum (17 ^ l) := fSum_ge_prime h17P hl'
        have hXYZ : 2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 17 := by
          rw [fSum_two_pow_five, fSum_five_sq, fSum_seventeen]; norm_num
        have hle := mul3_gt_of h25 le_rfl h17le
          (fSum_pos (pow_ne_zero 2 h5P.ne_zero)).le
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (show (17 : ℕ) ≠ 0 by decide)).le
          (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
            (fSum_pos (pow_ne_zero 2 h5P.ne_zero)).le)
        exact ne_of_gt (lt_of_lt_of_le hXYZ hle)
    · have hqs : fSum (q ^ 2) ≤ fSum (29 ^ 2) :=
        fSum_prime_sq_anti h29P hq' hq29
      have hC : fSum (q ^ l) ≤ fSum (29 ^ 2) := le_trans
        (fSum_le_sq_of_exp_le_two hq' hl') hqs
      have hB : fSum (5 ^ k) ≤ fSum (5 ^ 2) := fSum_le_sq_of_exp_le_two h5P hk'
      have hXYZ : (161 : ℚ) / 100 * fSum (5 ^ 2) * fSum (29 ^ 2) < 2 := by
        rw [fSum_five_sq, fSum_twenty_nine_sq]; norm_num
      have hmul := mul3_lt_of hbound hB hC
        (fSum_pos (pow_ne_zero k (show (5 : ℕ) ≠ 0 by decide)))
        (by norm_num)
        (fSum_pos (pow_ne_zero l hq'.ne_zero))
        (mul_nonneg (by norm_num) (fSum_pos (pow_ne_zero 2 h5P.ne_zero)).le)
      exact ne_of_lt (lt_trans hmul hXYZ)
  by_cases hp_is5 : p = 5
  · subst hp_is5
    exact hfive_left q k l hq hq1 hpq.symm hpk hql
  · by_cases hq_is5 : q = 5
    · subst hq_is5
      have hswap : fSum (2 ^ a) * fSum (p ^ k) * fSum (5 ^ l) =
          fSum (2 ^ a) * fSum (5 ^ l) * fSum (p ^ k) := by ring
      rw [hswap]
      exact hfive_left p l k hp hp1 hpq hql hpk
    · have hp13 : 13 ≤ p := by
        rcases hpcases with h | h | h | h
        · exact (hp_is5 h).elim
        · omega
        · omega
        · omega
      have hq13 : 13 ≤ q := by
        rcases hqcases with h | h | h | h
        · exact (hq_is5 h).elim
        · omega
        · omega
        · omega
      exact ne_of_lt (hge13 hp13 hq13)

lemma two_pow_ge_four_zmod16 (t : ℕ) (ht : 4 ≤ t) :
    ((2 ^ t : ℕ) : ZMod 16) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
  rw [show t = 4 + k from hk, pow_add, Nat.cast_mul]
  have : ((2 ^ 4 : ℕ) : ZMod 16) = 0 := by decide
  rw [this, zero_mul]

lemma mersenne_zmod16_of_ge_three {k : ℕ} (hk : 3 ≤ k) :
    ((2 ^ (k + 1) - 1 : ℕ) : ZMod 16) = 15 := by
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [Nat.cast_sub hle]
  have : ((2 ^ (k + 1) : ℕ) : ZMod 16) = 0 :=
    two_pow_ge_four_zmod16 (k + 1) (by omega)
  rw [this]
  decide

lemma twoPowDen_zmod16_of_mod16_thirteen {a : ℕ} (h : a ≡ 13 [MOD 16]) :
    (twoPowDen a : ZMod 16) = 11 := by
  have ha : a % 16 = 13 := by simpa [Nat.ModEq] using h
  have hage : 13 ≤ a := by omega
  rw [twoPowDen]
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  rw [← mul_prod_erase _ _ h0, Nat.cast_mul]
  have hd0 : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 16) = 1 := by decide
  rw [hd0, one_mul]
  have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h1e, Nat.cast_mul]
  have hd1 : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 16) = 3 := by decide
  rw [hd1]
  have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h2e, Nat.cast_mul]
  have hd2 : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 16) = 7 := by decide
  rw [hd2]
  have hrest : ∀ k ∈ (((range (a + 1)).erase 0).erase 1).erase 2,
      ((2 ^ (k + 1) - 1 : ℕ) : ZMod 16) = 15 := by
    intro k hk
    have hk3 : 3 ≤ k := by simp [mem_erase] at hk; omega
    exact mersenne_zmod16_of_ge_three hk3
  have hcard : ((((range (a + 1)).erase 0).erase 1).erase 2).card = a - 2 := by
    rw [card_erase_of_mem h2e, card_erase_of_mem h1e, card_erase_of_mem h0,
      card_range]
    omega
  have hprod : ((∏ k ∈ (((range (a + 1)).erase 0).erase 1).erase 2,
      (2 ^ (k + 1) - 1) : ℕ) : ZMod 16) = 15 := by
    rw [Nat.cast_prod, prod_congr rfl hrest, prod_const, hcard]
    have : (15 : ZMod 16) = -1 := by decide
    rw [this]
    have hodd : Odd (a - 2) := by rw [Nat.odd_iff]; omega
    rw [hodd.neg_one_pow]
  rw [hprod]
  decide

lemma twoPowNum_zmod16_of_mod16_thirteen {a : ℕ} (h : a ≡ 13 [MOD 16]) :
    twoPowNum a % 16 = 8 := by
  have ha : a % 16 = 13 := by simpa [Nat.ModEq] using h
  have hage : 13 ≤ a := by omega
  have hV : (twoPowDen a : ZMod 16) = 11 :=
    twoPowDen_zmod16_of_mod16_thirteen h
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 16) = 11 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 16) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 16) = 9 := by
    have hdvd := twoPowDen_dvd a 1 h1
    have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 16) * 11 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 16) = 13 := by
    have hdvd := twoPowDen_dvd a 2 h2
    have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 16) * 7 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hsum : (twoPowNum a : ZMod 16) = 8 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h1e, hterm1]
    have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h2e, hterm2]
    have htermk : ∀ k ∈ (((range (a + 1)).erase 0).erase 1).erase 2,
        ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 16) = 5 := by
      intro k hk
      have hk3 : 3 ≤ k := by simp [mem_erase] at hk; omega
      have hkmem : k ∈ range (a + 1) := by
        simp [mem_erase] at hk; simp [mem_range]; omega
      have hdvd := twoPowDen_dvd a k hkmem
      have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 16) = 15 :=
        mersenne_zmod16_of_ge_three hk3
      have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 16) * 15 = 1 := by
        rw [hd]; decide
      rw [nat_div_cast_mul_inv hdvd hu, hV]
      decide
    rw [sum_congr rfl htermk, sum_const]
    have hcard : ((((range (a + 1)).erase 0).erase 1).erase 2).card = a - 2 := by
      rw [card_erase_of_mem h2e, card_erase_of_mem h1e, card_erase_of_mem h0,
        card_range]
      omega
    rw [hcard, nsmul_eq_mul]
    have ha2 : ((a - 2 : ℕ) : ZMod 16) = 11 := by
      have : (a - 2) % 16 = 11 := by omega
      rw [← Nat.cast_ofNat (n := 11), ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using this
    rw [ha2]
    decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (8 : ZMod 16).val = 8 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod16_thirteen {a : ℕ} (h : a ≡ 13 [MOD 16]) :
    padicValRat 2 (fSum (2 ^ a)) = 3 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 16 = 8 := twoPowNum_zmod16_of_mod16_thirteen h
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have hdiv8 : 8 ∣ twoPowNum a :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hndiv16 : ¬ 16 ∣ twoPowNum a := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hle : 3 ≤ padicValNat 2 (twoPowNum a) := by
    have : 2 ^ 3 ∣ twoPowNum a := by simpa using hdiv8
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 (twoPowNum a) < 4 := by
    by_contra hge
    have : 2 ^ 4 ∣ twoPowNum a := by
      have : 4 ≤ padicValNat 2 (twoPowNum a) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv16 (by simpa using this)
  have : padicValNat 2 (twoPowNum a) = 3 := by omega
  exact_mod_cast this

lemma two_pow_ge_five_zmod32 (t : ℕ) (ht : 5 ≤ t) :
    ((2 ^ t : ℕ) : ZMod 32) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
  rw [show t = 5 + k from hk, pow_add, Nat.cast_mul]
  have : ((2 ^ 5 : ℕ) : ZMod 32) = 0 := by decide
  rw [this, zero_mul]

lemma mersenne_zmod32_of_ge_four {k : ℕ} (hk : 4 ≤ k) :
    ((2 ^ (k + 1) - 1 : ℕ) : ZMod 32) = 31 := by
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [Nat.cast_sub hle]
  have : ((2 ^ (k + 1) : ℕ) : ZMod 32) = 0 :=
    two_pow_ge_five_zmod32 (k + 1) (by omega)
  rw [this]
  decide

lemma twoPowDen_zmod32_of_mod32_five {a : ℕ} (h : a ≡ 5 [MOD 32]) :
    (twoPowDen a : ZMod 32) = 27 := by
  have ha : a % 32 = 5 := by simpa [Nat.ModEq] using h
  have hage : 5 ≤ a := by omega
  rw [twoPowDen]
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  rw [← mul_prod_erase _ _ h0, Nat.cast_mul]
  have hd0 : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 32) = 1 := by decide
  rw [hd0, one_mul]
  have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h1e, Nat.cast_mul]
  have hd1 : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 32) = 3 := by decide
  rw [hd1]
  have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h2e, Nat.cast_mul]
  have hd2 : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 32) = 7 := by decide
  rw [hd2]
  have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h3e, Nat.cast_mul]
  have hd3 : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 32) = 15 := by decide
  rw [hd3]
  have hrest : ∀ k ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3,
      ((2 ^ (k + 1) - 1 : ℕ) : ZMod 32) = 31 := by
    intro k hk
    have hk4 : 4 ≤ k := by simp [mem_erase] at hk; omega
    exact mersenne_zmod32_of_ge_four hk4
  have hcard : (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).card =
      a - 3 := by
    rw [card_erase_of_mem h3e, card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem h0, card_range]
    omega
  have hprod : ((∏ k ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3,
      (2 ^ (k + 1) - 1) : ℕ) : ZMod 32) = 1 := by
    rw [Nat.cast_prod, prod_congr rfl hrest, prod_const, hcard]
    have : (31 : ZMod 32) = -1 := by decide
    rw [this]
    have heven : Even (a - 3) := by
      rw [Nat.even_iff]; omega
    rw [heven.neg_one_pow]
  rw [hprod]
  decide

lemma twoPowNum_zmod32_of_mod32_five {a : ℕ} (h : a ≡ 5 [MOD 32]) :
    twoPowNum a % 32 = 16 := by
  have ha : a % 32 = 5 := by simpa [Nat.ModEq] using h
  have hage : 5 ≤ a := by omega
  have hV : (twoPowDen a : ZMod 32) = 27 :=
    twoPowDen_zmod32_of_mod32_five h
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 32) = 27 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 32) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 32) = 9 := by
    have hdvd := twoPowDen_dvd a 1 h1
    have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 32) * 11 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 32) = 13 := by
    have hdvd := twoPowDen_dvd a 2 h2
    have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 32) * 23 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm3 : ((twoPowDen a / (2 ^ (3 + 1) - 1) : ℕ) : ZMod 32) = 21 := by
    have hdvd := twoPowDen_dvd a 3 h3
    have hu : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 32) * 15 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hsum : (twoPowNum a : ZMod 32) = 16 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h1e, hterm1]
    have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h2e, hterm2]
    have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h3e, hterm3]
    have htermk : ∀ k ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3,
        ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 32) = 5 := by
      intro k hk
      have hk4 : 4 ≤ k := by simp [mem_erase] at hk; omega
      have hkmem : k ∈ range (a + 1) := by
        simp [mem_erase] at hk; simp [mem_range]; omega
      have hdvd := twoPowDen_dvd a k hkmem
      have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 32) = 31 :=
        mersenne_zmod32_of_ge_four hk4
      have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 32) * 31 = 1 := by
        rw [hd]; decide
      rw [nat_div_cast_mul_inv hdvd hu, hV]
      decide
    rw [sum_congr rfl htermk, sum_const]
    have hcard : (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).card =
        a - 3 := by
      rw [card_erase_of_mem h3e, card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem h0, card_range]
      omega
    rw [hcard, nsmul_eq_mul]
    have ha3 : ((a - 3 : ℕ) : ZMod 32) = 2 := by
      have : (a - 3) % 32 = 2 := by omega
      rw [← Nat.cast_ofNat (n := 2), ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using this
    rw [ha3]
    decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (16 : ZMod 32).val = 16 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod32_five {a : ℕ} (h : a ≡ 5 [MOD 32]) :
    padicValRat 2 (fSum (2 ^ a)) = 4 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 32 = 16 := twoPowNum_zmod32_of_mod32_five h
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have hdiv16 : 16 ∣ twoPowNum a :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hndiv32 : ¬ 32 ∣ twoPowNum a := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hle : 4 ≤ padicValNat 2 (twoPowNum a) := by
    have : 2 ^ 4 ∣ twoPowNum a := by simpa using hdiv16
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 (twoPowNum a) < 5 := by
    by_contra hge
    have : 2 ^ 5 ∣ twoPowNum a := by
      have : 5 ≤ padicValNat 2 (twoPowNum a) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv32 (by simpa using this)
  have : padicValNat 2 (twoPowNum a) = 4 := by omega
  exact_mod_cast this

lemma twoPowNum_zmod16_of_mod16_five {a : ℕ} (h : a ≡ 5 [MOD 16]) :
    twoPowNum a % 16 = 0 := by
  have ha : a % 16 = 5 := by simpa [Nat.ModEq] using h
  have h32 : a % 32 = 5 ∨ a % 32 = 21 := by omega
  cases h32 with
  | inl h5 =>
    have : a ≡ 5 [MOD 32] := by simpa [Nat.ModEq] using h5
    have : twoPowNum a % 32 = 16 := twoPowNum_zmod32_of_mod32_five this
    omega
  | inr h21 =>
    -- a ≡ 21 [MOD 32] will be proved via a direct ZMod 32 computation below;
    -- for now deduce divisibility by 16 from the 32-adic pattern after that lemma.
    -- Placeholder replaced by a self-contained ZMod 16 argument.
    have hage : 5 ≤ a := by omega
    -- Use that a ≡ 5 [MOD 16] implies twoPowNum ≡ 0 [MOD 16] by the same
    -- expansion used for residue 13, with a-2 ≡ 3 [MOD 16].
    have hV16 : (twoPowDen a : ZMod 16) = 11 := by
      -- 1*3*7*15^{a-2}, a-2 ≡ 3 [MOD 16] is odd, so 15^{a-2} ≡ 15,
      -- 3*7*15 ≡ 11.
      rw [twoPowDen]
      have h0 : 0 ∈ range (a + 1) := by simp
      have h1 : 1 ∈ range (a + 1) := by simp; omega
      have h2 : 2 ∈ range (a + 1) := by simp; omega
      rw [← mul_prod_erase _ _ h0, Nat.cast_mul]
      have hd0 : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 16) = 1 := by decide
      rw [hd0, one_mul]
      have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
      rw [← mul_prod_erase _ _ h1e, Nat.cast_mul]
      have hd1 : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 16) = 3 := by decide
      rw [hd1]
      have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
        simp [mem_erase]; omega
      rw [← mul_prod_erase _ _ h2e, Nat.cast_mul]
      have hd2 : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 16) = 7 := by decide
      rw [hd2]
      have hrest : ∀ k ∈ (((range (a + 1)).erase 0).erase 1).erase 2,
          ((2 ^ (k + 1) - 1 : ℕ) : ZMod 16) = 15 := by
        intro k hk
        have hk3 : 3 ≤ k := by simp [mem_erase] at hk; omega
        exact mersenne_zmod16_of_ge_three hk3
      have hcard : ((((range (a + 1)).erase 0).erase 1).erase 2).card = a - 2 := by
        rw [card_erase_of_mem h2e, card_erase_of_mem h1e, card_erase_of_mem h0,
          card_range]
        omega
      have hprod : ((∏ k ∈ (((range (a + 1)).erase 0).erase 1).erase 2,
          (2 ^ (k + 1) - 1) : ℕ) : ZMod 16) = 15 := by
        rw [Nat.cast_prod, prod_congr rfl hrest, prod_const, hcard]
        have : (15 : ZMod 16) = -1 := by decide
        rw [this]
        have hodd : Odd (a - 2) := by rw [Nat.odd_iff]; omega
        rw [hodd.neg_one_pow]
      rw [hprod]
      decide
    have h0 : 0 ∈ range (a + 1) := by simp
    have h1 : 1 ∈ range (a + 1) := by simp; omega
    have h2 : 2 ∈ range (a + 1) := by simp; omega
    have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 16) = 11 := by
      have hdvd := twoPowDen_dvd a 0 h0
      have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 16) * 1 = 1 := by decide
      rw [nat_div_cast_mul_inv hdvd hu, hV16, mul_one]
    have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 16) = 9 := by
      have hdvd := twoPowDen_dvd a 1 h1
      have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 16) * 11 = 1 := by decide
      rw [nat_div_cast_mul_inv hdvd hu, hV16]
      decide
    have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 16) = 13 := by
      have hdvd := twoPowDen_dvd a 2 h2
      have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 16) * 7 = 1 := by decide
      rw [nat_div_cast_mul_inv hdvd hu, hV16]
      decide
    have hsum : (twoPowNum a : ZMod 16) = 0 := by
      rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
      have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
      rw [← add_sum_erase _ _ h1e, hterm1]
      have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
        simp [mem_erase]; omega
      rw [← add_sum_erase _ _ h2e, hterm2]
      have htermk : ∀ k ∈ (((range (a + 1)).erase 0).erase 1).erase 2,
          ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 16) = 5 := by
        intro k hk
        have hk3 : 3 ≤ k := by simp [mem_erase] at hk; omega
        have hkmem : k ∈ range (a + 1) := by
          simp [mem_erase] at hk; simp [mem_range]; omega
        have hdvd := twoPowDen_dvd a k hkmem
        have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 16) = 15 :=
          mersenne_zmod16_of_ge_three hk3
        have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 16) * 15 = 1 := by
          rw [hd]; decide
        rw [nat_div_cast_mul_inv hdvd hu, hV16]
        decide
      rw [sum_congr rfl htermk, sum_const]
      have hcard : ((((range (a + 1)).erase 0).erase 1).erase 2).card = a - 2 := by
        rw [card_erase_of_mem h2e, card_erase_of_mem h1e, card_erase_of_mem h0,
          card_range]
        omega
      rw [hcard, nsmul_eq_mul]
      have ha2 : ((a - 2 : ℕ) : ZMod 16) = 3 := by
        have : (a - 2) % 16 = 3 := by omega
        rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]
        simpa [Nat.ModEq] using this
      rw [ha2]
      decide
    have hval := congrArg ZMod.val hsum
    rw [ZMod.val_natCast] at hval
    have : (0 : ZMod 16).val = 0 := by decide
    rwa [this] at hval

lemma v2_fSum_two_pow_mod16_five {a : ℕ} (h : a ≡ 5 [MOD 16]) :
    4 ≤ padicValRat 2 (fSum (2 ^ a)) := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 16 = 0 := twoPowNum_zmod16_of_mod16_five h
  have hdiv : 16 ∣ twoPowNum a := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have : 2 ^ 4 ∣ twoPowNum a := by simpa using hdiv
  have : 4 ≤ padicValNat 2 (twoPowNum a) := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  exact_mod_cast this

lemma padicValRat_two_two : padicValRat 2 (2 : ℚ) = 1 := by
  haveI := two_fact
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
  simp [padicValNat_self]

lemma den_ne_one_of_lt_three_v2_ne_one {q : ℚ}
    (h1 : 1 < q) (h3 : q < 3)
    (hv : padicValRat 2 q ≠ 1) : q.den ≠ 1 := by
  intro hd
  have hq : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hd
  haveI := two_fact
  have h1z : (1 : ℤ) < q.num := by
    have : (1 : ℚ) < (q.num : ℚ) := by rw [hq]; exact h1
    exact_mod_cast this
  have h3z : (q.num : ℤ) < 3 := by
    have : (q.num : ℚ) < 3 := by rw [hq]; exact h3
    exact_mod_cast this
  have hnum : q.num = 2 := by omega
  have : padicValRat 2 q = 1 := by
    rw [← hq, hnum]
    exact padicValRat_two_two
  exact hv this

lemma fSum_two_three_prime_lt_three {a k p l : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) < 3 := by
  have h1 := fSum_two_pow_lt_13_8 a
  have h2 := fSum_three_pow_lt_three_halves k
  have h3 := fSum_prime_pow_lt_73_60 p l hp hp5
  have hp1 : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hp2 : 0 < fSum (3 ^ k) := fSum_pos (pow_ne_zero k (by decide : (3 : ℕ) ≠ 0))
  have hp3 : 0 < fSum (p ^ l) := fSum_pos (pow_ne_zero l hp.ne_zero)
  have h12 : fSum (2 ^ a) * fSum (3 ^ k) < (13 : ℚ) / 8 * (3 / 2) :=
    mul_lt_mul'' h1 h2 hp1.le hp2.le
  have h123 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) <
      (13 : ℚ) / 8 * (3 / 2) * (73 / 60) :=
    mul_lt_mul'' h12 h3 (mul_nonneg hp1.le hp2.le) hp3.le
  have : (13 : ℚ) / 8 * (3 / 2) * (73 / 60) < 3 := by norm_num
  linarith

lemma fSum_two_mul_two_prime_pows_lt_three' {a p k q l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) :
    fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) < 3 := by
  have hp2 : p ≠ 2 := by
    intro h; subst h; exact Nat.not_odd_iff_even.mpr even_two hpo
  have hq2 : q ≠ 2 := by
    intro h; subst h; exact Nat.not_odd_iff_even.mpr even_two hqo
  have hp3or : p = 3 ∨ 5 ≤ p := by
    have h2le : 2 ≤ p := hp.two_le
    have hodd : p % 2 = 1 := Nat.odd_iff.mp hpo
    omega
  have hq3or : q = 3 ∨ 5 ≤ q := by
    have h2le : 2 ≤ q := hq.two_le
    have hodd : q % 2 = 1 := Nat.odd_iff.mp hqo
    omega
  rcases hp3or with hp3 | hp5
  · subst hp3
    have hq5 : 5 ≤ q := by
      rcases hq3or with hq3 | hq5
      · exact (hpq hq3.symm).elim
      · exact hq5
    exact fSum_two_three_prime_lt_three hq hq5
  · rcases hq3or with hq3 | hq5
    · subst hq3
      have : fSum (2 ^ a) * fSum (p ^ k) * fSum (3 ^ l) =
          fSum (2 ^ a) * fSum (3 ^ l) * fSum (p ^ k) := by ring
      rw [this]
      exact fSum_two_three_prime_lt_three hp hp5
    · exact fSum_two_mul_two_prime_pows_lt_three hp hq hp5 hq5

/-- If `a ≡ 5 [MOD 8]` then `a ≡ 5 [MOD 16]` or `a ≡ 13 [MOD 16]`. -/
lemma mod8_five_of_mod16 {a : ℕ} (h : a ≡ 5 [MOD 8]) :
    a ≡ 5 [MOD 16] ∨ a ≡ 13 [MOD 16] := by
  have : a % 8 = 5 := by simpa [Nat.ModEq] using h
  have : a % 16 = 5 ∨ a % 16 = 13 := by
    have : a % 16 < 16 := Nat.mod_lt _ (by decide)
    omega
  cases this with
  | inl h => exact Or.inl (by simpa [Nat.ModEq] using h)
  | inr h => exact Or.inr (by simpa [Nat.ModEq] using h)

lemma fSum_three_prime_pows_lt_three {a p k q l r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hr5 : 5 ≤ r) :
    fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) * fSum (r ^ s) < 3 := by
  have hA := fSum_two_pow_lt_13_8 a
  have hB := fSum_prime_pow_lt_73_60 p k hp hp5
  have hC := fSum_prime_pow_lt_73_60 q l hq hq5
  have hD := fSum_prime_pow_lt_73_60 r s hr hr5
  have hAp : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hBp : 0 < fSum (p ^ k) := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hCp : 0 < fSum (q ^ l) := fSum_pos (pow_ne_zero l hq.ne_zero)
  have hDp : 0 < fSum (r ^ s) := fSum_pos (pow_ne_zero s hr.ne_zero)
  have hAB : fSum (2 ^ a) * fSum (p ^ k) < (13 : ℚ) / 8 * (73 / 60) :=
    mul_lt_mul'' hA hB hAp.le hBp.le
  have hABC : fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) <
      (13 : ℚ) / 8 * (73 / 60) * (73 / 60) :=
    mul_lt_mul'' hAB hC (mul_nonneg hAp.le hBp.le) hCp.le
  have hABCD : fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) * fSum (r ^ s) <
      (13 : ℚ) / 8 * (73 / 60) * (73 / 60) * (73 / 60) :=
    mul_lt_mul'' hABC hD
      (mul_nonneg (mul_nonneg hAp.le hBp.le) hCp.le) hDp.le
  have : (13 : ℚ) / 8 * (73 / 60) * (73 / 60) * (73 / 60) < 3 := by norm_num
  linarith

lemma odd_prime_ne_two {p : ℕ} (hp : p.Prime) (hpo : Odd p) : p ≠ 2 := by
  intro h; subst h; exact Nat.not_odd_iff_even.mpr even_two hpo

lemma odd_prime_ge_three {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2le : 2 ≤ p := hp.two_le
  have hne : p ≠ 2 := odd_prime_ne_two hp hpo
  omega

lemma odd_prime_eq_three_or_ge_five {p : ℕ} (hp : p.Prime) (hpo : Odd p) :
    p = 3 ∨ 5 ≤ p := by
  have h3 : 3 ≤ p := odd_prime_ge_three hp hpo
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpo
  omega

lemma v2_fSum_eq_one_sub {p k : ℕ} (hp : p.Prime) (hpo : Odd p) (hk : 1 ≤ k) :
    padicValRat 2 (fSum (p ^ k)) =
      (1 : ℤ) - padicValNat 2 (p + 1) - Nat.log 2 (k + 1) :=
  padicValRat_two_fSum_odd_prime_pow hp hpo hk

lemma eq_three_prime_pows_of_card_eq_three {m : ℕ} (hm : m ≠ 0)
    (h : m.primeFactors.card = 3) :
    ∃ p q r : ℕ, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      p.Prime ∧ q.Prime ∧ r.Prime ∧
      m.primeFactors = {p, q, r} ∧
      m = p ^ m.factorization p * q ^ m.factorization q *
        r ^ m.factorization r := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hs⟩ := Finset.card_eq_three.mp h
  have hp : p.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp)
  have hq : q.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp [hpq])
  have hr : r.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp [hpr, hqr])
  refine ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hs, ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Finsupp.prod, Nat.support_factorization, hs]
  rw [prod_insert (by simp [hpq, hpr]), prod_insert (by simp [hqr]),
    prod_singleton]
  ac_rfl

lemma fSum_gt_one_of_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    1 < fSum (p ^ k) :=
  fSum_gt_one (Nat.one_lt_pow (by omega) hp.one_lt)

lemma fSum_four_mul_gt_one {a p k q l r s : ℕ}
    (ha : 1 ≤ a) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hs : 1 ≤ s) :
    1 < fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) * fSum (r ^ s) := by
  have h1 := fSum_two_pow_gt_one ha
  have h2 := fSum_gt_one_of_prime_pow hp hk
  have h3 := fSum_gt_one_of_prime_pow hq hl
  have h4 := fSum_gt_one_of_prime_pow hr hs
  have hp1 : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hp2 : 0 < fSum (p ^ k) := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hp3 : 0 < fSum (q ^ l) := fSum_pos (pow_ne_zero l hq.ne_zero)
  have hp4 : 0 < fSum (r ^ s) := fSum_pos (pow_ne_zero s hr.ne_zero)
  have h12 : 1 < fSum (2 ^ a) * fSum (p ^ k) := by nlinarith
  have h123 : 1 < fSum (2 ^ a) * fSum (p ^ k) * fSum (q ^ l) := by nlinarith
  nlinarith

lemma twoPowDen_zmod32_of_mod8_five {a : ℕ} (h : a ≡ 5 [MOD 8]) :
    (twoPowDen a : ZMod 32) = 27 := by
  have ha : a % 8 = 5 := by simpa [Nat.ModEq] using h
  have hage : 5 ≤ a := by omega
  rw [twoPowDen]
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  rw [← mul_prod_erase _ _ h0, Nat.cast_mul]
  have hd0 : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 32) = 1 := by decide
  rw [hd0, one_mul]
  have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h1e, Nat.cast_mul]
  have hd1 : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 32) = 3 := by decide
  rw [hd1]
  have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h2e, Nat.cast_mul]
  have hd2 : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 32) = 7 := by decide
  rw [hd2]
  have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h3e, Nat.cast_mul]
  have hd3 : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 32) = 15 := by decide
  rw [hd3]
  have hrest : ∀ k ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3,
      ((2 ^ (k + 1) - 1 : ℕ) : ZMod 32) = 31 := by
    intro k hk
    have hk4 : 4 ≤ k := by simp [mem_erase] at hk; omega
    exact mersenne_zmod32_of_ge_four hk4
  have hcard : (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).card =
      a - 3 := by
    rw [card_erase_of_mem h3e, card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem h0, card_range]
    omega
  have hprod : ((∏ k ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3,
      (2 ^ (k + 1) - 1) : ℕ) : ZMod 32) = 1 := by
    rw [Nat.cast_prod, prod_congr rfl hrest, prod_const, hcard]
    have : (31 : ZMod 32) = -1 := by decide
    rw [this]
    have heven : Even (a - 3) := by
      rw [Nat.even_iff]; omega
    rw [heven.neg_one_pow]
  rw [hprod]
  decide

lemma twoPowNum_zmod32_of_mod32_twentyone {a : ℕ} (h : a ≡ 21 [MOD 32]) :
    twoPowNum a % 32 = 0 := by
  have ha : a % 32 = 21 := by simpa [Nat.ModEq] using h
  have ha5 : a ≡ 5 [MOD 8] := by
    have : a % 8 = 5 := by omega
    simpa [Nat.ModEq] using this
  have hage : 5 ≤ a := by omega
  have hV : (twoPowDen a : ZMod 32) = 27 := twoPowDen_zmod32_of_mod8_five ha5
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 32) = 27 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 32) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 32) = 9 := by
    have hdvd := twoPowDen_dvd a 1 h1
    have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 32) * 11 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 32) = 13 := by
    have hdvd := twoPowDen_dvd a 2 h2
    have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 32) * 23 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm3 : ((twoPowDen a / (2 ^ (3 + 1) - 1) : ℕ) : ZMod 32) = 21 := by
    have hdvd := twoPowDen_dvd a 3 h3
    have hu : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 32) * 15 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hsum : (twoPowNum a : ZMod 32) = 0 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h1e, hterm1]
    have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h2e, hterm2]
    have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h3e, hterm3]
    have htermk : ∀ k ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3,
        ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 32) = 5 := by
      intro k hk
      have hk4 : 4 ≤ k := by simp [mem_erase] at hk; omega
      have hkmem : k ∈ range (a + 1) := by
        simp [mem_erase] at hk; simp [mem_range]; omega
      have hdvd := twoPowDen_dvd a k hkmem
      have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 32) = 31 :=
        mersenne_zmod32_of_ge_four hk4
      have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 32) * 31 = 1 := by
        rw [hd]; decide
      rw [nat_div_cast_mul_inv hdvd hu, hV]
      decide
    rw [sum_congr rfl htermk, sum_const]
    have hcard : (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).card =
        a - 3 := by
      rw [card_erase_of_mem h3e, card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem h0, card_range]
      omega
    rw [hcard, nsmul_eq_mul]
    have ha3 : ((a - 3 : ℕ) : ZMod 32) = 18 := by
      have : (a - 3) % 32 = 18 := by omega
      rw [← Nat.cast_ofNat (n := 18), ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using this
    rw [ha3]
    decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (0 : ZMod 32).val = 0 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod32_twentyone {a : ℕ} (h : a ≡ 21 [MOD 32]) :
    5 ≤ padicValRat 2 (fSum (2 ^ a)) := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 32 = 0 := twoPowNum_zmod32_of_mod32_twentyone h
  have hdiv : 32 ∣ twoPowNum a := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have : 2 ^ 5 ∣ twoPowNum a := by simpa using hdiv
  have : 5 ≤ padicValNat 2 (twoPowNum a) := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  exact_mod_cast this

lemma two_pow_ge_six_zmod64 (t : ℕ) (ht : 6 ≤ t) :
    ((2 ^ t : ℕ) : ZMod 64) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
  rw [show t = 6 + k from hk, pow_add, Nat.cast_mul]
  have : ((2 ^ 6 : ℕ) : ZMod 64) = 0 := by decide
  rw [this, zero_mul]

lemma mersenne_zmod64_of_ge_five {k : ℕ} (hk : 5 ≤ k) :
    ((2 ^ (k + 1) - 1 : ℕ) : ZMod 64) = 63 := by
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [Nat.cast_sub hle]
  have : ((2 ^ (k + 1) : ℕ) : ZMod 64) = 0 :=
    two_pow_ge_six_zmod64 (k + 1) (by omega)
  rw [this]
  decide

lemma twoPowDen_zmod64_of_mod8_five {a : ℕ} (h : a ≡ 5 [MOD 8]) :
    (twoPowDen a : ZMod 64) = 27 := by
  have ha : a % 8 = 5 := by simpa [Nat.ModEq] using h
  have hage : 5 ≤ a := by omega
  rw [twoPowDen]
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have h4 : 4 ∈ range (a + 1) := by simp; omega
  rw [← mul_prod_erase _ _ h0, Nat.cast_mul]
  have hd0 : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 64) = 1 := by decide
  rw [hd0, one_mul]
  have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h1e, Nat.cast_mul]
  have hd1 : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 64) = 3 := by decide
  rw [hd1]
  have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h2e, Nat.cast_mul]
  have hd2 : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 64) = 7 := by decide
  rw [hd2]
  have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h3e, Nat.cast_mul]
  have hd3 : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 64) = 15 := by decide
  rw [hd3]
  have h4e : 4 ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h4e, Nat.cast_mul]
  have hd4 : ((2 ^ (4 + 1) - 1 : ℕ) : ZMod 64) = 31 := by decide
  rw [hd4]
  have hrest : ∀ k ∈ (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4,
      ((2 ^ (k + 1) - 1 : ℕ) : ZMod 64) = 63 := by
    intro k hk
    have hk5 : 5 ≤ k := by simp [mem_erase] at hk; omega
    exact mersenne_zmod64_of_ge_five hk5
  have hcard : ((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).card =
      a - 4 := by
    rw [card_erase_of_mem h4e, card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem h0, card_range]
    omega
  have hprod : ((∏ k ∈ (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4,
      (2 ^ (k + 1) - 1) : ℕ) : ZMod 64) = 63 := by
    rw [Nat.cast_prod, prod_congr rfl hrest, prod_const, hcard]
    have : (63 : ZMod 64) = -1 := by decide
    rw [this]
    have hodd : Odd (a - 4) := by rw [Nat.odd_iff]; omega
    rw [hodd.neg_one_pow]
  rw [hprod]
  decide

lemma twoPowNum_zmod64_of_mod64_twentyone {a : ℕ} (h : a ≡ 21 [MOD 64]) :
    twoPowNum a % 64 = 32 := by
  have ha : a % 64 = 21 := by simpa [Nat.ModEq] using h
  have ha5 : a ≡ 5 [MOD 8] := by
    have : a % 8 = 5 := by omega
    simpa [Nat.ModEq] using this
  have hage : 5 ≤ a := by omega
  have hV : (twoPowDen a : ZMod 64) = 27 := twoPowDen_zmod64_of_mod8_five ha5
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have h4 : 4 ∈ range (a + 1) := by simp; omega
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 64) = 27 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 64) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 64) = 9 := by
    have hdvd := twoPowDen_dvd a 1 h1
    have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 64) * 43 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 64) = 13 := by
    have hdvd := twoPowDen_dvd a 2 h2
    have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 64) * 55 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm3 : ((twoPowDen a / (2 ^ (3 + 1) - 1) : ℕ) : ZMod 64) = 53 := by
    have hdvd := twoPowDen_dvd a 3 h3
    have hu : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 64) * 47 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm4 : ((twoPowDen a / (2 ^ (4 + 1) - 1) : ℕ) : ZMod 64) = 5 := by
    have hdvd := twoPowDen_dvd a 4 h4
    have hu : ((2 ^ (4 + 1) - 1 : ℕ) : ZMod 64) * 31 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hsum : (twoPowNum a : ZMod 64) = 32 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h1e, hterm1]
    have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h2e, hterm2]
    have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h3e, hterm3]
    have h4e : 4 ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h4e, hterm4]
    have htermk : ∀ k ∈ (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4,
        ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 64) = 37 := by
      intro k hk
      have hk5 : 5 ≤ k := by simp [mem_erase] at hk; omega
      have hkmem : k ∈ range (a + 1) := by
        simp [mem_erase] at hk; simp [mem_range]; omega
      have hdvd := twoPowDen_dvd a k hkmem
      have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 64) = 63 :=
        mersenne_zmod64_of_ge_five hk5
      have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 64) * 63 = 1 := by
        rw [hd]; decide
      rw [nat_div_cast_mul_inv hdvd hu, hV]
      decide
    rw [sum_congr rfl htermk, sum_const]
    have hcard : ((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).card =
        a - 4 := by
      rw [card_erase_of_mem h4e, card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem h0, card_range]
      omega
    rw [hcard, nsmul_eq_mul]
    have ha4 : ((a - 4 : ℕ) : ZMod 64) = 17 := by
      have : (a - 4) % 64 = 17 := by omega
      rw [← Nat.cast_ofNat (n := 17), ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using this
    rw [ha4]
    decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (32 : ZMod 64).val = 32 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod64_twentyone {a : ℕ} (h : a ≡ 21 [MOD 64]) :
    padicValRat 2 (fSum (2 ^ a)) = 5 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 64 = 32 := twoPowNum_zmod64_of_mod64_twentyone h
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have hdiv32 : 32 ∣ twoPowNum a :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hndiv64 : ¬ 64 ∣ twoPowNum a := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hle : 5 ≤ padicValNat 2 (twoPowNum a) := by
    have : 2 ^ 5 ∣ twoPowNum a := by simpa using hdiv32
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 (twoPowNum a) < 6 := by
    by_contra hge
    have : 2 ^ 6 ∣ twoPowNum a := by
      have : 6 ≤ padicValNat 2 (twoPowNum a) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv64 (by simpa using this)
  have : padicValNat 2 (twoPowNum a) = 5 := by omega
  exact_mod_cast this

lemma twoPowNum_zmod64_of_mod64_fiftythree {a : ℕ} (h : a ≡ 53 [MOD 64]) :
    twoPowNum a % 64 = 0 := by
  have ha : a % 64 = 53 := by simpa [Nat.ModEq] using h
  have ha5 : a ≡ 5 [MOD 8] := by
    have : a % 8 = 5 := by omega
    simpa [Nat.ModEq] using this
  have hage : 5 ≤ a := by omega
  have hV : (twoPowDen a : ZMod 64) = 27 := twoPowDen_zmod64_of_mod8_five ha5
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have h4 : 4 ∈ range (a + 1) := by simp; omega
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 64) = 27 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 64) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 64) = 9 := by
    have hdvd := twoPowDen_dvd a 1 h1
    have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 64) * 43 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 64) = 13 := by
    have hdvd := twoPowDen_dvd a 2 h2
    have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 64) * 55 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm3 : ((twoPowDen a / (2 ^ (3 + 1) - 1) : ℕ) : ZMod 64) = 53 := by
    have hdvd := twoPowDen_dvd a 3 h3
    have hu : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 64) * 47 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm4 : ((twoPowDen a / (2 ^ (4 + 1) - 1) : ℕ) : ZMod 64) = 5 := by
    have hdvd := twoPowDen_dvd a 4 h4
    have hu : ((2 ^ (4 + 1) - 1 : ℕ) : ZMod 64) * 31 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hsum : (twoPowNum a : ZMod 64) = 0 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h1e, hterm1]
    have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h2e, hterm2]
    have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h3e, hterm3]
    have h4e : 4 ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h4e, hterm4]
    have htermk : ∀ k ∈ (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4,
        ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 64) = 37 := by
      intro k hk
      have hk5 : 5 ≤ k := by simp [mem_erase] at hk; omega
      have hkmem : k ∈ range (a + 1) := by
        simp [mem_erase] at hk; simp [mem_range]; omega
      have hdvd := twoPowDen_dvd a k hkmem
      have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 64) = 63 :=
        mersenne_zmod64_of_ge_five hk5
      have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 64) * 63 = 1 := by
        rw [hd]; decide
      rw [nat_div_cast_mul_inv hdvd hu, hV]
      decide
    rw [sum_congr rfl htermk, sum_const]
    have hcard : ((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).card =
        a - 4 := by
      rw [card_erase_of_mem h4e, card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem h0, card_range]
      omega
    rw [hcard, nsmul_eq_mul]
    have ha4 : ((a - 4 : ℕ) : ZMod 64) = 49 := by
      have : (a - 4) % 64 = 49 := by omega
      rw [← Nat.cast_ofNat (n := 49), ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using this
    rw [ha4]
    decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (0 : ZMod 64).val = 0 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod64_fiftythree {a : ℕ} (h : a ≡ 53 [MOD 64]) :
    6 ≤ padicValRat 2 (fSum (2 ^ a)) := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 64 = 0 := twoPowNum_zmod64_of_mod64_fiftythree h
  have hdiv : 64 ∣ twoPowNum a := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have : 2 ^ 6 ∣ twoPowNum a := by simpa using hdiv
  have : 6 ≤ padicValNat 2 (twoPowNum a) := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  exact_mod_cast this

lemma mod32_twentyone_of_mod64 {a : ℕ} (h : a ≡ 21 [MOD 32]) :
    a ≡ 21 [MOD 64] ∨ a ≡ 53 [MOD 64] := by
  have : a % 32 = 21 := by simpa [Nat.ModEq] using h
  have : a % 64 = 21 ∨ a % 64 = 53 := by
    have : a % 64 < 64 := Nat.mod_lt _ (by decide)
    omega
  cases this with
  | inl h => exact Or.inl (by simpa [Nat.ModEq] using h)
  | inr h => exact Or.inr (by simpa [Nat.ModEq] using h)

lemma two_pow_ge_seven_zmod128 (t : ℕ) (ht : 7 ≤ t) :
    ((2 ^ t : ℕ) : ZMod 128) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
  rw [show t = 7 + k from hk, pow_add, Nat.cast_mul]
  have : ((2 ^ 7 : ℕ) : ZMod 128) = 0 := by decide
  rw [this, zero_mul]

lemma mersenne_zmod128_of_ge_six {k : ℕ} (hk : 6 ≤ k) :
    ((2 ^ (k + 1) - 1 : ℕ) : ZMod 128) = 127 := by
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [Nat.cast_sub hle]
  have : ((2 ^ (k + 1) : ℕ) : ZMod 128) = 0 :=
    two_pow_ge_seven_zmod128 (k + 1) (by omega)
  rw [this]
  decide

lemma twoPowDen_zmod128_of_mod8_five {a : ℕ} (h : a ≡ 5 [MOD 8]) :
    (twoPowDen a : ZMod 128) = 27 := by
  have ha : a % 8 = 5 := by simpa [Nat.ModEq] using h
  have hage : 5 ≤ a := by omega
  rw [twoPowDen]
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have h4 : 4 ∈ range (a + 1) := by simp; omega
  have h5 : 5 ∈ range (a + 1) := by simp; omega
  rw [← mul_prod_erase _ _ h0, Nat.cast_mul]
  have hd0 : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 128) = 1 := by decide
  rw [hd0, one_mul]
  have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h1e, Nat.cast_mul]
  have hd1 : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 128) = 3 := by decide
  rw [hd1]
  have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h2e, Nat.cast_mul]
  have hd2 : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 128) = 7 := by decide
  rw [hd2]
  have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h3e, Nat.cast_mul]
  have hd3 : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 128) = 15 := by decide
  rw [hd3]
  have h4e : 4 ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h4e, Nat.cast_mul]
  have hd4 : ((2 ^ (4 + 1) - 1 : ℕ) : ZMod 128) = 31 := by decide
  rw [hd4]
  have h5e : 5 ∈ (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4 := by
    simp [mem_erase]; omega
  rw [← mul_prod_erase _ _ h5e, Nat.cast_mul]
  have hd5 : ((2 ^ (5 + 1) - 1 : ℕ) : ZMod 128) = 63 := by decide
  rw [hd5]
  have hrest : ∀ k ∈ ((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).erase 5,
      ((2 ^ (k + 1) - 1 : ℕ) : ZMod 128) = 127 := by
    intro k hk
    have hk6 : 6 ≤ k := by simp [mem_erase] at hk; omega
    exact mersenne_zmod128_of_ge_six hk6
  have hcard : (((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).erase 5).card =
      a - 5 := by
    rw [card_erase_of_mem h5e, card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem (by simp [mem_erase]; omega),
      card_erase_of_mem h0, card_range]
    omega
  have hprod : ((∏ k ∈ ((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).erase 5,
      (2 ^ (k + 1) - 1) : ℕ) : ZMod 128) = 1 := by
    rw [Nat.cast_prod, prod_congr rfl hrest, prod_const, hcard]
    have : (127 : ZMod 128) = -1 := by decide
    rw [this]
    have heven : Even (a - 5) := by rw [Nat.even_iff]; omega
    rw [heven.neg_one_pow]
  rw [hprod]
  decide

lemma twoPowNum_zmod128_of_mod128_fiftythree {a : ℕ} (h : a ≡ 53 [MOD 128]) :
    twoPowNum a % 128 = 64 := by
  have ha : a % 128 = 53 := by simpa [Nat.ModEq] using h
  have ha5 : a ≡ 5 [MOD 8] := by
    have : a % 8 = 5 := by omega
    simpa [Nat.ModEq] using this
  have hage : 5 ≤ a := by omega
  have hV : (twoPowDen a : ZMod 128) = 27 := twoPowDen_zmod128_of_mod8_five ha5
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have h4 : 4 ∈ range (a + 1) := by simp; omega
  have h5 : 5 ∈ range (a + 1) := by simp; omega
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 128) = 27 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 128) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 128) = 9 := by
    have hdvd := twoPowDen_dvd a 1 h1
    have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 128) * 43 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 128) = 77 := by
    have hdvd := twoPowDen_dvd a 2 h2
    have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 128) * 55 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm3 : ((twoPowDen a / (2 ^ (3 + 1) - 1) : ℕ) : ZMod 128) = 53 := by
    have hdvd := twoPowDen_dvd a 3 h3
    have hu : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 128) * 111 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm4 : ((twoPowDen a / (2 ^ (4 + 1) - 1) : ℕ) : ZMod 128) = 5 := by
    have hdvd := twoPowDen_dvd a 4 h4
    have hu : ((2 ^ (4 + 1) - 1 : ℕ) : ZMod 128) * 95 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm5 : ((twoPowDen a / (2 ^ (5 + 1) - 1) : ℕ) : ZMod 128) = 37 := by
    have hdvd := twoPowDen_dvd a 5 h5
    have hu : ((2 ^ (5 + 1) - 1 : ℕ) : ZMod 128) * 63 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hsum : (twoPowNum a : ZMod 128) = 64 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h1e, hterm1]
    have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h2e, hterm2]
    have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h3e, hterm3]
    have h4e : 4 ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h4e, hterm4]
    have h5e : 5 ∈ (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h5e, hterm5]
    have htermk : ∀ k ∈ ((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).erase 5,
        ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 128) = 101 := by
      intro k hk
      have hk6 : 6 ≤ k := by simp [mem_erase] at hk; omega
      have hkmem : k ∈ range (a + 1) := by
        simp [mem_erase] at hk; simp [mem_range]; omega
      have hdvd := twoPowDen_dvd a k hkmem
      have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 128) = 127 :=
        mersenne_zmod128_of_ge_six hk6
      have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 128) * 127 = 1 := by
        rw [hd]; decide
      rw [nat_div_cast_mul_inv hdvd hu, hV]
      decide
    rw [sum_congr rfl htermk, sum_const]
    have hcard : (((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).erase 5).card =
        a - 5 := by
      rw [card_erase_of_mem h5e, card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem h0, card_range]
      omega
    rw [hcard, nsmul_eq_mul]
    have ha5z : ((a - 5 : ℕ) : ZMod 128) = 48 := by
      have : (a - 5) % 128 = 48 := by omega
      rw [← Nat.cast_ofNat (n := 48), ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using this
    rw [ha5z]
    decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (64 : ZMod 128).val = 64 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod128_fiftythree {a : ℕ} (h : a ≡ 53 [MOD 128]) :
    padicValRat 2 (fSum (2 ^ a)) = 6 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 128 = 64 := twoPowNum_zmod128_of_mod128_fiftythree h
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have hdiv64 : 64 ∣ twoPowNum a :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hndiv128 : ¬ 128 ∣ twoPowNum a := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hle : 6 ≤ padicValNat 2 (twoPowNum a) := by
    have : 2 ^ 6 ∣ twoPowNum a := by simpa using hdiv64
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 (twoPowNum a) < 7 := by
    by_contra hge
    have : 2 ^ 7 ∣ twoPowNum a := by
      have : 7 ≤ padicValNat 2 (twoPowNum a) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv128 (by simpa using this)
  have : padicValNat 2 (twoPowNum a) = 6 := by omega
  exact_mod_cast this

lemma twoPowNum_zmod128_of_mod128_onehundredseventeen {a : ℕ}
    (h : a ≡ 117 [MOD 128]) :
    twoPowNum a % 128 = 0 := by
  have ha : a % 128 = 117 := by simpa [Nat.ModEq] using h
  have ha5 : a ≡ 5 [MOD 8] := by
    have : a % 8 = 5 := by omega
    simpa [Nat.ModEq] using this
  have hage : 5 ≤ a := by omega
  have hV : (twoPowDen a : ZMod 128) = 27 := twoPowDen_zmod128_of_mod8_five ha5
  have h0 : 0 ∈ range (a + 1) := by simp
  have h1 : 1 ∈ range (a + 1) := by simp; omega
  have h2 : 2 ∈ range (a + 1) := by simp; omega
  have h3 : 3 ∈ range (a + 1) := by simp; omega
  have h4 : 4 ∈ range (a + 1) := by simp; omega
  have h5 : 5 ∈ range (a + 1) := by simp; omega
  have hterm0 : ((twoPowDen a / (2 ^ (0 + 1) - 1) : ℕ) : ZMod 128) = 27 := by
    have hdvd := twoPowDen_dvd a 0 h0
    have hu : ((2 ^ (0 + 1) - 1 : ℕ) : ZMod 128) * 1 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV, mul_one]
  have hterm1 : ((twoPowDen a / (2 ^ (1 + 1) - 1) : ℕ) : ZMod 128) = 9 := by
    have hdvd := twoPowDen_dvd a 1 h1
    have hu : ((2 ^ (1 + 1) - 1 : ℕ) : ZMod 128) * 43 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm2 : ((twoPowDen a / (2 ^ (2 + 1) - 1) : ℕ) : ZMod 128) = 77 := by
    have hdvd := twoPowDen_dvd a 2 h2
    have hu : ((2 ^ (2 + 1) - 1 : ℕ) : ZMod 128) * 55 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm3 : ((twoPowDen a / (2 ^ (3 + 1) - 1) : ℕ) : ZMod 128) = 53 := by
    have hdvd := twoPowDen_dvd a 3 h3
    have hu : ((2 ^ (3 + 1) - 1 : ℕ) : ZMod 128) * 111 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm4 : ((twoPowDen a / (2 ^ (4 + 1) - 1) : ℕ) : ZMod 128) = 5 := by
    have hdvd := twoPowDen_dvd a 4 h4
    have hu : ((2 ^ (4 + 1) - 1 : ℕ) : ZMod 128) * 95 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hterm5 : ((twoPowDen a / (2 ^ (5 + 1) - 1) : ℕ) : ZMod 128) = 37 := by
    have hdvd := twoPowDen_dvd a 5 h5
    have hu : ((2 ^ (5 + 1) - 1 : ℕ) : ZMod 128) * 63 = 1 := by decide
    rw [nat_div_cast_mul_inv hdvd hu, hV]
    decide
  have hsum : (twoPowNum a : ZMod 128) = 0 := by
    rw [twoPowNum, Nat.cast_sum, ← add_sum_erase _ _ h0, hterm0]
    have h1e : 1 ∈ (range (a + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h1e, hterm1]
    have h2e : 2 ∈ ((range (a + 1)).erase 0).erase 1 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h2e, hterm2]
    have h3e : 3 ∈ (((range (a + 1)).erase 0).erase 1).erase 2 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h3e, hterm3]
    have h4e : 4 ∈ ((((range (a + 1)).erase 0).erase 1).erase 2).erase 3 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h4e, hterm4]
    have h5e : 5 ∈ (((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4 := by
      simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h5e, hterm5]
    have htermk : ∀ k ∈ ((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).erase 5,
        ((twoPowDen a / (2 ^ (k + 1) - 1) : ℕ) : ZMod 128) = 101 := by
      intro k hk
      have hk6 : 6 ≤ k := by simp [mem_erase] at hk; omega
      have hkmem : k ∈ range (a + 1) := by
        simp [mem_erase] at hk; simp [mem_range]; omega
      have hdvd := twoPowDen_dvd a k hkmem
      have hd : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 128) = 127 :=
        mersenne_zmod128_of_ge_six hk6
      have hu : ((2 ^ (k + 1) - 1 : ℕ) : ZMod 128) * 127 = 1 := by
        rw [hd]; decide
      rw [nat_div_cast_mul_inv hdvd hu, hV]
      decide
    rw [sum_congr rfl htermk, sum_const]
    have hcard : (((((((range (a + 1)).erase 0).erase 1).erase 2).erase 3).erase 4).erase 5).card =
        a - 5 := by
      rw [card_erase_of_mem h5e, card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem (by simp [mem_erase]; omega),
        card_erase_of_mem h0, card_range]
      omega
    rw [hcard, nsmul_eq_mul]
    have ha5z : ((a - 5 : ℕ) : ZMod 128) = 112 := by
      have : (a - 5) % 128 = 112 := by omega
      rw [← Nat.cast_ofNat (n := 112), ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using this
    rw [ha5z]
    decide
  have hval := congrArg ZMod.val hsum
  rw [ZMod.val_natCast] at hval
  have : (0 : ZMod 128).val = 0 := by decide
  rwa [this] at hval

lemma v2_fSum_two_pow_mod128_onehundredseventeen {a : ℕ}
    (h : a ≡ 117 [MOD 128]) :
    7 ≤ padicValRat 2 (fSum (2 ^ a)) := by
  haveI := two_fact
  rw [padicValRat_two_fSum_two_pow]
  have hmod : twoPowNum a % 128 = 0 :=
    twoPowNum_zmod128_of_mod128_onehundredseventeen h
  have hdiv : 128 ∣ twoPowNum a := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hpos : twoPowNum a ≠ 0 := (twoPowNum_pos a).ne'
  have : 2 ^ 7 ∣ twoPowNum a := by simpa using hdiv
  have : 7 ≤ padicValNat 2 (twoPowNum a) := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  exact_mod_cast this

lemma mod64_fiftythree_of_mod128 {a : ℕ} (h : a ≡ 53 [MOD 64]) :
    a ≡ 53 [MOD 128] ∨ a ≡ 117 [MOD 128] := by
  have : a % 64 = 53 := by simpa [Nat.ModEq] using h
  have : a % 128 = 53 ∨ a % 128 = 117 := by
    have : a % 128 < 128 := Nat.mod_lt _ (by decide)
    omega
  cases this with
  | inl h => exact Or.inl (by simpa [Nat.ModEq] using h)
  | inr h => exact Or.inr (by simpa [Nat.ModEq] using h)

lemma odd_mod8 {n : ℕ} (h : Odd n) :
    n ≡ 1 [MOD 8] ∨ n ≡ 3 [MOD 8] ∨ n ≡ 5 [MOD 8] ∨ n ≡ 7 [MOD 8] := by
  have h2 : n % 2 = 1 := Nat.odd_iff.mp h
  have h8 : n % 8 < 8 := Nat.mod_lt _ (by decide)
  have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases this with h | h | h | h
  · exact Or.inl (by simpa [Nat.ModEq] using h)
  · exact Or.inr (Or.inl (by simpa [Nat.ModEq] using h))
  · exact Or.inr (Or.inr (Or.inl (by simpa [Nat.ModEq] using h)))
  · exact Or.inr (Or.inr (Or.inr (by simpa [Nat.ModEq] using h)))

lemma padicValNat_two_add_one_of_mod8_three {p : ℕ} (hp : Odd p)
    (h : p ≡ 3 [MOD 8]) : padicValNat 2 (p + 1) = 2 := by
  haveI := two_fact
  have hmod : (p + 1) % 8 = 4 := by
    have : p % 8 = 3 := by simpa [Nat.ModEq] using h
    omega
  have hdiv4 : 4 ∣ p + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hndiv8 : ¬ 8 ∣ p + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hpos : p + 1 ≠ 0 := by omega
  have hle : 2 ≤ padicValNat 2 (p + 1) := by
    have : 2 ^ 2 ∣ p + 1 := by simpa using hdiv4
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 (p + 1) < 3 := by
    by_contra hge
    have : 2 ^ 3 ∣ p + 1 := by
      have : 3 ≤ padicValNat 2 (p + 1) := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    exact hndiv8 (by simpa using this)
  omega

lemma padicValNat_two_add_one_of_mod8_seven {p : ℕ} (hp : Odd p)
    (h : p ≡ 7 [MOD 8]) : 3 ≤ padicValNat 2 (p + 1) := by
  haveI := two_fact
  have hmod : (p + 1) % 8 = 0 := by
    have : p % 8 = 7 := by simpa [Nat.ModEq] using h
    omega
  have hdiv8 : 8 ∣ p + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hpos : p + 1 ≠ 0 := by omega
  have : 2 ^ 3 ∣ p + 1 := by simpa using hdiv8
  have : 3 ≤ padicValNat 2 (p + 1) := by
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  exact this

lemma log_two_eq_one_of_mem_two_three {n : ℕ} (h1 : 2 ≤ n) (h2 : n ≤ 3) :
    Nat.log 2 n = 1 := by
  interval_cases n <;> decide

lemma log_two_eq_two_of_mem_four_seven {n : ℕ} (h1 : 4 ≤ n) (h2 : n ≤ 7) :
    Nat.log 2 n = 2 := by
  interval_cases n <;> decide

lemma log_two_eq_three_of_mem_eight_fifteen {n : ℕ} (h1 : 8 ≤ n) (h2 : n ≤ 15) :
    Nat.log 2 n = 3 := by
  interval_cases n <;> decide

lemma v2_fSum_odd_prime_pow_mod8_three_small {p k : ℕ}
    (hp : p.Prime) (hodd : Odd p) (h : p ≡ 3 [MOD 8])
    (hk : k = 1 ∨ k = 2) :
    padicValRat 2 (fSum (p ^ k)) = -2 := by
  haveI := two_fact
  have hk1 : 1 ≤ k := by omega
  rw [padicValRat_two_fSum_odd_prime_pow hp hodd hk1]
  have hv : padicValNat 2 (p + 1) = 2 :=
    padicValNat_two_add_one_of_mod8_three hodd h
  have hlog : Nat.log 2 (k + 1) = 1 :=
    log_two_eq_one_of_mem_two_three (by omega) (by omega)
  omega

lemma v2_fSum_odd_prime_pow_mod4_one_mid {p k : ℕ}
    (hp : p.Prime) (hodd : Odd p) (h : p ≡ 1 [MOD 4])
    (hk : 3 ≤ k) (hk6 : k ≤ 6) :
    padicValRat 2 (fSum (p ^ k)) = -2 := by
  haveI := two_fact
  have hk1 : 1 ≤ k := by omega
  rw [padicValRat_two_fSum_odd_prime_pow hp hodd hk1]
  have hv : padicValNat 2 (p + 1) = 1 :=
    padicValNat_two_add_one_of_mod4_one hodd h
  have hlog : Nat.log 2 (k + 1) = 2 :=
    log_two_eq_two_of_mem_four_seven (by omega) (by omega)
  omega

lemma v2_fSum_odd_prime_pow_mod8_seven_small {p k : ℕ}
    (hp : p.Prime) (hodd : Odd p) (h : p ≡ 7 [MOD 8])
    (hk : 1 ≤ k) :
    padicValRat 2 (fSum (p ^ k)) ≤ -3 := by
  haveI := two_fact
  rw [padicValRat_two_fSum_odd_prime_pow hp hodd hk]
  have h1 : 3 ≤ padicValNat 2 (p + 1) :=
    padicValNat_two_add_one_of_mod8_seven hodd h
  have h2 : 1 ≤ Nat.log 2 (k + 1) := Nat.log_pos (by decide) (by omega)
  omega

lemma p_mod4_one_of_mod8_one {p : ℕ} (h : p ≡ 1 [MOD 8]) : p ≡ 1 [MOD 4] := by
  have : p % 8 = 1 := by simpa [Nat.ModEq] using h
  have : p % 4 = 1 := by omega
  simpa [Nat.ModEq] using this

lemma p_mod4_one_of_mod8_five {p : ℕ} (h : p ≡ 5 [MOD 8]) : p ≡ 1 [MOD 4] := by
  have : p % 8 = 5 := by simpa [Nat.ModEq] using h
  have : p % 4 = 1 := by omega
  simpa [Nat.ModEq] using this

lemma p_mod4_three_of_mod8_three {p : ℕ} (h : p ≡ 3 [MOD 8]) : p ≡ 3 [MOD 4] := by
  have : p % 8 = 3 := by simpa [Nat.ModEq] using h
  have : p % 4 = 3 := by omega
  simpa [Nat.ModEq] using this

lemma p_mod4_three_of_mod8_seven {p : ℕ} (h : p ≡ 7 [MOD 8]) : p ≡ 3 [MOD 4] := by
  have : p % 8 = 7 := by simpa [Nat.ModEq] using h
  have : p % 4 = 3 := by omega
  simpa [Nat.ModEq] using this



lemma mod16_five_of_mod32 {a : ℕ} (h : a ≡ 5 [MOD 16]) :
    a ≡ 5 [MOD 32] ∨ a ≡ 21 [MOD 32] := by
  have : a % 16 = 5 := by simpa [Nat.ModEq] using h
  have : a % 32 = 5 ∨ a % 32 = 21 := by
    have : a % 32 < 32 := Nat.mod_lt _ (by decide)
    omega
  cases this with
  | inl h => exact Or.inl (by simpa [Nat.ModEq] using h)
  | inr h => exact Or.inr (by simpa [Nat.ModEq] using h)

lemma fSum_two_five_three_sq_gt_two : 2 < fSum (2 ^ 5) * fSum (3 ^ 2) := by
  rw [fSum_two_pow_five, fSum_nine]; norm_num

lemma fSum_prime_pow_lt_geom {p l : ℕ} (hp : p.Prime) :
    fSum (p ^ l) < (p : ℚ) / (p - 1) := by
  have hq1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hr : (1 : ℚ) / p ≠ 1 := fun h => hq1.ne' (by field_simp at h; exact h.symm)
  have hr1 : (1 : ℚ) / p < 1 := (div_lt_one (zero_lt_one.trans hq1)).mpr hq1
  have hle : fSum (p ^ l) ≤ ∑ j ∈ range (l + 1), ((1 : ℚ) / p) ^ j := by
    rw [fSum_prime_pow hp]
    refine sum_le_sum fun j _ => ?_
    cases Nat.eq_zero_or_pos j with
    | inl hj0 =>
      subst hj0
      simp [sigma_one]
    | inr hj0 =>
      calc (1 : ℚ) / (sigma 1 (p ^ j) : ℚ)
          ≤ (1 : ℚ) / (p : ℚ) ^ j := (inv_sigma_lt_pow hp hj0).le
        _ = (1 / (p : ℚ)) ^ j := (one_div_pow _ _).symm
  have hclosed : ∑ j ∈ range (l + 1), ((1 : ℚ) / p) ^ j =
      (((1 : ℚ) / p) ^ (l + 1) - 1) / (1 / p - 1) :=
    geom_sum_eq hr (l + 1)
  have hrew : (((1 : ℚ) / p) ^ (l + 1) - 1) / (1 / p - 1) =
      (1 - ((1 : ℚ) / p) ^ (l + 1)) / (1 - 1 / p) := by
    have h1 : (1 : ℚ) / p - 1 = -((1 : ℚ) - 1 / p) := by ring
    have h2 : ((1 : ℚ) / p) ^ (l + 1) - 1 = -((1 : ℚ) - ((1 : ℚ) / p) ^ (l + 1)) := by ring
    rw [h1, h2, neg_div_neg_eq]
  have hden : (0 : ℚ) < 1 - 1 / p := sub_pos.mpr hr1
  have hlt : (1 - ((1 : ℚ) / p) ^ (l + 1)) / (1 - 1 / p) < 1 / (1 - 1 / p) := by
    rw [div_lt_div_iff₀ hden hden]
    nlinarith [show (0 : ℚ) < ((1 : ℚ) / p) ^ (l + 1) by positivity]
  have hinf : (1 : ℚ) / (1 - 1 / p) = p / (p - 1) := by
    have h1 : (1 : ℚ) - 1 / p = (p - 1) / p := by
      rw [← div_self hp0, sub_div]
    rw [h1, one_div_div]
  calc fSum (p ^ l)
      ≤ ∑ j ∈ range (l + 1), ((1 : ℚ) / p) ^ j := hle
    _ = (((1 : ℚ) / p) ^ (l + 1) - 1) / (1 / p - 1) := hclosed
    _ = (1 - ((1 : ℚ) / p) ^ (l + 1)) / (1 - 1 / p) := hrew
    _ < 1 / (1 - 1 / p) := hlt
    _ = p / (p - 1) := hinf

/-- `2^5 · 3^k · q^l` is never `2`. -/
lemma fSum_two_five_three_odd_ne_two {k q l : ℕ}
    (hq : q.Prime) (hqo : Odd q) (hk : 1 ≤ k) (hl : 1 ≤ l) (hqne3 : q ≠ 3) :
    fSum (2 ^ 5) * fSum (3 ^ k) * fSum (q ^ l) ≠ 2 := by
  have hq5 : 5 ≤ q := by
    rcases odd_prime_eq_three_or_ge_five hq hqo with h | h
    · exact (hqne3 h).elim
    · exact h
  have h2pos : 0 < fSum (2 ^ 5) := fSum_pos (pow_ne_zero 5 two_ne_zero)
  have h3pos : 0 < fSum (3 ^ k) := fSum_pos (pow_ne_zero k (by decide : (3 : ℕ) ≠ 0))
  have hqpos' : 0 < fSum (q ^ l) := fSum_pos (pow_ne_zero l hq.ne_zero)
  cases lt_or_ge k 2 with
  | inr hk2 =>
    have h32 : fSum (3 ^ 2) ≤ fSum (3 ^ k) := by
      cases Nat.eq_or_lt_of_le hk2 with
      | inl h => rw [h]
      | inr h => exact (fSum_strict_mono_prime_pow Nat.prime_three h).le
    have h0 : 2 < fSum (2 ^ 5) * fSum (3 ^ 2) := fSum_two_five_three_sq_gt_two
    have hqpos : 1 < fSum (q ^ l) := fSum_gt_one_of_prime_pow hq hl
    have hApos : 0 < fSum (2 ^ 5) * fSum (3 ^ 2) :=
      mul_pos h2pos (fSum_pos (show (3 : ℕ) ^ 2 ≠ 0 by decide))
    have hgtA : 2 < fSum (2 ^ 5) * fSum (3 ^ 2) * fSum (q ^ l) := by
      calc (2 : ℚ) < fSum (2 ^ 5) * fSum (3 ^ 2) := h0
        _ = fSum (2 ^ 5) * fSum (3 ^ 2) * 1 := (mul_one _).symm
        _ < fSum (2 ^ 5) * fSum (3 ^ 2) * fSum (q ^ l) :=
          mul_lt_mul_of_pos_left hqpos hApos
    have hmono : fSum (2 ^ 5) * fSum (3 ^ 2) * fSum (q ^ l) ≤
        fSum (2 ^ 5) * fSum (3 ^ k) * fSum (q ^ l) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h32 h2pos.le) hqpos'.le
    exact ne_of_gt (lt_of_lt_of_le hgtA hmono)
  | inl hk1 =>
    have hk_eq : k = 1 := by omega
    subst hk_eq
    by_cases hsmall : q ≤ 173
    · have hgt0 : 2 < fSum (2 ^ 5) * fSum 3 * fSum q := by
        rw [fSum_two_pow_five, fSum_three, fSum_prime hq]
        have hqle : (q : ℚ) ≤ 173 := by exact_mod_cast hsmall
        have hq1 : (q : ℚ) + 1 ≠ 0 := by
          exact (add_pos_of_nonneg_of_pos (Nat.cast_nonneg q) zero_lt_one).ne'
        field_simp
        nlinarith
      have hqleFS : fSum q ≤ fSum (q ^ l) := by
        cases Nat.eq_or_lt_of_le hl with
        | inl h => subst h; rw [pow_one]
        | inr h =>
          simpa [pow_one] using (fSum_strict_mono_prime_pow hq h).le
      have h3pos1 : 0 < fSum (3 : ℕ) := fSum_pos (by decide)
      have hmono : fSum (2 ^ 5) * fSum 3 * fSum q ≤
          fSum (2 ^ 5) * fSum (3 ^ 1) * fSum (q ^ l) := by
        rw [pow_one]
        exact mul_le_mul_of_nonneg_left hqleFS (mul_nonneg h2pos.le h3pos1.le)
      exact ne_of_gt (lt_of_lt_of_le hgt0 hmono)
    · have hqge : 179 ≤ q := by
        have h174 : 174 ≤ q := by omega
        have n174 : ¬ Nat.Prime 174 :=
          Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 87 = 174)
            (by decide) (by decide)
        have n175 : ¬ Nat.Prime 175 :=
          Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 35 = 175)
            (by decide) (by decide)
        have n176 : ¬ Nat.Prime 176 :=
          Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 88 = 176)
            (by decide) (by decide)
        have n177 : ¬ Nat.Prime 177 :=
          Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 59 = 177)
            (by decide) (by decide)
        have n178 : ¬ Nat.Prime 178 :=
          Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 89 = 178)
            (by decide) (by decide)
        have hq174 : q ≠ 174 := fun h => n174 (h ▸ hq)
        have hq175 : q ≠ 175 := fun h => n175 (h ▸ hq)
        have hq176 : q ≠ 176 := fun h => n176 (h ▸ hq)
        have hq177 : q ≠ 177 := fun h => n177 (h ▸ hq)
        have hq178 : q ≠ 178 := fun h => n178 (h ▸ hq)
        omega
      have hσ := fSum_prime_pow_lt_geom (l := l) hq
      have h3pos1 : 0 < fSum (3 : ℕ) := fSum_pos (by decide)
      have hprod : fSum (2 ^ 5) * fSum 3 * ((q : ℚ) / (q - 1)) < 2 := by
        rw [fSum_two_pow_five, fSum_three]
        have hqg : (179 : ℚ) ≤ q := by exact_mod_cast hqge
        have hq1Q : (1 : ℚ) < q := by exact_mod_cast hq.one_lt
        have hqm : (q : ℚ) - 1 ≠ 0 := (sub_pos.mpr hq1Q).ne'
        field_simp
        rw [div_lt_iff₀ (sub_pos.mpr hq1Q)]
        nlinarith
      have hlt : fSum (2 ^ 5) * fSum (3 ^ 1) * fSum (q ^ l) < 2 := by
        rw [pow_one]
        have hmul : fSum (2 ^ 5) * fSum 3 * fSum (q ^ l) <
            fSum (2 ^ 5) * fSum 3 * ((q : ℚ) / (q - 1)) :=
          mul_lt_mul_of_pos_left hσ (mul_pos h2pos h3pos1)
        exact hmul.trans hprod
      exact ne_of_lt hlt

lemma tight_pos {p : ℕ} (hp : 2 ≤ p) :
    (0 : ℚ) < 1 / ((p : ℚ) + 1) ∧
    (0 : ℚ) < 1 / ((p : ℚ) * (p - 1)) := by
  have hq1 : (1 : ℚ) < p := by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hp)
  have hp1pos : (0 : ℚ) < p - 1 := sub_pos.mpr hq1
  refine ⟨one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one),
    one_div_pos.mpr (mul_pos (zero_lt_one.trans hq1) hp1pos)⟩

lemma geom_tail_eq {p : ℚ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    ((1 / p) ^ 2) / (1 - 1 / p) = 1 / (p * (p - 1)) := by
  have hpow : (1 / p) ^ 2 = 1 / p ^ 2 := by rw [div_pow, one_pow]
  have hden : (1 : ℚ) - 1 / p = (p - 1) / p := by rw [← div_self hp0, sub_div]
  rw [hpow, hden]
  field_simp [hp0, sub_ne_zero.mpr (Ne.symm hp1)]

lemma fSum_prime_pow_lt_tight {p k : ℕ} (hp : p.Prime) :
    fSum (p ^ k) <
      (1 : ℚ) + 1 / ((p : ℚ) + 1) + 1 / ((p : ℚ) * (p - 1)) := by
  have hq1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℚ) ≠ 1 := hq1.ne'
  have hr1 : (1 : ℚ) / p < 1 := (div_lt_one (zero_lt_one.trans hq1)).mpr hq1
  have ⟨hpos1, hpos2⟩ := tight_pos hp.two_le
  rw [fSum_prime_pow hp]
  cases lt_or_ge k 2 with
  | inl hk =>
    interval_cases k
    · rw [sum_range_one, pow_zero, sigma_one, Nat.cast_one, div_one]
      simpa [add_assoc] using
        (lt_add_of_pos_right (1 : ℚ) (add_pos hpos1 hpos2))
    · rw [sum_range_succ, sum_range_one, pow_zero, pow_one, sigma_one, sigma_prime hp]
      push_cast
      linarith [hpos2]
  | inr hk =>
    have h0mem : 0 ∈ range (k + 1) := by simp
    have h1mem : 1 ∈ (range (k + 1)).erase 0 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h0mem]
    have hterm0 : (1 : ℚ) / (sigma 1 (p ^ 0) : ℚ) = 1 := by simp [sigma_one]
    rw [hterm0, ← add_sum_erase _ _ h1mem]
    have hterm1 : (1 : ℚ) / (sigma 1 (p ^ 1) : ℚ) = 1 / ((p : ℚ) + 1) := by
      rw [pow_one, sigma_prime hp]
      norm_cast
    rw [hterm1]
    have hset : ((range (k + 1)).erase 0).erase 1 = Icc 2 k := by
      ext j; simp [mem_erase, mem_range, mem_Icc]; omega
    rw [hset]
    have hI : Icc 2 k = Ico 2 (k + 1) := by
      ext j
      simp [mem_Icc, mem_Ico]
    have hrest :
        ∑ j ∈ Icc 2 k, (1 : ℚ) / (sigma 1 (p ^ j) : ℚ) <
          1 / ((p : ℚ) * (p - 1)) := by
      have hle : ∑ j ∈ Icc 2 k, (1 : ℚ) / (sigma 1 (p ^ j) : ℚ) <
          ∑ j ∈ Icc 2 k, (1 / (p : ℚ)) ^ j := by
        refine sum_lt_sum (fun j hj => ?_) ⟨2, by simp [mem_Icc]; omega, ?_⟩
        · have hj1 : 1 ≤ j := le_trans (by decide : (1 : ℕ) ≤ 2) (mem_Icc.mp hj).1
          exact ((inv_sigma_lt_pow hp hj1).le).trans_eq (one_div_pow _ _).symm
        · exact (inv_sigma_lt_pow hp (by decide : (1 : ℕ) ≤ 2)).trans_eq
            (one_div_pow _ _).symm
      have hgeom : ∑ j ∈ Icc 2 k, (1 / (p : ℚ)) ^ j ≤
          ((1 / (p : ℚ)) ^ 2) / (1 - 1 / p) := by
        rw [hI]
        exact geom_sum_Ico_le_of_lt_one (by positivity) hr1
      exact hle.trans_le (hgeom.trans_eq (geom_tail_eq hp0 hp1))
    linarith

lemma geom_tail3_eq {p : ℚ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    ((1 / p) ^ 3) / (1 - 1 / p) = 1 / (p ^ 2 * (p - 1)) := by
  have hpow : (1 / p) ^ 3 = 1 / p ^ 3 := by rw [div_pow, one_pow]
  have hden : (1 : ℚ) - 1 / p = (p - 1) / p := by rw [← div_self hp0, sub_div]
  rw [hpow, hden]
  field_simp [hp0, sub_ne_zero.mpr (Ne.symm hp1)]

lemma fSum_prime_pow_lt_tight3 {p k : ℕ} (hp : p.Prime) :
    fSum (p ^ k) <
      (1 : ℚ) + 1 / ((p : ℚ) + 1) + 1 / (1 + p + p ^ 2) +
        1 / ((p : ℚ) ^ 2 * (p - 1)) := by
  have hq1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℚ) ≠ 1 := hq1.ne'
  have hr1 : (1 : ℚ) / p < 1 := (div_lt_one (zero_lt_one.trans hq1)).mpr hq1
  have hpos1 : (0 : ℚ) < 1 / ((p : ℚ) + 1) :=
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)
  have hpos2 : (0 : ℚ) < 1 / (1 + (p : ℚ) + p ^ 2) := by positivity
  have hpos3 : (0 : ℚ) < 1 / ((p : ℚ) ^ 2 * (p - 1)) :=
    one_div_pos.mpr (mul_pos (pow_pos (zero_lt_one.trans hq1) 2) (sub_pos.mpr hq1))
  rw [fSum_prime_pow hp]
  cases lt_or_ge k 3 with
  | inl hk =>
    interval_cases k
    · rw [sum_range_one, pow_zero, sigma_one, Nat.cast_one, div_one]
      simpa [add_assoc] using
        (lt_add_of_pos_right (1 : ℚ) (add_pos hpos1 (add_pos hpos2 hpos3)))
    · rw [sum_range_succ, sum_range_one, pow_zero, pow_one, sigma_one, sigma_prime hp]
      push_cast
      linarith [hpos2, hpos3]
    · rw [sum_range_succ, sum_range_succ, sum_range_one, pow_zero, pow_one,
        sigma_one, sigma_prime hp]
      have hs2 : (sigma 1 (p ^ 2) : ℚ) = 1 + p + p ^ 2 := by
        rw [sigma_eq_geom hp]
        simp [sum_range_succ, pow_zero, pow_one, pow_two]
      rw [hs2]
      push_cast
      linarith [hpos3]
  | inr hk =>
    have h0mem : 0 ∈ range (k + 1) := by simp
    have h1mem : 1 ∈ (range (k + 1)).erase 0 := by simp [mem_erase]; omega
    have h2mem : 2 ∈ ((range (k + 1)).erase 0).erase 1 := by simp [mem_erase]; omega
    rw [← add_sum_erase _ _ h0mem]
    have hterm0 : (1 : ℚ) / (sigma 1 (p ^ 0) : ℚ) = 1 := by simp [sigma_one]
    rw [hterm0, ← add_sum_erase _ _ h1mem]
    have hterm1 : (1 : ℚ) / (sigma 1 (p ^ 1) : ℚ) = 1 / ((p : ℚ) + 1) := by
      rw [pow_one, sigma_prime hp]; norm_cast
    rw [hterm1, ← add_sum_erase _ _ h2mem]
    have hterm2 : (1 : ℚ) / (sigma 1 (p ^ 2) : ℚ) = 1 / (1 + p + p ^ 2) := by
      have hs2 : (sigma 1 (p ^ 2) : ℚ) = 1 + p + p ^ 2 := by
        rw [sigma_eq_geom hp]
        simp [sum_range_succ, pow_zero, pow_one, pow_two]
      rw [hs2]
    rw [hterm2]
    have hset : (((range (k + 1)).erase 0).erase 1).erase 2 = Icc 3 k := by
      ext j; simp [mem_erase, mem_range, mem_Icc]; omega
    rw [hset]
    have hI : Icc 3 k = Ico 3 (k + 1) := by
      ext j; simp [mem_Icc, mem_Ico]
    have hrest :
        ∑ j ∈ Icc 3 k, (1 : ℚ) / (sigma 1 (p ^ j) : ℚ) <
          1 / ((p : ℚ) ^ 2 * (p - 1)) := by
      have hle : ∑ j ∈ Icc 3 k, (1 : ℚ) / (sigma 1 (p ^ j) : ℚ) <
          ∑ j ∈ Icc 3 k, (1 / (p : ℚ)) ^ j := by
        refine sum_lt_sum (fun j hj => ?_) ⟨3, by simp [mem_Icc]; omega, ?_⟩
        · have hj1 : 1 ≤ j := le_trans (by decide : (1 : ℕ) ≤ 3) (mem_Icc.mp hj).1
          exact ((inv_sigma_lt_pow hp hj1).le).trans_eq (one_div_pow _ _).symm
        · exact (inv_sigma_lt_pow hp (by decide : (1 : ℕ) ≤ 3)).trans_eq
            (one_div_pow _ _).symm
      have hgeom : ∑ j ∈ Icc 3 k, (1 / (p : ℚ)) ^ j ≤
          ((1 / (p : ℚ)) ^ 3) / (1 - 1 / p) := by
        rw [hI]
        exact geom_sum_Ico_le_of_lt_one (by positivity) hr1
      exact hle.trans_le (hgeom.trans_eq (geom_tail3_eq hp0 hp1))
    linarith

lemma fSum_prime_pow_lt_tight_of_ge {r q k : ℕ}
    (hq : q.Prime) (hr2 : 2 ≤ r) (hrq : r ≤ q) :
    fSum (q ^ k) <
      (1 : ℚ) + 1 / ((r : ℚ) + 1) + 1 / ((r : ℚ) * (r - 1)) := by
  have h1 := fSum_prime_pow_lt_tight (p := q) (k := k) hq
  have hqQ : (r : ℚ) ≤ q := by exact_mod_cast hrq
  have hr1 : (1 : ℚ) < r :=
    by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hr2)
  have hA : (1 : ℚ) / ((q : ℚ) + 1) ≤ 1 / ((r : ℚ) + 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hB : (1 : ℚ) / ((q : ℚ) * (q - 1)) ≤ 1 / ((r : ℚ) * (r - 1)) := by
    refine one_div_le_one_div_of_le ?_ ?_
    · exact mul_pos (zero_lt_one.trans hr1) (sub_pos.mpr hr1)
    · nlinarith [Nat.cast_nonneg (α := ℚ) r, Nat.cast_nonneg (α := ℚ) q]
  linarith

lemma geom_anti_of_le {r q : ℕ} (hr2 : 2 ≤ r) (hrq : r ≤ q) :
    (q : ℚ) / (q - 1) ≤ (r : ℚ) / (r - 1) := by
  have hr1 : (1 : ℚ) < r :=
    by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hr2)
  have hq1 : (1 : ℚ) < q := lt_of_lt_of_le hr1 (by exact_mod_cast hrq)
  have heq : (q : ℚ) / (q - 1) = 1 + 1 / (q - 1) := by
    have hqm : (q : ℚ) - 1 ≠ 0 := (sub_pos.mpr hq1).ne'
    calc (q : ℚ) / (q - 1)
        = ((q - 1) + 1) / (q - 1) := by ring
      _ = 1 + 1 / (q - 1) := by rw [add_div, div_self hqm]
  have heqr : (r : ℚ) / (r - 1) = 1 + 1 / (r - 1) := by
    have hrm : (r : ℚ) - 1 ≠ 0 := (sub_pos.mpr hr1).ne'
    calc (r : ℚ) / (r - 1)
        = ((r - 1) + 1) / (r - 1) := by ring
      _ = 1 + 1 / (r - 1) := by rw [add_div, div_self hrm]
  have hrqQ : (r : ℚ) ≤ q := by exact_mod_cast hrq
  have hle : (1 : ℚ) / (q - 1) ≤ 1 / (r - 1) :=
    one_div_le_one_div_of_le (sub_pos.mpr hr1) (by linarith [hrqQ])
  linarith [heq, heqr, hle]

lemma not_prime_six : ¬ Nat.Prime 6 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 3 = 6) (by decide) (by decide)

lemma not_prime_eight : ¬ Nat.Prime 8 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 4 = 8) (by decide) (by decide)

lemma not_prime_nine : ¬ Nat.Prime 9 :=
  Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 3 = 9) (by decide) (by decide)

lemma not_prime_ten : ¬ Nat.Prime 10 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 5 = 10) (by decide) (by decide)

lemma not_prime_twelve : ¬ Nat.Prime 12 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 6 = 12) (by decide) (by decide)

lemma not_prime_fourteen : ¬ Nat.Prime 14 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 7 = 14) (by decide) (by decide)

lemma not_prime_fifteen : ¬ Nat.Prime 15 :=
  Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 5 = 15) (by decide) (by decide)

lemma not_prime_sixteen : ¬ Nat.Prime 16 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 8 = 16) (by decide) (by decide)

lemma not_prime_eighteen : ¬ Nat.Prime 18 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 9 = 18) (by decide) (by decide)

lemma not_prime_twenty : ¬ Nat.Prime 20 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 10 = 20) (by decide) (by decide)

lemma not_prime_twentyone : ¬ Nat.Prime 21 :=
  Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 7 = 21) (by decide) (by decide)

lemma not_prime_twentytwo : ¬ Nat.Prime 22 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 11 = 22) (by decide) (by decide)

lemma not_prime_twentyfour : ¬ Nat.Prime 24 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 12 = 24) (by decide) (by decide)

lemma not_prime_twentyfive : ¬ Nat.Prime 25 :=
  Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 5 = 25) (by decide) (by decide)

lemma not_prime_twentysix : ¬ Nat.Prime 26 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 13 = 26) (by decide) (by decide)

lemma not_prime_twentyseven : ¬ Nat.Prime 27 :=
  Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 9 = 27) (by decide) (by decide)

lemma not_prime_twentyeight : ¬ Nat.Prime 28 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 14 = 28) (by decide) (by decide)

lemma eq_five_of_prime_lt_seven {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p < 7) :
    p = 5 := by
  have : p ≠ 6 := fun h => not_prime_six (h ▸ hp)
  omega

lemma prime_ge_eleven_of_ge_seven_ne {q : ℕ}
    (hq : q.Prime) (h7 : 7 ≤ q) (hne : q ≠ 7) : 11 ≤ q := by
  have : q ≠ 8 := fun h => not_prime_eight (h ▸ hq)
  have : q ≠ 9 := fun h => not_prime_nine (h ▸ hq)
  have : q ≠ 10 := fun h => not_prime_ten (h ▸ hq)
  omega

lemma prime_ge_thirteen_of_ge_eleven_ne {q : ℕ}
    (hq : q.Prime) (h11 : 11 ≤ q) (hne : q ≠ 11) : 13 ≤ q := by
  have : q ≠ 12 := fun h => not_prime_twelve (h ▸ hq)
  omega

lemma prime_ge_seventeen_of_ge_thirteen_ne {q : ℕ}
    (hq : q.Prime) (h13 : 13 ≤ q) (hne : q ≠ 13) : 17 ≤ q := by
  have : q ≠ 14 := fun h => not_prime_fourteen (h ▸ hq)
  have : q ≠ 15 := fun h => not_prime_fifteen (h ▸ hq)
  have : q ≠ 16 := fun h => not_prime_sixteen (h ▸ hq)
  omega

lemma prime_mem_seven_eleven {q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q) (h11 : q ≤ 11) :
    q = 7 ∨ q = 11 := by
  have : q ≠ 8 := fun h => not_prime_eight (h ▸ hq)
  have : q ≠ 9 := fun h => not_prime_nine (h ▸ hq)
  have : q ≠ 10 := fun h => not_prime_ten (h ▸ hq)
  omega

lemma prime_mem_thirteen_seventeen_nineteen {q : ℕ}
    (hq : q.Prime) (h13 : 13 ≤ q) (h19 : q ≤ 19) :
    q = 13 ∨ q = 17 ∨ q = 19 := by
  have : q ≠ 14 := fun h => not_prime_fourteen (h ▸ hq)
  have : q ≠ 15 := fun h => not_prime_fifteen (h ▸ hq)
  have : q ≠ 16 := fun h => not_prime_sixteen (h ▸ hq)
  have : q ≠ 18 := fun h => not_prime_eighteen (h ▸ hq)
  omega

lemma prime_ge_twentythree_of_ge_nineteen_ne {q : ℕ}
    (hq : q.Prime) (h19 : 19 ≤ q) (hne : q ≠ 19) : 23 ≤ q := by
  have : q ≠ 20 := fun h => not_prime_twenty (h ▸ hq)
  have : q ≠ 21 := fun h => not_prime_twentyone (h ▸ hq)
  have : q ≠ 22 := fun h => not_prime_twentytwo (h ▸ hq)
  omega

lemma prime_ge_twentynine_of_ge_twentythree_ne {q : ℕ}
    (hq : q.Prime) (h23 : 23 ≤ q) (hne : q ≠ 23) : 29 ≤ q := by
  have : q ≠ 24 := fun h => not_prime_twentyfour (h ▸ hq)
  have : q ≠ 25 := fun h => not_prime_twentyfive (h ▸ hq)
  have : q ≠ 26 := fun h => not_prime_twentysix (h ▸ hq)
  have : q ≠ 27 := fun h => not_prime_twentyseven (h ▸ hq)
  have : q ≠ 28 := fun h => not_prime_twentyeight (h ▸ hq)
  omega

lemma fSum_le_of_exp_ge_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    fSum p ≤ fSum (p ^ k) := by
  cases Nat.eq_or_lt_of_le hk with
  | inl h => subst h; rw [pow_one]
  | inr h => simpa [pow_one] using (fSum_strict_mono_prime_pow hp h).le

lemma fSum_le_of_exp_ge {p a b : ℕ} (hp : p.Prime) (h : a ≤ b) :
    fSum (p ^ a) ≤ fSum (p ^ b) := by
  cases Nat.eq_or_lt_of_le h with
  | inl h => rw [h]
  | inr h => exact (fSum_strict_mono_prime_pow hp h).le

lemma fSum_seven : fSum 7 = (9 : ℚ) / 8 := by
  rw [fSum_prime (by decide : Nat.Prime 7)]; norm_num

lemma fSum_eleven : fSum 11 = (13 : ℚ) / 12 := by
  rw [fSum_prime (by decide : Nat.Prime 11)]; norm_num

lemma fSum_nineteen : fSum 19 = (21 : ℚ) / 20 := by
  rw [fSum_prime (by decide : Nat.Prime 19)]; norm_num

lemma fSum_twentythree : fSum 23 = (25 : ℚ) / 24 := by
  rw [fSum_prime (by decide : Nat.Prime 23)]; norm_num

lemma fSum_seven_sq : fSum (7 ^ 2) = (521 : ℚ) / 456 := by
  rw [fSum_prime_sq (by decide : Nat.Prime 7)]; norm_num

lemma fSum_eleven_sq : fSum (11 ^ 2) = (1741 : ℚ) / 1596 := by
  rw [fSum_prime_sq (by decide : Nat.Prime 11)]; norm_num

lemma fSum_five_cu : fSum (5 ^ 3) = (1943 : ℚ) / 1612 := by
  rw [fSum_prime_pow Nat.prime_five]
  simp [sum_range_succ, sigma_one, sigma_prime Nat.prime_five, sigma_eq_geom Nat.prime_five]
  norm_num

lemma fSum_five_four : fSum (5 ^ 4) = (1519095 : ℚ) / 1258972 := by
  rw [fSum_prime_pow Nat.prime_five]
  simp [sum_range_succ, sigma_one, sigma_prime Nat.prime_five, sigma_eq_geom Nat.prime_five]
  norm_num

lemma fSum_five_five_pow : fSum (5 ^ 5) = (95723291 : ℚ) / 79315236 := by
  rw [fSum_prime_pow Nat.prime_five]
  simp [sum_range_succ, sigma_one, sigma_prime Nat.prime_five, sigma_eq_geom Nat.prime_five]
  norm_num

lemma fSum_twentythree_sq : fSum (23 ^ 2) = (13849 : ℚ) / 13272 := by
  rw [fSum_prime_sq (by decide : Nat.Prime 23)]; norm_num

lemma fSum_two_five_twentythree_ne_two
    {kp kq : ℕ} (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq) (hk2 : 2 ≤ kp) :
    fSum (2 ^ 5) * fSum (5 ^ kp) * fSum (23 ^ kq) ≠ 2 := by
  have h2pos : 0 < fSum (2 ^ 5) := fSum_pos (pow_ne_zero 5 two_ne_zero)
  have h5pos : 0 < fSum (5 ^ kp) :=
    fSum_pos (pow_ne_zero kp (show (5 : ℕ) ≠ 0 by decide))
  have h23pos : 0 < fSum (23 ^ kq) :=
    fSum_pos (pow_ne_zero kq (show (23 : ℕ) ≠ 0 by decide))
  have hP : Nat.Prime 23 := by decide
  have h5P : Nat.Prime 5 := Nat.prime_five
  cases lt_or_ge kq 2 with
  | inl hkq1 =>
    have : kq = 1 := by omega
    subst this
    have hkp234 : kp = 2 ∨ kp = 3 ∨ kp = 4 ∨ 5 ≤ kp := by omega
    rcases hkp234 with hkpeq | hkpeq | hkpeq | hkp5
    · subst hkpeq
      have : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 23 < 2 := by
        rw [fSum_two_pow_five, fSum_five_sq, fSum_twentythree]; norm_num
      simpa [pow_one] using this.ne
    · subst hkpeq
      have : fSum (2 ^ 5) * fSum (5 ^ 3) * fSum 23 < 2 := by
        rw [fSum_two_pow_five, fSum_five_cu, fSum_twentythree]; norm_num
      simpa [pow_one] using this.ne
    · subst hkpeq
      have : fSum (2 ^ 5) * fSum (5 ^ 4) * fSum 23 < 2 := by
        rw [fSum_two_pow_five, fSum_five_four, fSum_twentythree]; norm_num
      simpa [pow_one] using this.ne
    · have h55 : fSum (5 ^ 5) ≤ fSum (5 ^ kp) := fSum_le_of_exp_ge h5P hkp5
      have hmin : 2 < fSum (2 ^ 5) * fSum (5 ^ 5) * fSum 23 := by
        rw [fSum_two_pow_five, fSum_five_five_pow, fSum_twentythree]; norm_num
      have hmono := mul3_gt_of le_rfl h55 le_rfl
        (fSum_pos (pow_ne_zero 5 (show (5 : ℕ) ≠ 0 by decide))).le h2pos.le
        (fSum_pos (show (23 : ℕ) ≠ 0 by decide)).le
        (mul_nonneg h2pos.le h5pos.le)
      simpa [pow_one] using (lt_of_lt_of_le hmin hmono).ne.symm
  | inr hkq2 =>
    cases lt_or_ge kp 3 with
    | inl hkp2 =>
      have : kp = 2 := by omega
      subst this
      have hσt := fSum_prime_pow_lt_tight (p := 23) (k := kq) hP
      have hprod : fSum (2 ^ 5) * fSum (5 ^ 2) *
          (1 + 1 / ((23 : ℚ) + 1) + 1 / ((23 : ℚ) * (23 - 1))) < 2 := by
        rw [fSum_two_pow_five, fSum_five_sq]; norm_num
      have : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (23 ^ kq) <
          fSum (2 ^ 5) * fSum (5 ^ 2) *
            (1 + 1 / ((23 : ℚ) + 1) + 1 / ((23 : ℚ) * (23 - 1))) :=
        mul_lt_mul_of_pos_left hσt
          (mul_pos h2pos (fSum_pos (pow_ne_zero 2 (show (5 : ℕ) ≠ 0 by decide))))
      exact ne_of_lt (this.trans hprod)
    | inr hkp3 =>
      have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) := fSum_le_of_exp_ge h5P hkp3
      have h232 : fSum (23 ^ 2) ≤ fSum (23 ^ kq) := fSum_le_of_exp_ge hP hkq2
      have hmin : 2 < fSum (2 ^ 5) * fSum (5 ^ 3) * fSum (23 ^ 2) := by
        rw [fSum_two_pow_five, fSum_five_cu, fSum_twentythree_sq]; norm_num
      have hmono := mul3_gt_of le_rfl h53 h232
        (fSum_pos (pow_ne_zero 3 (show (5 : ℕ) ≠ 0 by decide))).le h2pos.le
        (fSum_pos (pow_ne_zero 2 (show (23 : ℕ) ≠ 0 by decide))).le
        (mul_nonneg h2pos.le h5pos.le)
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)

lemma fs5_tight7_tight11_lt_two :
    fSum (2 ^ 5) *
      ((1 : ℚ) + 1 / (7 + 1) + 1 / (7 * (7 - 1))) *
      ((1 : ℚ) + 1 / (11 + 1) + 1 / (11 * (11 - 1))) < 2 := by
  rw [fSum_two_pow_five]; norm_num

lemma fSum_two_pow_five_both_ge5_ne_two
    {p q kp kq : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq) :
    fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) ≠ 2 := by
  wlog hle : p ≤ q generalizing p q kp kq
  · have hswap : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) =
        fSum (2 ^ 5) * fSum (q ^ kq) * fSum (p ^ kp) := by ring
    rw [hswap]
    exact this hq hp hpq.symm hq5 hp5 hqkp hpkp (le_of_lt (lt_of_not_ge hle))
  have h2pos : 0 < fSum (2 ^ 5) := fSum_pos (pow_ne_zero 5 two_ne_zero)
  have hppos : 0 < fSum (p ^ kp) := fSum_pos (pow_ne_zero kp hp.ne_zero)
  have hqpos : 0 < fSum (q ^ kq) := fSum_pos (pow_ne_zero kq hq.ne_zero)
  cases lt_or_ge p 7 with
  | inr hp7 =>
    have hq11 : 11 ≤ q := by
      have hq7 : 7 ≤ q := le_trans hp7 hle
      have hne7 : q ≠ 7 := fun h => hpq (le_antisymm hle (h ▸ hp7))
      exact prime_ge_eleven_of_ge_seven_ne hq hq7 hne7
    have hpB : fSum (p ^ kp) <
        (1 : ℚ) + 1 / (7 + 1) + 1 / (7 * (7 - 1)) :=
      fSum_prime_pow_lt_tight_of_ge (r := 7) (q := p) (k := kp) hp (by decide) hp7
    have hqB : fSum (q ^ kq) <
        (1 : ℚ) + 1 / (11 + 1) + 1 / (11 * (11 - 1)) :=
      fSum_prime_pow_lt_tight_of_ge (r := 11) (q := q) (k := kq) hq (by decide) hq11
    have hmul1 : fSum (2 ^ 5) * fSum (p ^ kp) <
        fSum (2 ^ 5) * (1 + 1 / ((7 : ℚ) + 1) + 1 / (7 * (7 - 1))) :=
      mul_lt_mul_of_pos_left hpB h2pos
    have hmul2 : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) <
        fSum (2 ^ 5) * (1 + 1 / ((7 : ℚ) + 1) + 1 / (7 * (7 - 1))) *
          (1 + 1 / ((11 : ℚ) + 1) + 1 / (11 * (11 - 1))) :=
      mul_lt_mul hmul1 hqB.le hqpos (mul_nonneg h2pos.le (by positivity))
    exact ne_of_lt (hmul2.trans fs5_tight7_tight11_lt_two)
  | inl hp5lt =>
    have hp_eq : p = 5 := eq_five_of_prime_lt_seven hp hp5 hp5lt
    subst hp_eq
    have hq7 : 7 ≤ q := by
      have : q ≠ 5 := hpq.symm
      have : q ≠ 6 := fun h => not_prime_six (h ▸ hq)
      omega
    have h5le : fSum 5 ≤ fSum (5 ^ kp) := fSum_le_of_exp_ge_one hp hpkp
    by_cases hq11le : q ≤ 11
    · have hqmem : q = 7 ∨ q = 11 := prime_mem_seven_eleven hq hq7 hq11le
      have hmin : 2 < fSum (2 ^ 5) * fSum 5 * fSum q := by
        rcases hqmem with h | h
        · subst h
          rw [fSum_two_pow_five, fSum_five, fSum_prime (by decide : Nat.Prime 7)]
          norm_num
        · subst h
          rw [fSum_two_pow_five, fSum_five, fSum_prime (by decide : Nat.Prime 11)]
          norm_num
      have hqleP : fSum q ≤ fSum (q ^ kq) := by
        cases Nat.eq_or_lt_of_le hqkp with
        | inl h => subst h; rw [pow_one]
        | inr h => simpa [pow_one] using (fSum_strict_mono_prime_pow hq h).le
      have hmono := mul3_gt_of le_rfl h5le hqleP
        (fSum_pos (show (5:ℕ) ≠ 0 by decide)).le h2pos.le
        (fSum_pos hq.ne_zero).le
        (mul_nonneg h2pos.le (fSum_pos (pow_ne_zero kp (show (5:ℕ) ≠ 0 by decide))).le)
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
    · have hq13 : 13 ≤ q := by
        have : 11 ≤ q := by omega
        have : q ≠ 11 := fun h => (lt_of_not_ge hq11le).ne.symm (by omega)
        exact prime_ge_thirteen_of_ge_eleven_ne hq (by omega) (by
          intro h; subst h; exact hq11le (by decide))
      cases lt_or_ge kp 2 with
      | inl hk1 =>
        have hkpeq : kp = 1 := by omega
        subst hkpeq
        have hσ := fSum_prime_pow_lt_geom (l := kq) hq
        by_cases hqeq13 : q = 13
        · subst hqeq13
          have hσt := fSum_prime_pow_lt_tight3 (p := 13) (k := kq) (by decide)
          have hprod : fSum (2 ^ 5) * fSum (5 ^ 1) *
              ((1 : ℚ) + 1 / (13 + 1) + 1 / (1 + 13 + 13 ^ 2) +
                1 / ((13 : ℚ) ^ 2 * (13 - 1))) < 2 := by
            rw [pow_one, fSum_two_pow_five, fSum_five]; norm_num
          have : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (13 ^ kq) <
              fSum (2 ^ 5) * fSum (5 ^ 1) *
                ((1 : ℚ) + 1 / (13 + 1) + 1 / (1 + 13 + 13 ^ 2) +
                  1 / ((13 : ℚ) ^ 2 * (13 - 1))) :=
            mul_lt_mul_of_pos_left hσt
              (mul_pos h2pos (fSum_pos (pow_ne_zero 1 (show (5 : ℕ) ≠ 0 by decide))))
          exact ne_of_lt (this.trans hprod)
        · have hq17 : 17 ≤ q :=
            prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqeq13
          have hqg17 : (q : ℚ) / (q - 1) ≤ (17 : ℚ) / 16 := by
            have hqQ : (17 : ℚ) ≤ q := by exact_mod_cast hq17
            have hqm : (0 : ℚ) < (q : ℚ) - 1 := by
              have : (1 : ℚ) < q := by exact_mod_cast hq.one_lt
              linarith
            have heq : (q : ℚ) / (q - 1) = 1 + 1 / (q - 1) := by field_simp; ring
            have : (1 : ℚ) / (q - 1) ≤ 1 / 16 :=
              one_div_le_one_div_of_le (by norm_num) (by linarith)
            have : (17 : ℚ) / 16 = 1 + 1 / 16 := by norm_num
            linarith
          have hprod : fSum (2 ^ 5) * fSum (5 ^ 1) * ((17 : ℚ) / 16) < 2 := by
            rw [pow_one, fSum_two_pow_five, fSum_five]; norm_num
          have : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (q ^ kq) <
              fSum (2 ^ 5) * fSum (5 ^ 1) * ((17 : ℚ) / 16) :=
            mul_lt_mul_of_pos_left (hσ.trans_le hqg17)
              (mul_pos h2pos (fSum_pos (pow_ne_zero 1 (show (5:ℕ) ≠ 0 by decide))))
          exact ne_of_lt (this.trans hprod)
      | inr hk2 =>
        have h52 : fSum (5 ^ 2) ≤ fSum (5 ^ kp) := by
          cases Nat.eq_or_lt_of_le hk2 with
          | inl h => rw [h]
          | inr h => exact (fSum_strict_mono_prime_pow hp h).le
        have hqleP : fSum q ≤ fSum (q ^ kq) := by
          cases Nat.eq_or_lt_of_le hqkp with
          | inl h => subst h; rw [pow_one]
          | inr h => simpa [pow_one] using (fSum_strict_mono_prime_pow hq h).le
        by_cases hqle19 : q ≤ 19
        · have hqmem := prime_mem_thirteen_seventeen_nineteen hq hq13 hqle19
          have hmin : 2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum q := by
            rcases hqmem with h | h | h
            · subst h; rw [fSum_two_pow_five, fSum_five_sq, fSum_thirteen]; norm_num
            · subst h; rw [fSum_two_pow_five, fSum_five_sq, fSum_seventeen]; norm_num
            · subst h; rw [fSum_two_pow_five, fSum_five_sq, fSum_nineteen]; norm_num
          have hmono := mul3_gt_of le_rfl h52 hqleP
            (fSum_pos (pow_ne_zero 2 (show (5 : ℕ) ≠ 0 by decide))).le h2pos.le
            (fSum_pos hq.ne_zero).le
            (mul_nonneg h2pos.le hppos.le)
          exact ne_of_gt (lt_of_lt_of_le hmin hmono)
        · have hq23 : 23 ≤ q :=
            prime_ge_twentythree_of_ge_nineteen_ne hq (by omega) (by
              intro h; subst h; exact hqle19 (by decide))
          by_cases hqeq23 : q = 23
          · subst hqeq23
            exact fSum_two_five_twentythree_ne_two hpkp hqkp hk2
          · have hq29 : 29 ≤ q :=
              prime_ge_twentynine_of_ge_twentythree_ne hq hq23 hqeq23
            have h5b := fSum_prime_pow_lt_tight3 (p := 5) (k := kp) Nat.prime_five
            have hσ := fSum_prime_pow_lt_geom (l := kq) hq
            have hqg : (q : ℚ) / (q - 1) ≤ (29 : ℚ) / 28 := by
              convert geom_anti_of_le (by decide : (2 : ℕ) ≤ 29) hq29
              norm_num
            have hprod : fSum (2 ^ 5) *
                ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
                  1 / ((5 : ℚ) ^ 2 * (5 - 1))) * ((29 : ℚ) / 28) < 2 := by
              rw [fSum_two_pow_five]; norm_num
            have hmul1 : fSum (2 ^ 5) * fSum (5 ^ kp) <
                fSum (2 ^ 5) * ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
                  1 / ((5 : ℚ) ^ 2 * (5 - 1))) :=
              mul_lt_mul_of_pos_left h5b h2pos
            have hmul2 : fSum (2 ^ 5) * fSum (5 ^ kp) * fSum (q ^ kq) <
                fSum (2 ^ 5) * ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
                  1 / ((5 : ℚ) ^ 2 * (5 - 1))) * ((29 : ℚ) / 28) :=
              mul_lt_mul hmul1 (hσ.trans_le hqg).le hqpos (by positivity)
            exact ne_of_lt (hmul2.trans hprod)

lemma fSum_two_pow_ge_seven {a : ℕ} (ha : 7 ≤ a) :
    (8 : ℚ) / 5 < fSum (2 ^ a) := by
  have hle : fSum (2 ^ 7) ≤ fSum (2 ^ a) := by
    cases Nat.lt_or_eq_of_le ha with
    | inl h => exact (fSum_strict_mono_two h).le
    | inr h => rw [h]
  exact lt_of_lt_of_le fSum_two_seven_gt_eight_five hle

lemma fSum_two_pow_eight :
    fSum (2 ^ 8) = (2469747943 : ℚ) / 1539032355 := by
  have h :
      fSum (2 ^ 8) = fSum (2 ^ 7) + (1 : ℚ) / (2 ^ 9 - 1 : ℕ) := by
    rw [fSum_two_pow_eq, fSum_two_pow_eq, show range 9 = insert 8 (range 8) by
      ext j; simp [mem_range]; omega]
    rw [sum_insert (by simp)]
    ac_rfl
  rw [h, fSum_two_pow_seven]
  norm_num

lemma fSum_two_eight_seven_eleven_sq_gt_two :
    2 < fSum (2 ^ 8) * fSum (7 ^ 2) * fSum (11 ^ 2) := by
  rw [fSum_two_pow_eight, fSum_seven_sq, fSum_eleven_sq]; norm_num

lemma fSum_two_pow_ge21_seven_eleven_ne_two
    {a kp kq : ℕ} (ha : 21 ≤ a) (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq) :
    fSum (2 ^ a) * fSum (7 ^ kp) * fSum (11 ^ kq) ≠ 2 := by
  have h2pos : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have h7P : Nat.Prime 7 := by decide
  have h11P : Nat.Prime 11 := by decide
  have h2b := fSum_two_pow_lt_161_100 a
  have h8le : fSum (2 ^ 8) ≤ fSum (2 ^ a) :=
    (fSum_strict_mono_two (by omega : (8 : ℕ) < a)).le
  cases Nat.eq_or_lt_of_le hpkp with
  | inl hk1 =>
    subst hk1
    have hσ := fSum_prime_pow_lt_tight (p := 11) (k := kq) h11P
    have hprod : (161 : ℚ) / 100 * fSum 7 *
        (1 + 1 / ((11 : ℚ) + 1) + 1 / (11 * (11 - 1))) < 2 := by
      rw [fSum_seven]; norm_num
    have : fSum (2 ^ a) * fSum (7 ^ 1) * fSum (11 ^ kq) <
        (161 : ℚ) / 100 * fSum 7 *
          (1 + 1 / ((11 : ℚ) + 1) + 1 / (11 * (11 - 1))) := by
      rw [pow_one]
      have h1 : fSum (2 ^ a) * fSum 7 < (161 : ℚ) / 100 * fSum 7 :=
        mul_lt_mul_of_pos_right h2b (fSum_pos (show (7 : ℕ) ≠ 0 by decide))
      exact mul_lt_mul h1 (le_of_lt hσ)
        (fSum_pos (pow_ne_zero kq (show (11 : ℕ) ≠ 0 by decide)))
        (mul_nonneg (by norm_num) (fSum_pos (show (7 : ℕ) ≠ 0 by decide)).le)
    exact ne_of_lt (this.trans hprod)
  | inr hkp2' =>
    have hkp2 : 2 ≤ kp := by omega
    cases Nat.eq_or_lt_of_le hqkp with
    | inl hl1 =>
      subst hl1
      have hσ := fSum_prime_pow_lt_tight3 (p := 7) (k := kp) h7P
      have hprod : (161 : ℚ) / 100 *
          ((1 : ℚ) + 1 / (7 + 1) + 1 / (1 + 7 + 7 ^ 2) +
            1 / ((7 : ℚ) ^ 2 * (7 - 1))) * fSum 11 < 2 := by
        rw [fSum_eleven]; norm_num
      have : fSum (2 ^ a) * fSum (7 ^ kp) * fSum (11 ^ 1) <
          (161 : ℚ) / 100 *
            ((1 : ℚ) + 1 / (7 + 1) + 1 / (1 + 7 + 7 ^ 2) +
              1 / ((7 : ℚ) ^ 2 * (7 - 1))) * fSum 11 := by
        rw [pow_one]
        have h1 : fSum (2 ^ a) * fSum (7 ^ kp) <
            (161 : ℚ) / 100 *
              ((1 : ℚ) + 1 / (7 + 1) + 1 / (1 + 7 + 7 ^ 2) +
                1 / ((7 : ℚ) ^ 2 * (7 - 1))) :=
          mul_lt_mul h2b (le_of_lt hσ)
            (fSum_pos (pow_ne_zero kp (show (7 : ℕ) ≠ 0 by decide))) (by positivity)
        exact mul_lt_mul_of_pos_right h1 (fSum_pos (show (11 : ℕ) ≠ 0 by decide))
      exact ne_of_lt (this.trans hprod)
    | inr hkq2' =>
      have hkq2 : 2 ≤ kq := by omega
      have h72 : fSum (7 ^ 2) ≤ fSum (7 ^ kp) := fSum_le_of_exp_ge h7P hkp2
      have h112 : fSum (11 ^ 2) ≤ fSum (11 ^ kq) := fSum_le_of_exp_ge h11P hkq2
      have hmin := fSum_two_eight_seven_eleven_sq_gt_two
      have hmono := mul3_gt_of h8le h72 h112
        (fSum_pos (pow_ne_zero 2 (show (7 : ℕ) ≠ 0 by decide))).le
        (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (pow_ne_zero 2 (show (11 : ℕ) ≠ 0 by decide))).le
        (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kp (show (7 : ℕ) ≠ 0 by decide))).le)
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)



lemma fSum_twenty_nine : fSum 29 = (31 : ℚ) / 30 := by
  rw [fSum_prime (by decide : Nat.Prime 29)]; norm_num

lemma exp_le_two_of_v2_eq_neg_one {p k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hk : 1 ≤ k)
    (hv : padicValRat 2 (fSum (p ^ k)) = -1) :
    k ≤ 2 := by
  haveI := two_fact
  have hform := v2_fSum_eq_one_sub hp hpo hk
  rw [hform] at hv
  have hv2p : 1 ≤ padicValNat 2 (p + 1) :=
    one_le_padicValNat_of_dvd (by omega)
      (even_iff_two_dvd.mp (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hpo)))
  have hlog : 1 ≤ Nat.log 2 (k + 1) := Nat.log_pos (by decide) (by omega)
  have hlog1 : Nat.log 2 (k + 1) = 1 := by omega
  have hlt : k + 1 < 2 ^ (Nat.log 2 (k + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (k + 1)
  rw [hlog1] at hlt
  omega

lemma mod4_one_of_v2_eq_neg_one {p k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hk : 1 ≤ k)
    (hv : padicValRat 2 (fSum (p ^ k)) = -1) :
    p ≡ 1 [MOD 4] := by
  haveI := two_fact
  have hform := v2_fSum_eq_one_sub hp hpo hk
  rw [hform] at hv
  have hv2p : 1 ≤ padicValNat 2 (p + 1) :=
    one_le_padicValNat_of_dvd (by omega)
      (even_iff_two_dvd.mp (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hpo)))
  have hlog : 1 ≤ Nat.log 2 (k + 1) := Nat.log_pos (by decide) (by omega)
  have hv1 : padicValNat 2 (p + 1) = 1 := by omega
  rcases odd_mod4 hpo with h1 | h3
  · exact h1
  · have : 2 ≤ padicValNat 2 (p + 1) :=
      padicValNat_two_add_one_of_mod4_three hpo h3
    omega

lemma exp_le_two_of_log_eq_one {k : ℕ} (hk : 1 ≤ k)
    (hlog : Nat.log 2 (k + 1) = 1) : k ≤ 2 := by
  have hlt : k + 1 < 2 ^ (Nat.log 2 (k + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (k + 1)
  rw [hlog] at hlt
  omega

lemma exp_mid_of_log_eq_two {k : ℕ} (hk : 1 ≤ k)
    (hlog : Nat.log 2 (k + 1) = 2) : 3 ≤ k ∧ k ≤ 6 := by
  have hle : 2 ^ Nat.log 2 (k + 1) ≤ k + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hlt : k + 1 < 2 ^ (Nat.log 2 (k + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (k + 1)
  rw [hlog] at hle hlt
  omega

lemma eight_five_f5_f13_eq_two :
    (8 : ℚ) / 5 * fSum 5 * fSum 13 = 2 := by
  rw [fSum_five, fSum_thirteen]; norm_num

lemma eight_five_f5_f11_gt_two :
    2 < (8 : ℚ) / 5 * fSum 5 * fSum 11 := by
  rw [fSum_five, fSum_eleven]; norm_num

lemma eight_five_f5sq_f17_gt_two :
    2 < (8 : ℚ) / 5 * fSum (5 ^ 2) * fSum 17 := by
  rw [fSum_five_sq, fSum_seventeen]; norm_num

lemma eight_five_f5sq_f19_gt_two :
    2 < (8 : ℚ) / 5 * fSum (5 ^ 2) * fSum 19 := by
  rw [fSum_five_sq, fSum_nineteen]; norm_num

lemma eight_five_f5cu_f13_gt_two :
    2 < (8 : ℚ) / 5 * fSum (5 ^ 3) * fSum 13 := by
  rw [fSum_five_cu, fSum_thirteen]; norm_num

lemma eight_five_f5cu_f17_gt_two :
    2 < (8 : ℚ) / 5 * fSum (5 ^ 3) * fSum 17 := by
  rw [fSum_five_cu, fSum_seventeen]; norm_num

lemma fs161_f5_tight3_17_lt_two :
    (161 : ℚ) / 100 * fSum 5 *
      (1 + 1 / ((17 : ℚ) + 1) + 1 / (1 + 17 + 17 ^ 2) +
        1 / ((17 : ℚ) ^ 2 * (17 - 1))) < 2 := by
  rw [fSum_five]; norm_num

lemma fs161_f5sq_tight3_29_lt_two :
    (161 : ℚ) / 100 * fSum (5 ^ 2) *
      (1 + 1 / ((29 : ℚ) + 1) + 1 / (1 + 29 + 29 ^ 2) +
        1 / ((29 : ℚ) ^ 2 * (29 - 1))) < 2 := by
  rw [fSum_five_sq]; norm_num

lemma fs161_f5_f19sq_lt_two :
    (161 : ℚ) / 100 * fSum 5 * fSum (19 ^ 2) < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 19)]; norm_num

lemma fs161_f5sq_tight43_lt_two :
    (161 : ℚ) / 100 * fSum (5 ^ 2) *
      (1 + 1 / ((43 : ℚ) + 1) + 1 / (43 * (43 - 1))) < 2 := by
  rw [fSum_five_sq]; norm_num

lemma fs161_tight13_tight3_17_lt_two :
    (161 : ℚ) / 100 *
      (1 + 1 / ((13 : ℚ) + 1) + 1 / (13 * (13 - 1))) *
      (1 + 1 / ((17 : ℚ) + 1) + 1 / (1 + 17 + 17 ^ 2) +
        1 / ((17 : ℚ) ^ 2 * (17 - 1))) < 2 := by
  norm_num

lemma fs161_tight13_tight11_lt_two :
    (161 : ℚ) / 100 *
      (1 + 1 / ((13 : ℚ) + 1) + 1 / (13 * (13 - 1))) *
      (1 + 1 / ((11 : ℚ) + 1) + 1 / (11 * (11 - 1))) < 2 := by
  norm_num

lemma fs161_tight3_5_f37sq_lt_two :
    (161 : ℚ) / 100 *
      ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
        1 / ((5 : ℚ) ^ 2 * (5 - 1))) * fSum (37 ^ 2) < 2 := by
  rw [fSum_prime_sq (by decide : Nat.Prime 37)]; norm_num

lemma fSum_two_pow_ge_ten {a : ℕ} (ha : 10 ≤ a) :
    fSum (2 ^ 10) ≤ fSum (2 ^ a) := by
  cases Nat.lt_or_eq_of_le ha with
  | inl h => exact (fSum_strict_mono_two h).le
  | inr h => rw [h]

lemma fSum_two_pow_ten_gt_803_500 :
    (803 : ℚ) / 500 < fSum (2 ^ 10) := by
  have h : fSum (2 ^ 10) =
      fSum (2 ^ 8) + (1 : ℚ) / (2 ^ 10 - 1 : ℕ) + (1 : ℚ) / (2 ^ 11 - 1 : ℕ) := by
    have h9 : fSum (2 ^ 9) = fSum (2 ^ 8) + (1 : ℚ) / (2 ^ 10 - 1 : ℕ) := by
      rw [fSum_two_pow_eq, fSum_two_pow_eq,
        show range 10 = insert 9 (range 9) by ext j; simp [mem_range]; omega]
      rw [sum_insert (by simp)]
      ac_rfl
    have h10 : fSum (2 ^ 10) = fSum (2 ^ 9) + (1 : ℚ) / (2 ^ 11 - 1 : ℕ) := by
      rw [fSum_two_pow_eq, fSum_two_pow_eq,
        show range 11 = insert 10 (range 10) by ext j; simp [mem_range]; omega]
      rw [sum_insert (by simp)]
      ac_rfl
    rw [h10, h9]
  rw [h, fSum_two_pow_eight]
  norm_num

lemma fSum_two_pow_ge21_gt_803_500 {a : ℕ} (ha : 21 ≤ a) :
    (803 : ℚ) / 500 < fSum (2 ^ a) :=
  lt_of_lt_of_le fSum_two_pow_ten_gt_803_500 (fSum_two_pow_ge_ten (by omega))

lemma eight03_f5cu_f29_gt_two :
    2 < (803 : ℚ) / 500 * fSum (5 ^ 3) * fSum 29 := by
  rw [fSum_five_cu, fSum_twenty_nine]; norm_num

lemma ge21_gt_two_of_eight_five {a A B : ℚ}
    (hA : 0 < A) (hB : 0 < B)
    (ha : (8 : ℚ) / 5 < a)
    (hth : 2 ≤ (8 : ℚ) / 5 * A * B) :
    2 < a * A * B := by
  have hmul : (8 : ℚ) / 5 * A * B < a * A * B :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right ha hA) hB
  exact lt_of_le_of_lt hth hmul


lemma ge21_mul3_gt_two {a p kp q kq : ℕ}
    (ha : 21 ≤ a) (hp : p.Prime) (hq : q.Prime)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    {X Y : ℚ} (hX : X ≤ fSum (p ^ kp)) (hY : Y ≤ fSum (q ^ kq))
    (hXpos : 0 < X) (hYpos : 0 < Y)
    (hth : 2 < (8 : ℚ) / 5 * X * Y) :
    2 < fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) := by
  have h27 := fSum_two_pow_ge_seven (by omega : 7 ≤ a)
  have hmin : 2 < fSum (2 ^ a) * X * Y := by
    have : (8 : ℚ) / 5 * X * Y < fSum (2 ^ a) * X * Y :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h27 hXpos) hYpos
    exact hth.trans this
  have hmono := mul3_gt_of le_rfl hX hY hXpos.le
    (fSum_pos (pow_ne_zero a two_ne_zero)).le hYpos.le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (pow_ne_zero kp hp.ne_zero)).le)
  exact lt_of_lt_of_le hmin hmono

lemma ge21_five_eleven_gt_two {a kp kq : ℕ} (ha : 21 ≤ a)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (11 ^ kq) := by
  have h5 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 5) hpkp
  have h11 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 11) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) hpkp hqkp h5 h11
    (fSum_pos (by decide)) (fSum_pos (by decide)) eight_five_f5_f11_gt_two

lemma ge21_five_thirteen_gt_two {a kp kq : ℕ} (ha : 21 ≤ a)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) := by
  have h5 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 5) hpkp
  have h13 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 13) hqkp
  have h27 := fSum_two_pow_ge_seven (by omega : 7 ≤ a)
  have hmin : 2 < fSum (2 ^ a) * fSum 5 * fSum 13 := by
    have heq := eight_five_f5_f13_eq_two
    have : (8 : ℚ) / 5 * fSum 5 * fSum 13 < fSum (2 ^ a) * fSum 5 * fSum 13 :=
      mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right h27 (fSum_pos (by decide)))
        (fSum_pos (by decide))
    linarith [heq]
  have hmono := mul3_gt_of le_rfl h5 h13
    (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le
    (fSum_pos (pow_ne_zero a two_ne_zero)).le
    (fSum_pos (by decide : (13 : ℕ) ≠ 0)).le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
  exact lt_of_lt_of_le hmin hmono

lemma ge21_five_one_seventeen_mid_lt_two {a kq : ℕ} (ha : 21 ≤ a) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have hσ := fSum_prime_pow_lt_tight3 (p := 17) (k := kq) (by decide)
  have hprod := fs161_f5_tight3_17_lt_two
  have : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) <
      (161 : ℚ) / 100 * fSum 5 *
        (1 + 1 / ((17 : ℚ) + 1) + 1 / (1 + 17 + 17 ^ 2) +
          1 / ((17 : ℚ) ^ 2 * (17 - 1))) := by
    rw [pow_one]
    have h1 : fSum (2 ^ a) * fSum 5 < (161 : ℚ) / 100 * fSum 5 :=
      mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
    exact mul_lt_mul h1 (le_of_lt hσ)
      (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0)))
      (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
  exact this.trans hprod

lemma ge21_five_two_seventeen_gt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum (17 ^ kq) := by
  have h17 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 17) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) (by decide) hqkp
    le_rfl h17
    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0)))
    (fSum_pos (by decide)) eight_five_f5sq_f17_gt_two

lemma ge21_five_le2_ge29_mid_lt_two {a kp q kq : ℕ} (ha : 21 ≤ a)
    (hq : q.Prime) (hq29 : 29 ≤ q) (hpkp : kp = 1 ∨ kp = 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have h5b : fSum (5 ^ kp) ≤ fSum (5 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide) hpkp
  have hσ := fSum_prime_pow_lt_tight3 (p := q) (k := kq) hq
  have hqB : fSum (q ^ kq) <
      (1 : ℚ) + 1 / ((29 : ℚ) + 1) + 1 / (1 + 29 + 29 ^ 2) +
        1 / ((29 : ℚ) ^ 2 * (29 - 1)) := by
    have h1 := hσ
    have hqQ : (29 : ℚ) ≤ q := by exact_mod_cast hq29
    have hr1 : (1 : ℚ) < 29 := by norm_num
    have hA : (1 : ℚ) / ((q : ℚ) + 1) ≤ 1 / ((29 : ℚ) + 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hB : (1 : ℚ) / (1 + (q : ℚ) + q ^ 2) ≤
        1 / (1 + (29 : ℚ) + 29 ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hC : (1 : ℚ) / ((q : ℚ) ^ 2 * (q - 1)) ≤
        1 / ((29 : ℚ) ^ 2 * (29 - 1)) := by
      refine one_div_le_one_div_of_le ?_ ?_
      · positivity
      · nlinarith [Nat.cast_nonneg (α := ℚ) q]
    linarith
  have hprod := fs161_f5sq_tight3_29_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) < (161 : ℚ) / 100 * fSum (5 ^ 2) :=
    mul_lt_mul h2b h5b (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0)))
      (by positivity)
  have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
      (161 : ℚ) / 100 * fSum (5 ^ 2) *
        (1 + 1 / ((29 : ℚ) + 1) + 1 / (1 + 29 + 29 ^ 2) +
          1 / ((29 : ℚ) ^ 2 * (29 - 1))) :=
    mul_lt_mul h1 (le_of_lt hqB)
      (fSum_pos (pow_ne_zero kq hq.ne_zero))
      (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  exact this.trans hprod

lemma ge21_five_cu_thirteen_gt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (13 ^ kq) := by
  have h13 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 13) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) (by decide : 1 ≤ 3) hqkp
    le_rfl h13
    (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0)))
    (fSum_pos (by decide)) eight_five_f5cu_f13_gt_two

lemma ge21_five_cu_seventeen_gt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (17 ^ kq) := by
  have h17 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 17) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) (by decide : 1 ≤ 3) hqkp
    le_rfl h17
    (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0)))
    (fSum_pos (by decide)) eight_five_f5cu_f17_gt_two

lemma ge21_five_ge3_twentynine_gt_two {a kp kq : ℕ} (ha : 21 ≤ a)
    (hpkp : 3 ≤ kp) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (29 ^ kq) := by
  have hlo := fSum_two_pow_ge21_gt_803_500 ha
  have h5 := fSum_le_of_exp_ge (by decide : Nat.Prime 5) hpkp
  have h29 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 29) hqkp
  have hmin : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum 29 := by
    have hgt0 := eight03_f5cu_f29_gt_two
    have : (803 : ℚ) / 500 * fSum (5 ^ 3) * fSum 29 <
        fSum (2 ^ a) * fSum (5 ^ 3) * fSum 29 :=
      mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right hlo
          (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))))
        (fSum_pos (by decide))
    exact hgt0.trans this
  have hmono := mul3_gt_of le_rfl h5 h29
    (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
    (fSum_pos (pow_ne_zero a two_ne_zero)).le
    (fSum_pos (by decide : (29 : ℕ) ≠ 0)).le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
  exact lt_of_lt_of_le hmin hmono

lemma ge21_five_ge3_ge37_lt_two {a kp q kq : ℕ} (ha : 21 ≤ a)
    (hq : q.Prime) (hq37 : 37 ≤ q) (hpkp : 1 ≤ kp) (hkq2 : kq ≤ 2)
    (hkq : 1 ≤ kq) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have h5b := fSum_prime_pow_lt_tight3 (p := 5) (k := kp) Nat.prime_five
  have hC : fSum (q ^ kq) ≤ fSum (q ^ 2) :=
    fSum_le_sq_of_exp_le_two hq (by omega)
  have hqs : fSum (q ^ 2) ≤ fSum (37 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 37) hq hq37
  have hC' : fSum (q ^ kq) ≤ fSum (37 ^ 2) := le_trans hC hqs
  have hprod := fs161_tight3_5_f37sq_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) <
      (161 : ℚ) / 100 *
        ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
          1 / ((5 : ℚ) ^ 2 * (5 - 1))) :=
    mul_lt_mul h2b (le_of_lt h5b)
      (fSum_pos (pow_ne_zero kp (show (5 : ℕ) ≠ 0 by decide))) (by positivity)
  have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
      (161 : ℚ) / 100 *
        ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
          1 / ((5 : ℚ) ^ 2 * (5 - 1))) * fSum (37 ^ 2) :=
    mul_lt_mul h1 hC'
      (fSum_pos (pow_ne_zero kq hq.ne_zero)) (by positivity)
  exact lt_of_lt_of_le this (le_of_lt hprod)

lemma ge21_five_one_nineteen_lt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq)
    (hkq2 : kq ≤ 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have hC : fSum (19 ^ kq) ≤ fSum (19 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 19) (by omega)
  have hprod := fs161_f5_f19sq_lt_two
  have : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) <
      (161 : ℚ) / 100 * fSum 5 * fSum (19 ^ 2) := by
    rw [pow_one]
    exact mul3_lt_of h2b le_rfl hC
      (fSum_pos (by decide)) (by positivity)
      (fSum_pos (pow_ne_zero kq (by decide : (19 : ℕ) ≠ 0)))
      (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
  exact this.trans hprod

lemma ge21_five_two_nineteen_gt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum (19 ^ kq) := by
  have h19 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 19) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) (by decide) hqkp
    le_rfl h19
    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0)))
    (fSum_pos (by decide)) eight_five_f5sq_f19_gt_two

lemma ge21_five_le2_ge43_lt_two {a kp q kq : ℕ} (ha : 21 ≤ a)
    (hq : q.Prime) (hq43 : 43 ≤ q) (hpkp : kp = 1 ∨ kp = 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have h5b : fSum (5 ^ kp) ≤ fSum (5 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide) hpkp
  have hσ := fSum_prime_pow_lt_tight_of_ge (r := 43) (q := q) (k := kq)
    hq (by decide) hq43
  have hprod := fs161_f5sq_tight43_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) < (161 : ℚ) / 100 * fSum (5 ^ 2) :=
    mul_lt_mul h2b h5b (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0)))
      (by positivity)
  have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
      (161 : ℚ) / 100 * fSum (5 ^ 2) *
        (1 + 1 / ((43 : ℚ) + 1) + 1 / (43 * (43 - 1))) :=
    mul_lt_mul h1 (le_of_lt hσ)
      (fSum_pos (pow_ne_zero kq hq.ne_zero))
      (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  exact this.trans hprod

lemma ge21_no_five_neg_three_lt_two {a p kp q kq : ℕ} (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime)
    (hp7 : 7 ≤ p) (hq13 : 13 ≤ q) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  -- Use 13 and 17-tight3 if both 1-mod-4, or 13 and 11 if mixed.
  -- Uniform: 161/100 * tight(13) * tight(11) < 2 covers q≥13 and a second ≥11,
  -- but here p≥7. tight(7)*tight(13) = ?
  -- Safer split is done by the caller. This lemma assumes hq13 so the
  -- larger prime is ≥13; for the smaller we use tight(7).
  -- 161/100 * tight7 * tight13:
  have hpB : fSum (p ^ kp) <
      (1 : ℚ) + 1 / (7 + 1) + 1 / (7 * (7 - 1)) :=
    fSum_prime_pow_lt_tight_of_ge (r := 7) (q := p) (k := kp)
      hp (by decide) hp7
  have hqB : fSum (q ^ kq) <
      (1 : ℚ) + 1 / (13 + 1) + 1 / (13 * (13 - 1)) :=
    fSum_prime_pow_lt_tight_of_ge (r := 13) (q := q) (k := kq)
      hq (by decide) hq13
  have hprod : (161 : ℚ) / 100 *
      (1 + 1 / ((7 : ℚ) + 1) + 1 / ((7 : ℚ) * (7 - 1))) *
      (1 + 1 / ((13 : ℚ) + 1) + 1 / ((13 : ℚ) * (13 - 1))) < 2 := by
    norm_num
  have hmul1 : fSum (2 ^ a) * fSum (p ^ kp) <
      (161 : ℚ) / 100 *
        (1 + 1 / ((7 : ℚ) + 1) + 1 / ((7 : ℚ) * (7 - 1))) :=
    mul_lt_mul h2b hpB.le
      (fSum_pos (pow_ne_zero kp hp.ne_zero)) (by positivity)
  have hmul2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) <
      (161 : ℚ) / 100 *
        (1 + 1 / ((7 : ℚ) + 1) + 1 / ((7 : ℚ) * (7 - 1))) *
        (1 + 1 / ((13 : ℚ) + 1) + 1 / ((13 : ℚ) * (13 - 1))) :=
    mul_lt_mul hmul1 hqB.le
      (fSum_pos (pow_ne_zero kq hq.ne_zero)) (by positivity)
  exact hmul2.trans hprod


lemma fSum_two_pow_five_two_odd_ne_two
    {p kp q kq : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (_hbig : 3 ≤ kp ∨ 3 ≤ kq ∨ p ≡ 3 [MOD 4] ∨ q ≡ 3 [MOD 4]) :
    fSum (2 ^ 5) * (fSum (p ^ kp) * fSum (q ^ kq)) ≠ 2 := by
  have hassoc : fSum (2 ^ 5) * (fSum (p ^ kp) * fSum (q ^ kq)) =
      fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
  rw [hassoc]
  have hp3or := odd_prime_eq_three_or_ge_five hp hpo
  have hq3or := odd_prime_eq_three_or_ge_five hq hqo
  rcases hp3or with hp3 | hp5
  · subst hp3
    exact fSum_two_five_three_odd_ne_two hq hqo hpkp hqkp (by intro h; exact hpq h.symm)
  · rcases hq3or with hq3 | hq5
    · subst hq3
      have hswap : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (3 ^ kq) =
          fSum (2 ^ 5) * fSum (3 ^ kq) * fSum (p ^ kp) := by ring
      rw [hswap]
      exact fSum_two_five_three_odd_ne_two hp hpo hqkp hpkp hpq
    · exact fSum_two_pow_five_both_ge5_ne_two hp hq hpq hp5 hq5 hpkp hqkp


lemma not_one_mod4_of_eq_seven : ¬ (7 : ℕ) ≡ 1 [MOD 4] := by decide
lemma not_one_mod4_of_eq_eleven : ¬ (11 : ℕ) ≡ 1 [MOD 4] := by decide
lemma not_one_mod4_of_eq_nineteen : ¬ (19 : ℕ) ≡ 1 [MOD 4] := by decide
lemma not_one_mod4_of_eq_twentythree : ¬ (23 : ℕ) ≡ 1 [MOD 4] := by decide
lemma not_one_mod8_one_of_eq_seven : ¬ (7 : ℕ) ≡ 1 [MOD 8] := by decide
lemma not_one_mod8_one_of_eq_eleven : ¬ (11 : ℕ) ≡ 1 [MOD 8] := by decide
lemma not_three_mod8_of_eq_seventeen : ¬ (17 : ℕ) ≡ 3 [MOD 8] := by decide
lemma not_three_mod8_of_eq_thirteen : ¬ (13 : ℕ) ≡ 3 [MOD 8] := by decide
lemma not_three_mod8_of_eq_twentythree : ¬ (23 : ℕ) ≡ 3 [MOD 8] := by decide
lemma not_three_mod8_of_eq_twentynine : ¬ (29 : ℕ) ≡ 3 [MOD 8] := by decide
lemma not_three_mod8_of_eq_thirtyone : ¬ (31 : ℕ) ≡ 3 [MOD 8] := by decide
lemma not_three_mod8_of_eq_thirtyseven : ¬ (37 : ℕ) ≡ 3 [MOD 8] := by decide
lemma not_three_mod8_of_eq_fortyone : ¬ (41 : ℕ) ≡ 3 [MOD 8] := by decide

lemma prime_eq_seventeen_or_ge_twentynine_of_one_mod4
    {q : ℕ} (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (h17 : 17 ≤ q) :
    q = 17 ∨ 29 ≤ q := by
  by_cases h29 : 29 ≤ q
  · exact Or.inr h29
  · have hlt : q < 29 := by omega
    interval_cases q
    · exact Or.inl rfl -- 17
    · exact absurd hq (by decide)
    · exact (not_one_mod4_of_eq_nineteen (by simpa [Nat.ModEq] using h1)).elim
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · exact (not_one_mod4_of_eq_twentythree (by simpa [Nat.ModEq] using h1)).elim
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)

lemma prime_eq_twentynine_or_ge_thirtyseven_of_one_mod4
    {q : ℕ} (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (h29 : 29 ≤ q) :
    q = 29 ∨ 37 ≤ q := by
  by_cases h37 : 37 ≤ q
  · exact Or.inr h37
  · have hlt : q < 37 := by omega
    have : q ≠ 31 := by
      intro h; subst h
      have : ¬ (31 : ℕ) ≡ 1 [MOD 4] := by decide
      exact this h1
    have n30 : ¬ Nat.Prime 30 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 15 = 30) (by decide) (by decide)
    have n32 : ¬ Nat.Prime 32 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 16 = 32) (by decide) (by decide)
    have n33 : ¬ Nat.Prime 33 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 11 = 33) (by decide) (by decide)
    have n34 : ¬ Nat.Prime 34 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 17 = 34) (by decide) (by decide)
    have n35 : ¬ Nat.Prime 35 :=
      Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 7 = 35) (by decide) (by decide)
    have n36 : ¬ Nat.Prime 36 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 18 = 36) (by decide) (by decide)
    have hq30 : q ≠ 30 := fun h => n30 (h ▸ hq)
    have hq32 : q ≠ 32 := fun h => n32 (h ▸ hq)
    have hq33 : q ≠ 33 := fun h => n33 (h ▸ hq)
    have hq34 : q ≠ 34 := fun h => n34 (h ▸ hq)
    have hq35 : q ≠ 35 := fun h => n35 (h ▸ hq)
    have hq36 : q ≠ 36 := fun h => n36 (h ▸ hq)
    omega

lemma prime_eq_nineteen_or_ge_fortythree_of_mod8_three
    {q : ℕ} (hq : q.Prime) (h3 : q ≡ 3 [MOD 8]) (h19 : 19 ≤ q) :
    q = 19 ∨ 43 ≤ q := by
  by_cases h43 : 43 ≤ q
  · exact Or.inr h43
  · have hlt : q < 43 := by omega
    have n20 : ¬ Nat.Prime 20 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 10 = 20) (by decide) (by decide)
    have n21 : ¬ Nat.Prime 21 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 7 = 21) (by decide) (by decide)
    have n22 : ¬ Nat.Prime 22 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 11 = 22) (by decide) (by decide)
    have n24 : ¬ Nat.Prime 24 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 12 = 24) (by decide) (by decide)
    have n25 : ¬ Nat.Prime 25 :=
      Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 5 = 25) (by decide) (by decide)
    have n26 : ¬ Nat.Prime 26 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 13 = 26) (by decide) (by decide)
    have n27 : ¬ Nat.Prime 27 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 9 = 27) (by decide) (by decide)
    have n28 : ¬ Nat.Prime 28 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 14 = 28) (by decide) (by decide)
    have n30 : ¬ Nat.Prime 30 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 15 = 30) (by decide) (by decide)
    have n32 : ¬ Nat.Prime 32 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 16 = 32) (by decide) (by decide)
    have n33 : ¬ Nat.Prime 33 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 11 = 33) (by decide) (by decide)
    have n34 : ¬ Nat.Prime 34 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 17 = 34) (by decide) (by decide)
    have n35 : ¬ Nat.Prime 35 :=
      Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 7 = 35) (by decide) (by decide)
    have n36 : ¬ Nat.Prime 36 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 18 = 36) (by decide) (by decide)
    have n38 : ¬ Nat.Prime 38 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 19 = 38) (by decide) (by decide)
    have n39 : ¬ Nat.Prime 39 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 13 = 39) (by decide) (by decide)
    have n40 : ¬ Nat.Prime 40 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 20 = 40) (by decide) (by decide)
    have n42 : ¬ Nat.Prime 42 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 21 = 42) (by decide) (by decide)
    have n23 : q ≠ 23 := fun h => not_three_mod8_of_eq_twentythree (h ▸ h3)
    have n29 : q ≠ 29 := fun h => not_three_mod8_of_eq_twentynine (h ▸ h3)
    have n31 : q ≠ 31 := fun h => not_three_mod8_of_eq_thirtyone (h ▸ h3)
    have n37 : q ≠ 37 := fun h => not_three_mod8_of_eq_thirtyseven (h ▸ h3)
    have n41 : q ≠ 41 := fun h => not_three_mod8_of_eq_fortyone (h ▸ h3)
    have : q = 19 := by
      have hqne : q ≠ 20 ∧ q ≠ 21 ∧ q ≠ 22 ∧ q ≠ 24 ∧ q ≠ 25 ∧ q ≠ 26 ∧
          q ≠ 27 ∧ q ≠ 28 ∧ q ≠ 30 ∧ q ≠ 32 ∧ q ≠ 33 ∧ q ≠ 34 ∧ q ≠ 35 ∧
          q ≠ 36 ∧ q ≠ 38 ∧ q ≠ 39 ∧ q ≠ 40 ∧ q ≠ 42 :=
        ⟨fun h => n20 (h ▸ hq), fun h => n21 (h ▸ hq), fun h => n22 (h ▸ hq),
          fun h => n24 (h ▸ hq), fun h => n25 (h ▸ hq), fun h => n26 (h ▸ hq),
          fun h => n27 (h ▸ hq), fun h => n28 (h ▸ hq), fun h => n30 (h ▸ hq),
          fun h => n32 (h ▸ hq), fun h => n33 (h ▸ hq), fun h => n34 (h ▸ hq),
          fun h => n35 (h ▸ hq), fun h => n36 (h ▸ hq), fun h => n38 (h ▸ hq),
          fun h => n39 (h ▸ hq), fun h => n40 (h ▸ hq), fun h => n42 (h ▸ hq)⟩
      omega
    exact Or.inl this

/-- `a ≥ 21`, both odd primes `≥ 5`, `v₂ = -3`. -/
lemma fSum_ge21_family_neg_three_ne_two
    {a p kp q kq : ℕ} (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (hv : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -3) :
    fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) ≠ 2 := by
  haveI := two_fact
  wlog hle : p ≤ q generalizing p q kp kq
  · have hswap : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
        fSum (2 ^ a) * (fSum (q ^ kq) * fSum (p ^ kp)) := by ring
    rw [hswap]
    have hv' : padicValRat 2 (fSum (q ^ kq) * fSum (p ^ kp)) = -3 := by
      rw [mul_comm]; exact hv
    exact this hq hp hpq.symm hqo hpo hq5 hp5 hqkp hpkp hv'
      (le_of_lt (lt_of_not_ge hle))
  have hassoc : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
      fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
  rw [hassoc]
  have hvp := padicValRat_two_fSum_odd_prime_pow hp hpo hpkp
  have hvq := padicValRat_two_fSum_odd_prime_pow hq hqo hqkp
  have hvsum : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) = -3 := by
    rwa [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
      (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))] at hv
  cases eq_or_ne p 5 with
  | inl hp5eq =>
    subst hp5eq
    have hq7 : 7 ≤ q := by
      have : q ≠ 5 := hpq.symm
      have : q ≠ 6 := fun h => not_prime_six (h ▸ hq)
      omega
    have hv5 : padicValRat 2 (fSum (5 ^ kp)) = - (Nat.log 2 (kp + 1) : ℤ) := by
      rw [hvp]
      have : padicValNat 2 (5 + 1) = 1 :=
        padicValNat_two_add_one_of_mod4_one (by decide : Odd 5)
          (by decide : (5 : ℕ) ≡ 1 [MOD 4])
      omega
    have hvq' : padicValRat 2 (fSum (q ^ kq)) = -3 + Nat.log 2 (kp + 1) := by
      linarith
    by_cases hkple2 : kp ≤ 2
    · have hlog1 : Nat.log 2 (kp + 1) = 1 :=
        log_two_eq_one_of_mem_two_three (by omega) (by omega)
      have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -2 := by
        rw [hvq']; omega
      have hkp12 : kp = 1 ∨ kp = 2 := by omega
      rcases odd_mod8 hqo with hq1 | hq3 | hq5m | hq7m
      · -- q ≡ 1 [MOD 8] ⊆ ≡ 1 [MOD 4], exp 3–6
        have hq14 : q ≡ 1 [MOD 4] := p_mod4_one_of_mod8_one hq1
        have hlogq : Nat.log 2 (kq + 1) = 2 := by
          have hv2q : padicValNat 2 (q + 1) = 1 :=
            padicValNat_two_add_one_of_mod4_one hqo hq14
          rw [hvq] at hvqeq; omega
        have ⟨hkq3, hkq6⟩ := exp_mid_of_log_eq_two hqkp hlogq
        have hq13 : 13 ≤ q := by
          have hne7 : q ≠ 7 := fun h => not_one_mod8_one_of_eq_seven (h ▸ hq1)
          have hne11 : q ≠ 11 := fun h => not_one_mod8_one_of_eq_eleven (h ▸ hq1)
          exact prime_ge_thirteen_of_ge_eleven_ne hq
            (prime_ge_eleven_of_ge_seven_ne hq hq7 hne7) hne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases prime_eq_seventeen_or_ge_twentynine_of_one_mod4 hq hq14 hq17 with
          | inl hq17eq =>
            subst hq17eq
            cases hkp12 with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_seventeen_mid_lt_two ha)
            | inr hk2 =>
              subst hk2
              exact ne_of_gt (ge21_five_two_seventeen_gt_two ha hqkp)
          | inr hq29 =>
            exact ne_of_lt (ge21_five_le2_ge29_mid_lt_two ha hq hq29 hkp12)
      · -- q ≡ 3 [MOD 8], exp 1–2
        have hlogq : Nat.log 2 (kq + 1) = 1 := by
          have hv2q : padicValNat 2 (q + 1) = 2 :=
            padicValNat_two_add_one_of_mod8_three hqo hq3
          rw [hvq] at hvqeq; omega
        have hkq2 : kq ≤ 2 := exp_le_two_of_log_eq_one hqkp hlogq
        have hq11 : 11 ≤ q :=
          prime_ge_eleven_of_ge_seven_ne hq hq7 (fun h => by
            subst h
            have : ¬ (7 : ℕ) ≡ 3 [MOD 8] := by decide
            exact this hq3)
        cases eq_or_ne q 11 with
        | inl hq11eq =>
          subst hq11eq
          exact ne_of_gt (ge21_five_eleven_gt_two ha hpkp hqkp)
        | inr hqne11 =>
          have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hqne11
          have hqne13 : q ≠ 13 := fun h => not_three_mod8_of_eq_thirteen (h ▸ hq3)
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          have hqne17 : q ≠ 17 := fun h => not_three_mod8_of_eq_seventeen (h ▸ hq3)
          have hq19 : 19 ≤ q := by
            have : q ≠ 18 := fun h => not_prime_eighteen (h ▸ hq)
            omega
          cases prime_eq_nineteen_or_ge_fortythree_of_mod8_three hq hq3 hq19 with
          | inl hq19eq =>
            subst hq19eq
            cases hkp12 with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_nineteen_lt_two ha hqkp hkq2)
            | inr hk2 =>
              subst hk2
              exact ne_of_gt (ge21_five_two_nineteen_gt_two ha hqkp)
          | inr hq43 =>
            exact ne_of_lt (ge21_five_le2_ge43_lt_two ha hq hq43 hkp12)
      · -- q ≡ 5 [MOD 8] ⊆ ≡ 1 [MOD 4], same as ≡ 1 [MOD 8]
        have hq14 : q ≡ 1 [MOD 4] := p_mod4_one_of_mod8_five hq5m
        have hlogq : Nat.log 2 (kq + 1) = 2 := by
          have hv2q : padicValNat 2 (q + 1) = 1 :=
            padicValNat_two_add_one_of_mod4_one hqo hq14
          rw [hvq] at hvqeq; omega
        have ⟨hkq3, hkq6⟩ := exp_mid_of_log_eq_two hqkp hlogq
        have hq13 : 13 ≤ q := by
          have hne7 : q ≠ 7 := by
            intro h; subst h; have : ¬ (7 : ℕ) ≡ 5 [MOD 8] := by decide
            exact this hq5m
          have hne11 : q ≠ 11 := by
            intro h; subst h; have : ¬ (11 : ℕ) ≡ 5 [MOD 8] := by decide
            exact this hq5m
          exact prime_ge_thirteen_of_ge_eleven_ne hq
            (prime_ge_eleven_of_ge_seven_ne hq hq7 hne7) hne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases prime_eq_seventeen_or_ge_twentynine_of_one_mod4 hq hq14 hq17 with
          | inl hq17eq =>
            subst hq17eq
            cases hkp12 with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_seventeen_mid_lt_two ha)
            | inr hk2 =>
              subst hk2
              exact ne_of_gt (ge21_five_two_seventeen_gt_two ha hqkp)
          | inr hq29 =>
            exact ne_of_lt (ge21_five_le2_ge29_mid_lt_two ha hq hq29 hkp12)
      · -- q ≡ 7 [MOD 8]: v₂ ≤ -3, cannot be -2
        have : padicValRat 2 (fSum (q ^ kq)) ≤ -3 :=
          v2_fSum_odd_prime_pow_mod8_seven_small hq hqo hq7m hqkp
        linarith
    · -- kp ≥ 3, so log ≥ 2, v₂(5^kp) ≤ -2, hence v₂(q) = -1 (since sum = -3)
      have hkp3 : 3 ≤ kp := by omega
      have hlog : 2 ≤ Nat.log 2 (kp + 1) := log_two_of_ge_four (by omega)
      have hlogkp : Nat.log 2 (kp + 1) = 2 := by
        have hvqZ : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
          Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqkp)
        -- v₂(5) = -log, v₂(q) = -3 + log, and v₂(q) ≤ -1 so log ≤ 2
        have : (Nat.log 2 (kp + 1) : ℤ) ≤ 2 := by linarith
        omega
      have ⟨_, hkp6⟩ := exp_mid_of_log_eq_two hpkp hlogkp
      have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by
        rw [hvq']; omega
      have hq14 : q ≡ 1 [MOD 4] :=
        mod4_one_of_v2_eq_neg_one hq hqo hqkp hvqeq
      have hkq2 : kq ≤ 2 :=
        exp_le_two_of_v2_eq_neg_one hq hqo hqkp hvqeq
      have hq13or := prime_one_mod_four_cases hq hq14
      rcases hq13or with hq5eq | hq13eq | hq17eq | hq29
      · exact (hpq.symm hq5eq).elim
      · subst hq13eq
        have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
          fSum_le_of_exp_ge (by decide : Nat.Prime 5) hkp3
        have : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (13 ^ kq) :=
          ge21_five_cu_thirteen_gt_two ha hqkp
        have hmono := mul3_gt_of le_rfl h53 le_rfl
          (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kq (by decide : (13 : ℕ) ≠ 0))).le
          (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
            (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
        exact ne_of_gt (lt_of_lt_of_le this hmono)
      · subst hq17eq
        have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
          fSum_le_of_exp_ge (by decide : Nat.Prime 5) hkp3
        have : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (17 ^ kq) :=
          ge21_five_cu_seventeen_gt_two ha hqkp
        have hmono := mul3_gt_of le_rfl h53 le_rfl
          (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))).le
          (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
            (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
        exact ne_of_gt (lt_of_lt_of_le this hmono)
      · cases prime_eq_twentynine_or_ge_thirtyseven_of_one_mod4 hq hq14 hq29 with
        | inl hq29eq =>
          subst hq29eq
          exact ne_of_gt (ge21_five_ge3_twentynine_gt_two ha hkp3 hqkp)
        | inr hq37 =>
          exact ne_of_lt (ge21_five_ge3_ge37_lt_two ha hq hq37 hpkp hkq2 hqkp)
  | inr hpne5 =>
    have hp7 : 7 ≤ p := by
      have : p ≠ 6 := fun h => not_prime_six (h ▸ hp)
      omega
    have hq13 : 13 ≤ q := by
      have hq7 : 7 ≤ q := le_trans hp7 hle
      have hne7 : q ≠ 7 := fun h => hpq (le_antisymm hle (h ▸ hp7))
      have hq11 : 11 ≤ q := prime_ge_eleven_of_ge_seven_ne hq hq7 hne7
      have hne11 : q ≠ 11 := by
        intro h; subst h
        have hp7eq : p = 7 := by
          have : p ≠ 8 := fun h => not_prime_eight (h ▸ hp)
          have : p ≠ 9 := fun h => not_prime_nine (h ▸ hp)
          have : p ≠ 10 := fun h => not_prime_ten (h ▸ hp)
          have : p ≠ 11 := hpq
          omega
        subst hp7eq
        have hv7 : padicValRat 2 (fSum (7 ^ kp)) ≤ -2 :=
          v2_fSum_odd_prime_pow_mod4_three hp hpo (by decide) hpkp
        have hv11 : padicValRat 2 (fSum (11 ^ kq)) ≤ -2 :=
          v2_fSum_odd_prime_pow_mod4_three hq hqo (by decide) hqkp
        linarith
      exact prime_ge_thirteen_of_ge_eleven_ne hq hq11 hne11
    exact ne_of_lt (ge21_no_five_neg_three_lt_two ha hp hq hp7 hq13)

lemma exp_high_of_log_eq_three {k : ℕ} (hk : 1 ≤ k)
    (hlog : Nat.log 2 (k + 1) = 3) : 7 ≤ k ∧ k ≤ 14 := by
  have hle : 2 ^ Nat.log 2 (k + 1) ≤ k + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hlt : k + 1 < 2 ^ (Nat.log 2 (k + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (k + 1)
  rw [hlog] at hle hlt
  omega

lemma log_of_v2_mod4_one {p k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (h1 : p ≡ 1 [MOD 4]) (hk : 1 ≤ k) :
    padicValRat 2 (fSum (p ^ k)) = - (Nat.log 2 (k + 1) : ℤ) := by
  haveI := two_fact
  rw [v2_fSum_eq_one_sub hp hpo hk]
  have : padicValNat 2 (p + 1) = 1 :=
    padicValNat_two_add_one_of_mod4_one hpo h1
  omega

lemma log_of_v2_mod8_three {p k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (h3 : p ≡ 3 [MOD 8]) (hk : 1 ≤ k) :
    padicValRat 2 (fSum (p ^ k)) = -1 - (Nat.log 2 (k + 1) : ℤ) := by
  haveI := two_fact
  rw [v2_fSum_eq_one_sub hp hpo hk]
  have : padicValNat 2 (p + 1) = 2 :=
    padicValNat_two_add_one_of_mod8_three hpo h3
  omega

lemma fSum_prime_pow_lt_tight3_of_ge {r q k : ℕ}
    (hq : q.Prime) (hr2 : 2 ≤ r) (hrq : r ≤ q) :
    fSum (q ^ k) <
      (1 : ℚ) + 1 / ((r : ℚ) + 1) + 1 / (1 + r + r ^ 2) +
        1 / ((r : ℚ) ^ 2 * (r - 1)) := by
  have h1 := fSum_prime_pow_lt_tight3 (p := q) (k := k) hq
  have hqQ : (r : ℚ) ≤ q := by exact_mod_cast hrq
  have hr1 : (1 : ℚ) < r :=
    by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hr2)
  have hA : (1 : ℚ) / ((q : ℚ) + 1) ≤ 1 / ((r : ℚ) + 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hB : (1 : ℚ) / (1 + (q : ℚ) + q ^ 2) ≤
      1 / (1 + (r : ℚ) + r ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hC : (1 : ℚ) / ((q : ℚ) ^ 2 * (q - 1)) ≤
      1 / ((r : ℚ) ^ 2 * (r - 1)) := by
    refine one_div_le_one_div_of_le ?_ ?_
    · exact mul_pos (pow_pos (zero_lt_one.trans hr1) 2) (sub_pos.mpr hr1)
    · have hsq : (r : ℚ) ^ 2 ≤ (q : ℚ) ^ 2 := by
        nlinarith [sq_nonneg ((r : ℚ) - q)]
      have hsub : (r : ℚ) - 1 ≤ (q : ℚ) - 1 := by linarith
      exact mul_le_mul hsq hsub (by linarith) (sq_nonneg _)
  linarith

lemma eight_five_f5_f7_gt_two :
    2 < (8 : ℚ) / 5 * fSum 5 * fSum 7 := by
  rw [fSum_five, fSum_seven]; norm_num

lemma eight_five_f5cu_f19_gt_two :
    2 < (8 : ℚ) / 5 * fSum (5 ^ 3) * fSum 19 := by
  rw [fSum_five_cu, fSum_nineteen]; norm_num

lemma eight03_f5sq_f23_gt_two :
    2 < (803 : ℚ) / 500 * fSum (5 ^ 2) * fSum 23 := by
  rw [fSum_five_sq, fSum_twentythree]; norm_num

lemma fs161_f5_tight3_19_lt_two :
    (161 : ℚ) / 100 * fSum 5 *
      (1 + 1 / ((19 : ℚ) + 1) + 1 / (1 + 19 + 19 ^ 2) +
        1 / ((19 : ℚ) ^ 2 * (19 - 1))) < 2 := by
  rw [fSum_five]; norm_num

lemma fs161_f5_f23sq_lt_two :
    (161 : ℚ) / 100 * fSum 5 * fSum (23 ^ 2) < 2 := by
  rw [fSum_five, fSum_twentythree_sq]; norm_num

lemma fs161_f5sq_tight31_lt_two :
    (161 : ℚ) / 100 * fSum (5 ^ 2) *
      (1 + 1 / ((31 : ℚ) + 1) + 1 / (31 * (31 - 1))) < 2 := by
  rw [fSum_five_sq]; norm_num

lemma fs161_tight3_5_tight3_37_lt_two :
    (161 : ℚ) / 100 *
      ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
        1 / ((5 : ℚ) ^ 2 * (5 - 1))) *
      ((1 : ℚ) + 1 / (37 + 1) + 1 / (1 + 37 + 37 ^ 2) +
        1 / ((37 : ℚ) ^ 2 * (37 - 1))) < 2 := by
  norm_num

lemma fs161_tight3_5_f43sq_lt_two :
    (161 : ℚ) / 100 *
      ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
        1 / ((5 : ℚ) ^ 2 * (5 - 1))) * fSum (43 ^ 2) < 2 := by
  rw [fSum_prime_sq (by decide : Nat.Prime 43)]; norm_num

lemma ge21_five_seven_gt_two {a kp kq : ℕ} (ha : 21 ≤ a)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (7 ^ kq) := by
  have h5 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 5) hpkp
  have h7 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 7) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) hpkp hqkp h5 h7
    (fSum_pos (by decide)) (fSum_pos (by decide)) eight_five_f5_f7_gt_two

lemma ge21_five_cu_nineteen_gt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (19 ^ kq) := by
  have h19 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 19) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) (by decide : 1 ≤ 3) hqkp
    le_rfl h19
    (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0)))
    (fSum_pos (by decide)) eight_five_f5cu_f19_gt_two

lemma ge21_five_one_nineteen_any_lt_two {a kq : ℕ} (ha : 21 ≤ a) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have hσ := fSum_prime_pow_lt_tight3 (p := 19) (k := kq) (by decide)
  have hprod := fs161_f5_tight3_19_lt_two
  have : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) <
      (161 : ℚ) / 100 * fSum 5 *
        (1 + 1 / ((19 : ℚ) + 1) + 1 / (1 + 19 + 19 ^ 2) +
          1 / ((19 : ℚ) ^ 2 * (19 - 1))) := by
    rw [pow_one]
    have h1 : fSum (2 ^ a) * fSum 5 < (161 : ℚ) / 100 * fSum 5 :=
      mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
    exact mul_lt_mul h1 (le_of_lt hσ)
      (fSum_pos (pow_ne_zero kq (by decide : (19 : ℕ) ≠ 0)))
      (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
  exact this.trans hprod

lemma ge21_five_one_twentythree_lt_two {a kq : ℕ} (ha : 21 ≤ a)
    (hqkp : 1 ≤ kq) (hkq2 : kq ≤ 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (23 ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have hC : fSum (23 ^ kq) ≤ fSum (23 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 23) (by omega)
  have hprod := fs161_f5_f23sq_lt_two
  have : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (23 ^ kq) <
      (161 : ℚ) / 100 * fSum 5 * fSum (23 ^ 2) := by
    rw [pow_one]
    exact mul3_lt_of h2b le_rfl hC
      (fSum_pos (by decide)) (by positivity)
      (fSum_pos (pow_ne_zero kq (by decide : (23 : ℕ) ≠ 0)))
      (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
  exact this.trans hprod

lemma ge21_five_two_twentythree_gt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum (23 ^ kq) := by
  have hlo := fSum_two_pow_ge21_gt_803_500 ha
  have h23 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 23) hqkp
  have hmin : 2 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum 23 := by
    have hgt0 := eight03_f5sq_f23_gt_two
    have : (803 : ℚ) / 500 * fSum (5 ^ 2) * fSum 23 <
        fSum (2 ^ a) * fSum (5 ^ 2) * fSum 23 :=
      mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right hlo
          (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))))
        (fSum_pos (by decide))
    exact hgt0.trans this
  have hmono := mul3_gt_of le_rfl le_rfl h23
    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le
    (fSum_pos (pow_ne_zero a two_ne_zero)).le
    (fSum_pos (by decide : (23 : ℕ) ≠ 0)).le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  exact lt_of_lt_of_le hmin hmono

lemma ge21_five_le2_ge31_lt_two {a kp q kq : ℕ} (ha : 21 ≤ a)
    (hq : q.Prime) (hq31 : 31 ≤ q) (hpkp : kp = 1 ∨ kp = 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have h5b : fSum (5 ^ kp) ≤ fSum (5 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide) hpkp
  have hσ := fSum_prime_pow_lt_tight_of_ge (r := 31) (q := q) (k := kq)
    hq (by decide) hq31
  have hprod := fs161_f5sq_tight31_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) < (161 : ℚ) / 100 * fSum (5 ^ 2) :=
    mul_lt_mul h2b h5b (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0)))
      (by positivity)
  have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
      (161 : ℚ) / 100 * fSum (5 ^ 2) *
        (1 + 1 / ((31 : ℚ) + 1) + 1 / (31 * (31 - 1))) :=
    mul_lt_mul h1 (le_of_lt hσ)
      (fSum_pos (pow_ne_zero kq hq.ne_zero))
      (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  exact this.trans hprod

lemma ge21_five_mid_ge37_any_lt_two {a kp q kq : ℕ} (ha : 21 ≤ a)
    (hq : q.Prime) (hq37 : 37 ≤ q) (hpkp : 1 ≤ kp) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have h5b := fSum_prime_pow_lt_tight3 (p := 5) (k := kp) Nat.prime_five
  have hσ := fSum_prime_pow_lt_tight3_of_ge (r := 37) (q := q) (k := kq)
    hq (by decide) hq37
  have hprod := fs161_tight3_5_tight3_37_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) <
      (161 : ℚ) / 100 *
        ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
          1 / ((5 : ℚ) ^ 2 * (5 - 1))) :=
    mul_lt_mul h2b (le_of_lt h5b)
      (fSum_pos (pow_ne_zero kp (show (5 : ℕ) ≠ 0 by decide))) (by positivity)
  have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
      (161 : ℚ) / 100 *
        ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
          1 / ((5 : ℚ) ^ 2 * (5 - 1))) *
        ((1 : ℚ) + 1 / (37 + 1) + 1 / (1 + 37 + 37 ^ 2) +
          1 / ((37 : ℚ) ^ 2 * (37 - 1))) :=
    mul_lt_mul h1 (le_of_lt hσ)
      (fSum_pos (pow_ne_zero kq hq.ne_zero)) (by positivity)
  exact this.trans hprod

lemma ge21_five_mid_ge43_le2_lt_two {a kp q kq : ℕ} (ha : 21 ≤ a)
    (hq : q.Prime) (hq43 : 43 ≤ q) (hpkp : 1 ≤ kp) (hkq2 : kq ≤ 2)
    (hkq : 1 ≤ kq) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_161_100 a
  have h5b := fSum_prime_pow_lt_tight3 (p := 5) (k := kp) Nat.prime_five
  have hC : fSum (q ^ kq) ≤ fSum (q ^ 2) :=
    fSum_le_sq_of_exp_le_two hq (by omega)
  have hqs : fSum (q ^ 2) ≤ fSum (43 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 43) hq hq43
  have hC' : fSum (q ^ kq) ≤ fSum (43 ^ 2) := le_trans hC hqs
  have hprod := fs161_tight3_5_f43sq_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) <
      (161 : ℚ) / 100 *
        ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
          1 / ((5 : ℚ) ^ 2 * (5 - 1))) :=
    mul_lt_mul h2b (le_of_lt h5b)
      (fSum_pos (pow_ne_zero kp (show (5 : ℕ) ≠ 0 by decide))) (by positivity)
  have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
      (161 : ℚ) / 100 *
        ((1 : ℚ) + 1 / (5 + 1) + 1 / (1 + 5 + 5 ^ 2) +
          1 / ((5 : ℚ) ^ 2 * (5 - 1))) * fSum (43 ^ 2) :=
    mul_lt_mul h1 hC'
      (fSum_pos (pow_ne_zero kq hq.ne_zero)) (by positivity)
  exact lt_of_lt_of_le this (le_of_lt hprod)

lemma not_seven_mod8_of_eq_eleven : ¬ (11 : ℕ) ≡ 7 [MOD 8] := by decide
lemma not_seven_mod8_of_eq_thirteen : ¬ (13 : ℕ) ≡ 7 [MOD 8] := by decide
lemma not_seven_mod8_of_eq_seventeen : ¬ (17 : ℕ) ≡ 7 [MOD 8] := by decide
lemma not_seven_mod8_of_eq_nineteen : ¬ (19 : ℕ) ≡ 7 [MOD 8] := by decide
lemma not_seven_mod8_of_eq_twentynine : ¬ (29 : ℕ) ≡ 7 [MOD 8] := by decide

lemma prime_eq_seven_or_twentythree_or_ge_thirtyone_of_mod8_seven
    {q : ℕ} (hq : q.Prime) (h7 : q ≡ 7 [MOD 8]) (hge : 7 ≤ q) :
    q = 7 ∨ q = 23 ∨ 31 ≤ q := by
  by_cases h31 : 31 ≤ q
  · exact Or.inr (Or.inr h31)
  · have hlt : q < 31 := by omega
    have n8 : ¬ Nat.Prime 8 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 4 = 8) (by decide) (by decide)
    have n9 : ¬ Nat.Prime 9 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 3 = 9) (by decide) (by decide)
    have n10 : ¬ Nat.Prime 10 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 5 = 10) (by decide) (by decide)
    have n12 : ¬ Nat.Prime 12 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 6 = 12) (by decide) (by decide)
    have n14 : ¬ Nat.Prime 14 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 7 = 14) (by decide) (by decide)
    have n15 : ¬ Nat.Prime 15 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 5 = 15) (by decide) (by decide)
    have n16 : ¬ Nat.Prime 16 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 8 = 16) (by decide) (by decide)
    have n18 : ¬ Nat.Prime 18 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 9 = 18) (by decide) (by decide)
    have n20 : ¬ Nat.Prime 20 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 10 = 20) (by decide) (by decide)
    have n21 : ¬ Nat.Prime 21 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 7 = 21) (by decide) (by decide)
    have n22 : ¬ Nat.Prime 22 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 11 = 22) (by decide) (by decide)
    have n24 : ¬ Nat.Prime 24 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 12 = 24) (by decide) (by decide)
    have n25 : ¬ Nat.Prime 25 :=
      Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 5 = 25) (by decide) (by decide)
    have n26 : ¬ Nat.Prime 26 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 13 = 26) (by decide) (by decide)
    have n27 : ¬ Nat.Prime 27 :=
      Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 9 = 27) (by decide) (by decide)
    have n28 : ¬ Nat.Prime 28 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 14 = 28) (by decide) (by decide)
    have n30 : ¬ Nat.Prime 30 :=
      Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 15 = 30) (by decide) (by decide)
    have n11 : q ≠ 11 := fun h => not_seven_mod8_of_eq_eleven (h ▸ h7)
    have n13 : q ≠ 13 := fun h => not_seven_mod8_of_eq_thirteen (h ▸ h7)
    have n17 : q ≠ 17 := fun h => not_seven_mod8_of_eq_seventeen (h ▸ h7)
    have n19 : q ≠ 19 := fun h => not_seven_mod8_of_eq_nineteen (h ▸ h7)
    have n29 : q ≠ 29 := fun h => not_seven_mod8_of_eq_twentynine (h ▸ h7)
    have hqne : q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 10 ∧ q ≠ 12 ∧ q ≠ 14 ∧ q ≠ 15 ∧
        q ≠ 16 ∧ q ≠ 18 ∧ q ≠ 20 ∧ q ≠ 21 ∧ q ≠ 22 ∧ q ≠ 24 ∧ q ≠ 25 ∧
        q ≠ 26 ∧ q ≠ 27 ∧ q ≠ 28 ∧ q ≠ 30 :=
      ⟨fun h => n8 (h ▸ hq), fun h => n9 (h ▸ hq), fun h => n10 (h ▸ hq),
        fun h => n12 (h ▸ hq), fun h => n14 (h ▸ hq), fun h => n15 (h ▸ hq),
        fun h => n16 (h ▸ hq), fun h => n18 (h ▸ hq), fun h => n20 (h ▸ hq),
        fun h => n21 (h ▸ hq), fun h => n22 (h ▸ hq), fun h => n24 (h ▸ hq),
        fun h => n25 (h ▸ hq), fun h => n26 (h ▸ hq), fun h => n27 (h ▸ hq),
        fun h => n28 (h ▸ hq), fun h => n30 (h ▸ hq)⟩
    have : q = 7 ∨ q = 23 := by omega
    exact this.elim Or.inl (fun h => Or.inr (Or.inl h))

/-- `a ≥ 21`, both odd primes `≥ 5`, `v₂ = -4`. -/
lemma fSum_ge21_family_neg_four_ne_two
    {a p kp q kq : ℕ} (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (hv : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -4) :
    fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) ≠ 2 := by
  haveI := two_fact
  wlog hle : p ≤ q generalizing p q kp kq
  · have hswap : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
        fSum (2 ^ a) * (fSum (q ^ kq) * fSum (p ^ kp)) := by ring
    rw [hswap]
    have hv' : padicValRat 2 (fSum (q ^ kq) * fSum (p ^ kp)) = -4 := by
      rw [mul_comm]; exact hv
    exact this hq hp hpq.symm hqo hpo hq5 hp5 hqkp hpkp hv'
      (le_of_lt (lt_of_not_ge hle))
  have hassoc : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
      fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
  rw [hassoc]
  have hvp := padicValRat_two_fSum_odd_prime_pow hp hpo hpkp
  have hvq := padicValRat_two_fSum_odd_prime_pow hq hqo hqkp
  have hvsum : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) = -4 := by
    rwa [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
      (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))] at hv
  cases eq_or_ne p 5 with
  | inl hp5eq =>
    subst hp5eq
    have hq7 : 7 ≤ q := by
      have : q ≠ 5 := hpq.symm
      have : q ≠ 6 := fun h => not_prime_six (h ▸ hq)
      omega
    have hv5 : padicValRat 2 (fSum (5 ^ kp)) = - (Nat.log 2 (kp + 1) : ℤ) :=
      log_of_v2_mod4_one (by decide) (by decide) (by decide) hpkp
    have hvq' : padicValRat 2 (fSum (q ^ kq)) = -4 + Nat.log 2 (kp + 1) := by
      linarith
    have hlog_le : Nat.log 2 (kp + 1) ≤ 3 := by
      have hvqZ : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
        Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqkp)
      have : (Nat.log 2 (kp + 1) : ℤ) ≤ 3 := by linarith
      omega
    have hlog_ge : 1 ≤ Nat.log 2 (kp + 1) := Nat.log_pos (by decide) (by omega)
    have hlog123 : Nat.log 2 (kp + 1) = 1 ∨ Nat.log 2 (kp + 1) = 2 ∨
        Nat.log 2 (kp + 1) = 3 := by omega
    rcases hlog123 with hlog1 | hlog2 | hlog3
    · -- kp = 1 or 2, v₂(q) = -3
      have hkp12 : kp = 1 ∨ kp = 2 := by
        have := exp_le_two_of_log_eq_one hpkp hlog1
        omega
      have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -3 := by
        rw [hvq']; omega
      rcases odd_mod8 hqo with hq1 | hq3 | hq5m | hq7m
      · -- q ≡ 1 [MOD 8] ⊆ ≡ 1 [MOD 4], exp 7–14
        have hq14 : q ≡ 1 [MOD 4] := p_mod4_one_of_mod8_one hq1
        have hlogq : Nat.log 2 (kq + 1) = 3 := by
          rw [log_of_v2_mod4_one hq hqo hq14 hqkp] at hvqeq
          omega
        have ⟨hkq7, hkq14⟩ := exp_high_of_log_eq_three hqkp hlogq
        have hq13 : 13 ≤ q := by
          have hne7 : q ≠ 7 := fun h => not_one_mod8_one_of_eq_seven (h ▸ hq1)
          have hne11 : q ≠ 11 := fun h => not_one_mod8_one_of_eq_eleven (h ▸ hq1)
          exact prime_ge_thirteen_of_ge_eleven_ne hq
            (prime_ge_eleven_of_ge_seven_ne hq hq7 hne7) hne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases prime_eq_seventeen_or_ge_twentynine_of_one_mod4 hq hq14 hq17 with
          | inl hq17eq =>
            subst hq17eq
            cases hkp12 with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_seventeen_mid_lt_two ha)
            | inr hk2 =>
              subst hk2
              exact ne_of_gt (ge21_five_two_seventeen_gt_two ha hqkp)
          | inr hq29 =>
            exact ne_of_lt (ge21_five_le2_ge29_mid_lt_two ha hq hq29 hkp12)
      · -- q ≡ 3 [MOD 8], exp 3–6
        have hlogq : Nat.log 2 (kq + 1) = 2 := by
          rw [log_of_v2_mod8_three hq hqo hq3 hqkp] at hvqeq
          omega
        have ⟨hkq3, hkq6⟩ := exp_mid_of_log_eq_two hqkp hlogq
        have hq11 : 11 ≤ q :=
          prime_ge_eleven_of_ge_seven_ne hq hq7 (fun h => by
            subst h
            have : ¬ (7 : ℕ) ≡ 3 [MOD 8] := by decide
            exact this hq3)
        cases eq_or_ne q 11 with
        | inl hq11eq =>
          subst hq11eq
          exact ne_of_gt (ge21_five_eleven_gt_two ha hpkp hqkp)
        | inr hqne11 =>
          have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hqne11
          have hqne13 : q ≠ 13 := fun h => not_three_mod8_of_eq_thirteen (h ▸ hq3)
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          have hqne17 : q ≠ 17 := fun h => not_three_mod8_of_eq_seventeen (h ▸ hq3)
          have hq19 : 19 ≤ q := by
            have : q ≠ 18 := fun h => not_prime_eighteen (h ▸ hq)
            omega
          cases prime_eq_nineteen_or_ge_fortythree_of_mod8_three hq hq3 hq19 with
          | inl hq19eq =>
            subst hq19eq
            cases hkp12 with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_nineteen_any_lt_two ha)
            | inr hk2 =>
              subst hk2
              exact ne_of_gt (ge21_five_two_nineteen_gt_two ha hqkp)
          | inr hq43 =>
            exact ne_of_lt (ge21_five_le2_ge43_lt_two ha hq hq43 hkp12)
      · -- q ≡ 5 [MOD 8] ⊆ ≡ 1 [MOD 4], same as ≡ 1 [MOD 8]
        have hq14 : q ≡ 1 [MOD 4] := p_mod4_one_of_mod8_five hq5m
        have hlogq : Nat.log 2 (kq + 1) = 3 := by
          rw [log_of_v2_mod4_one hq hqo hq14 hqkp] at hvqeq
          omega
        have ⟨hkq7, hkq14⟩ := exp_high_of_log_eq_three hqkp hlogq
        have hq13 : 13 ≤ q := by
          have hne7 : q ≠ 7 := by
            intro h; subst h; have : ¬ (7 : ℕ) ≡ 5 [MOD 8] := by decide
            exact this hq5m
          have hne11 : q ≠ 11 := by
            intro h; subst h; have : ¬ (11 : ℕ) ≡ 5 [MOD 8] := by decide
            exact this hq5m
          exact prime_ge_thirteen_of_ge_eleven_ne hq
            (prime_ge_eleven_of_ge_seven_ne hq hq7 hne7) hne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases prime_eq_seventeen_or_ge_twentynine_of_one_mod4 hq hq14 hq17 with
          | inl hq17eq =>
            subst hq17eq
            cases hkp12 with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_seventeen_mid_lt_two ha)
            | inr hk2 =>
              subst hk2
              exact ne_of_gt (ge21_five_two_seventeen_gt_two ha hqkp)
          | inr hq29 =>
            exact ne_of_lt (ge21_five_le2_ge29_mid_lt_two ha hq hq29 hkp12)
      · -- q ≡ 7 [MOD 8]: v₂ + log = 4, so v₂ = 3 and log = 1
        have h7v : 3 ≤ padicValNat 2 (q + 1) :=
          padicValNat_two_add_one_of_mod8_seven hqo hq7m
        have hlogq1 : 1 ≤ Nat.log 2 (kq + 1) := Nat.log_pos (by decide) (by omega)
        have hvform := v2_fSum_eq_one_sub hq hqo hqkp
        have hsum4 : padicValNat 2 (q + 1) + Nat.log 2 (kq + 1) = 4 := by
          rw [hvform] at hvqeq; omega
        have hv2q : padicValNat 2 (q + 1) = 3 := by omega
        have hlogq : Nat.log 2 (kq + 1) = 1 := by omega
        have hkq2 : kq ≤ 2 := exp_le_two_of_log_eq_one hqkp hlogq
        cases prime_eq_seven_or_twentythree_or_ge_thirtyone_of_mod8_seven
            hq hq7m hq7 with
        | inl hq7eq =>
          subst hq7eq
          exact ne_of_gt (ge21_five_seven_gt_two ha hpkp hqkp)
        | inr hrest =>
          cases hrest with
          | inl hq23eq =>
            subst hq23eq
            cases hkp12 with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_twentythree_lt_two ha hqkp hkq2)
            | inr hk2 =>
              subst hk2
              exact ne_of_gt (ge21_five_two_twentythree_gt_two ha hqkp)
          | inr hq31 =>
            exact ne_of_lt (ge21_five_le2_ge31_lt_two ha hq hq31 hkp12)
    · -- kp = 3–6, v₂(q) = -2
      have ⟨hkp3, hkp6⟩ := exp_mid_of_log_eq_two hpkp hlog2
      have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -2 := by
        rw [hvq']; omega
      rcases odd_mod8 hqo with hq1 | hq3 | hq5m | hq7m
      · -- q ≡ 1 [MOD 8] ⊆ ≡ 1 [MOD 4], exp 3–6
        have hq14 : q ≡ 1 [MOD 4] := p_mod4_one_of_mod8_one hq1
        have hlogq : Nat.log 2 (kq + 1) = 2 := by
          rw [log_of_v2_mod4_one hq hqo hq14 hqkp] at hvqeq
          omega
        have ⟨hkq3, hkq6⟩ := exp_mid_of_log_eq_two hqkp hlogq
        have hq13 : 13 ≤ q := by
          have hne7 : q ≠ 7 := fun h => not_one_mod8_one_of_eq_seven (h ▸ hq1)
          have hne11 : q ≠ 11 := fun h => not_one_mod8_one_of_eq_eleven (h ▸ hq1)
          exact prime_ge_thirteen_of_ge_eleven_ne hq
            (prime_ge_eleven_of_ge_seven_ne hq hq7 hne7) hne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases prime_eq_seventeen_or_ge_twentynine_of_one_mod4 hq hq14 hq17 with
          | inl hq17eq =>
            subst hq17eq
            have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
              fSum_le_of_exp_ge (by decide : Nat.Prime 5) hkp3
            have : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (17 ^ kq) :=
              ge21_five_cu_seventeen_gt_two ha hqkp
            have hmono := mul3_gt_of le_rfl h53 le_rfl
              (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
              (fSum_pos (pow_ne_zero a two_ne_zero)).le
              (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))).le
              (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
                (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
            exact ne_of_gt (lt_of_lt_of_le this hmono)
          | inr hq29 =>
            cases prime_eq_twentynine_or_ge_thirtyseven_of_one_mod4 hq hq14 hq29 with
            | inl hq29eq =>
              subst hq29eq
              exact ne_of_gt (ge21_five_ge3_twentynine_gt_two ha hkp3 hqkp)
            | inr hq37 =>
              exact ne_of_lt (ge21_five_mid_ge37_any_lt_two ha hq hq37 hpkp)
      · -- q ≡ 3 [MOD 8], exp 1–2
        have hlogq : Nat.log 2 (kq + 1) = 1 := by
          rw [log_of_v2_mod8_three hq hqo hq3 hqkp] at hvqeq
          omega
        have hkq2 : kq ≤ 2 := exp_le_two_of_log_eq_one hqkp hlogq
        have hq11 : 11 ≤ q :=
          prime_ge_eleven_of_ge_seven_ne hq hq7 (fun h => by
            subst h
            have : ¬ (7 : ℕ) ≡ 3 [MOD 8] := by decide
            exact this hq3)
        cases eq_or_ne q 11 with
        | inl hq11eq =>
          subst hq11eq
          exact ne_of_gt (ge21_five_eleven_gt_two ha hpkp hqkp)
        | inr hqne11 =>
          have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hqne11
          have hqne13 : q ≠ 13 := fun h => not_three_mod8_of_eq_thirteen (h ▸ hq3)
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          have hqne17 : q ≠ 17 := fun h => not_three_mod8_of_eq_seventeen (h ▸ hq3)
          have hq19 : 19 ≤ q := by
            have : q ≠ 18 := fun h => not_prime_eighteen (h ▸ hq)
            omega
          cases prime_eq_nineteen_or_ge_fortythree_of_mod8_three hq hq3 hq19 with
          | inl hq19eq =>
            subst hq19eq
            have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
              fSum_le_of_exp_ge (by decide : Nat.Prime 5) hkp3
            have : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (19 ^ kq) :=
              ge21_five_cu_nineteen_gt_two ha hqkp
            have hmono := mul3_gt_of le_rfl h53 le_rfl
              (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
              (fSum_pos (pow_ne_zero a two_ne_zero)).le
              (fSum_pos (pow_ne_zero kq (by decide : (19 : ℕ) ≠ 0))).le
              (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
                (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
            exact ne_of_gt (lt_of_lt_of_le this hmono)
          | inr hq43 =>
            exact ne_of_lt
              (ge21_five_mid_ge43_le2_lt_two ha hq hq43 hpkp hkq2 hqkp)
      · -- q ≡ 5 [MOD 8] ⊆ ≡ 1 [MOD 4]
        have hq14 : q ≡ 1 [MOD 4] := p_mod4_one_of_mod8_five hq5m
        have hlogq : Nat.log 2 (kq + 1) = 2 := by
          rw [log_of_v2_mod4_one hq hqo hq14 hqkp] at hvqeq
          omega
        have ⟨hkq3, hkq6⟩ := exp_mid_of_log_eq_two hqkp hlogq
        have hq13 : 13 ≤ q := by
          have hne7 : q ≠ 7 := by
            intro h; subst h; have : ¬ (7 : ℕ) ≡ 5 [MOD 8] := by decide
            exact this hq5m
          have hne11 : q ≠ 11 := by
            intro h; subst h; have : ¬ (11 : ℕ) ≡ 5 [MOD 8] := by decide
            exact this hq5m
          exact prime_ge_thirteen_of_ge_eleven_ne hq
            (prime_ge_eleven_of_ge_seven_ne hq hq7 hne7) hne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases prime_eq_seventeen_or_ge_twentynine_of_one_mod4 hq hq14 hq17 with
          | inl hq17eq =>
            subst hq17eq
            have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
              fSum_le_of_exp_ge (by decide : Nat.Prime 5) hkp3
            have : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (17 ^ kq) :=
              ge21_five_cu_seventeen_gt_two ha hqkp
            have hmono := mul3_gt_of le_rfl h53 le_rfl
              (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
              (fSum_pos (pow_ne_zero a two_ne_zero)).le
              (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))).le
              (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
                (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
            exact ne_of_gt (lt_of_lt_of_le this hmono)
          | inr hq29 =>
            cases prime_eq_twentynine_or_ge_thirtyseven_of_one_mod4 hq hq14 hq29 with
            | inl hq29eq =>
              subst hq29eq
              exact ne_of_gt (ge21_five_ge3_twentynine_gt_two ha hkp3 hqkp)
            | inr hq37 =>
              exact ne_of_lt (ge21_five_mid_ge37_any_lt_two ha hq hq37 hpkp)
      · -- q ≡ 7 [MOD 8]: v₂ ≥ 3 and log ≥ 1 cannot sum to 3
        have h7v : 3 ≤ padicValNat 2 (q + 1) :=
          padicValNat_two_add_one_of_mod8_seven hqo hq7m
        have hlogq1 : 1 ≤ Nat.log 2 (kq + 1) := Nat.log_pos (by decide) (by omega)
        have hvform := v2_fSum_eq_one_sub hq hqo hqkp
        rw [hvform] at hvqeq
        omega
    · -- kp = 7–14, v₂(q) = -1
      have ⟨hkp7, hkp14⟩ := exp_high_of_log_eq_three hpkp hlog3
      have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by
        rw [hvq']; omega
      have hq14 : q ≡ 1 [MOD 4] :=
        mod4_one_of_v2_eq_neg_one hq hqo hqkp hvqeq
      have hkq2 : kq ≤ 2 :=
        exp_le_two_of_v2_eq_neg_one hq hqo hqkp hvqeq
      have hq13or := prime_one_mod_four_cases hq hq14
      rcases hq13or with hq5eq | hq13eq | hq17eq | hq29
      · exact (hpq.symm hq5eq).elim
      · subst hq13eq
        have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
          fSum_le_of_exp_ge (by decide : Nat.Prime 5) (by omega)
        have : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (13 ^ kq) :=
          ge21_five_cu_thirteen_gt_two ha hqkp
        have hmono := mul3_gt_of le_rfl h53 le_rfl
          (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kq (by decide : (13 : ℕ) ≠ 0))).le
          (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
            (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
        exact ne_of_gt (lt_of_lt_of_le this hmono)
      · subst hq17eq
        have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
          fSum_le_of_exp_ge (by decide : Nat.Prime 5) (by omega)
        have : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (17 ^ kq) :=
          ge21_five_cu_seventeen_gt_two ha hqkp
        have hmono := mul3_gt_of le_rfl h53 le_rfl
          (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))).le
          (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
            (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
        exact ne_of_gt (lt_of_lt_of_le this hmono)
      · cases prime_eq_twentynine_or_ge_thirtyseven_of_one_mod4 hq hq14 hq29 with
        | inl hq29eq =>
          subst hq29eq
          exact ne_of_gt (ge21_five_ge3_twentynine_gt_two ha (by omega) hqkp)
        | inr hq37 =>
          exact ne_of_lt (ge21_five_ge3_ge37_lt_two ha hq hq37 hpkp hkq2 hqkp)
  | inr hpne5 =>
    have hp7 : 7 ≤ p := by
      have : p ≠ 6 := fun h => not_prime_six (h ▸ hp)
      omega
    have hq13 : 13 ≤ q := by
      have hq7 : 7 ≤ q := le_trans hp7 hle
      have hne7 : q ≠ 7 := fun h => hpq (le_antisymm hle (h ▸ hp7))
      have hq11 : 11 ≤ q := prime_ge_eleven_of_ge_seven_ne hq hq7 hne7
      have hne11 : q ≠ 11 := by
        intro h; subst h
        have hp7eq : p = 7 := by
          have : p ≠ 8 := fun h => not_prime_eight (h ▸ hp)
          have : p ≠ 9 := fun h => not_prime_nine (h ▸ hp)
          have : p ≠ 10 := fun h => not_prime_ten (h ▸ hp)
          have : p ≠ 11 := hpq
          omega
        subst hp7eq
        have hv7 : padicValRat 2 (fSum (7 ^ kp)) ≤ -3 :=
          v2_fSum_odd_prime_pow_mod8_seven_small hp hpo (by decide) hpkp
        have hv11 : padicValRat 2 (fSum (11 ^ kq)) ≤ -2 :=
          v2_fSum_odd_prime_pow_mod4_three hq hqo (by decide) hqkp
        linarith
      exact prime_ge_thirteen_of_ge_eleven_ne hq hq11 hne11
    exact ne_of_lt (ge21_no_five_neg_three_lt_two ha hp hq hp7 hq13)

lemma exp_of_log_eq_four {k : ℕ} (hk : 1 ≤ k)
    (hlog : Nat.log 2 (k + 1) = 4) : 15 ≤ k ∧ k ≤ 30 := by
  have hle : 2 ^ Nat.log 2 (k + 1) ≤ k + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hlt : k + 1 < 2 ^ (Nat.log 2 (k + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (k + 1)
  rw [hlog] at hle hlt
  omega

lemma eight_five_f5cu_f23_gt_two :
    2 < (8 : ℚ) / 5 * fSum (5 ^ 3) * fSum 23 := by
  rw [fSum_five_cu, fSum_twentythree]; norm_num

lemma ge21_five_cu_twentythree_gt_two {a kq : ℕ} (ha : 21 ≤ a) (hqkp : 1 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (23 ^ kq) := by
  have h23 := fSum_le_of_exp_ge_one (by decide : Nat.Prime 23) hqkp
  exact ge21_mul3_gt_two ha (by decide) (by decide) (by decide : 1 ≤ 3) hqkp
    le_rfl h23
    (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0)))
    (fSum_pos (by decide)) eight_five_f5cu_f23_gt_two

lemma ge21_five_ge3_lift {a kp q kq : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hpkp : 3 ≤ kp) (hqkp : 1 ≤ kq)
    (hth : 2 < fSum (2 ^ a) * fSum (5 ^ 3) * fSum (q ^ kq)) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) := by
  have h53 : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) hpkp
  have hmono := mul3_gt_of le_rfl h53 le_rfl
    (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
    (fSum_pos (pow_ne_zero a two_ne_zero)).le
    (fSum_pos (pow_ne_zero kq hq.ne_zero)).le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
  exact lt_of_lt_of_le hth hmono

lemma padicValNat_two_four : padicValNat 2 4 = 2 := by
  haveI := two_fact
  have hpos : (4 : ℕ) ≠ 0 := by decide
  have hle : 2 ≤ padicValNat 2 4 := by
    have : 2 ^ 2 ∣ 4 := by decide
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 4 < 3 := by
    by_contra hge
    have : 2 ^ 3 ∣ 4 := by
      have : 3 ≤ padicValNat 2 4 := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    have : 8 ∣ 4 := by simpa using this
    exact absurd this (by decide)
  omega

lemma padicValNat_two_thirtytwo : padicValNat 2 32 = 5 := by
  haveI := two_fact
  have hpos : (32 : ℕ) ≠ 0 := by decide
  have hle : 5 ≤ padicValNat 2 32 := by
    have : 2 ^ 5 ∣ 32 := by decide
    rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos] at this
    exact_mod_cast this
  have hlt : padicValNat 2 32 < 6 := by
    by_contra hge
    have : 2 ^ 6 ∣ 32 := by
      have : 6 ≤ padicValNat 2 32 := by omega
      rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity hpos]
      exact_mod_cast this
    have : 64 ∣ 32 := by simpa using this
    exact absurd this (by decide)
  omega

lemma v2_fSum_thirtyone_le_neg_five {k : ℕ} (hk : 1 ≤ k) :
    padicValRat 2 (fSum (31 ^ k)) ≤ -5 := by
  haveI := two_fact
  rw [v2_fSum_eq_one_sub (by decide : Nat.Prime 31) (by decide) hk]
  have : padicValNat 2 (31 + 1) = 5 := padicValNat_two_thirtytwo
  have : 1 ≤ Nat.log 2 (k + 1) := Nat.log_pos (by decide) (by omega)
  omega

lemma not_prime_thirty : ¬ Nat.Prime 30 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 15 = 30) (by decide) (by decide)
lemma not_prime_thirtytwo : ¬ Nat.Prime 32 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 16 = 32) (by decide) (by decide)
lemma not_prime_thirtythree : ¬ Nat.Prime 33 :=
  Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 11 = 33) (by decide) (by decide)
lemma not_prime_thirtyfour : ¬ Nat.Prime 34 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 17 = 34) (by decide) (by decide)
lemma not_prime_thirtyfive : ¬ Nat.Prime 35 :=
  Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 7 = 35) (by decide) (by decide)
lemma not_prime_thirtysix : ¬ Nat.Prime 36 :=
  Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 18 = 36) (by decide) (by decide)

/-- `a ≥ 21`, both odd primes `≥ 5`, `v₂ = -5`. -/
lemma fSum_ge21_family_neg_five_ne_two
    {a p kp q kq : ℕ} (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (hv : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -5) :
    fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) ≠ 2 := by
  haveI := two_fact
  wlog hle : p ≤ q generalizing p q kp kq
  · have hswap : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
        fSum (2 ^ a) * (fSum (q ^ kq) * fSum (p ^ kp)) := by ring
    rw [hswap]
    have hv' : padicValRat 2 (fSum (q ^ kq) * fSum (p ^ kp)) = -5 := by
      rw [mul_comm]; exact hv
    exact this hq hp hpq.symm hqo hpo hq5 hp5 hqkp hpkp hv'
      (le_of_lt (lt_of_not_ge hle))
  have hassoc : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
      fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
  rw [hassoc]
  have hvsum : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) = -5 := by
    rwa [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
      (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))] at hv
  cases eq_or_ne p 5 with
  | inl hp5eq =>
    subst hp5eq
    have hq7 : 7 ≤ q := by
      have : q ≠ 5 := hpq.symm
      have : q ≠ 6 := fun h => not_prime_six (h ▸ hq)
      omega
    cases eq_or_ne q 7 with
    | inl hq7eq =>
      subst hq7eq
      exact ne_of_gt (ge21_five_seven_gt_two ha hpkp hqkp)
    | inr hqne7 =>
      have hq11 : 11 ≤ q := prime_ge_eleven_of_ge_seven_ne hq hq7 hqne7
      cases eq_or_ne q 11 with
      | inl hq11eq =>
        subst hq11eq
        exact ne_of_gt (ge21_five_eleven_gt_two ha hpkp hqkp)
      | inr hqne11 =>
        have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hqne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases eq_or_ne q 17 with
          | inl hq17eq =>
            subst hq17eq
            cases Nat.eq_or_lt_of_le hpkp with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_seventeen_mid_lt_two ha)
            | inr hkt =>
              have hkp2 : 2 ≤ kp := by omega
              cases Nat.eq_or_lt_of_le hkp2 with
              | inl hk2 =>
                subst hk2
                exact ne_of_gt (ge21_five_two_seventeen_gt_two ha hqkp)
              | inr hkp3' =>
                exact ne_of_gt (ge21_five_ge3_lift ha (by decide) (by omega) hqkp
                  (ge21_five_cu_seventeen_gt_two ha hqkp))
          | inr hqne17 =>
            have hq19 : 19 ≤ q := by
              have : q ≠ 18 := fun h => not_prime_eighteen (h ▸ hq)
              omega
            cases eq_or_ne q 19 with
            | inl hq19eq =>
              subst hq19eq
              cases Nat.eq_or_lt_of_le hpkp with
              | inl hk1 =>
                subst hk1
                exact ne_of_lt (ge21_five_one_nineteen_any_lt_two ha)
              | inr hkt =>
                have hkp2 : 2 ≤ kp := by omega
                cases Nat.eq_or_lt_of_le hkp2 with
                | inl hk2 =>
                  subst hk2
                  exact ne_of_gt (ge21_five_two_nineteen_gt_two ha hqkp)
                | inr _ =>
                  exact ne_of_gt (ge21_five_ge3_lift ha (by decide) (by omega) hqkp
                    (ge21_five_cu_nineteen_gt_two ha hqkp))
            | inr hqne19 =>
              have hq23 : 23 ≤ q :=
                prime_ge_twentythree_of_ge_nineteen_ne hq hq19 hqne19
              cases eq_or_ne q 23 with
              | inl hq23eq =>
                subst hq23eq
                cases Nat.eq_or_lt_of_le hpkp with
                | inl hk1 =>
                  subst hk1
                  have hkq2 : kq ≤ 2 ∨ 3 ≤ kq := by omega
                  cases hkq2 with
                  | inl hle2 =>
                    exact ne_of_lt (ge21_five_one_twentythree_lt_two ha hqkp hle2)
                  | inr _ =>
                    have hσ := fSum_prime_pow_lt_tight (p := 23) (k := kq)
                      (by decide)
                    have h2b := fSum_two_pow_lt_161_100 a
                    have hprod : (161 : ℚ) / 100 * fSum 5 *
                        (1 + 1 / ((23 : ℚ) + 1) + 1 / (23 * (23 - 1))) < 2 := by
                      rw [fSum_five]; norm_num
                    have : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (23 ^ kq) <
                        (161 : ℚ) / 100 * fSum 5 *
                          (1 + 1 / ((23 : ℚ) + 1) + 1 / (23 * (23 - 1))) := by
                      rw [pow_one]
                      have h1 : fSum (2 ^ a) * fSum 5 < (161 : ℚ) / 100 * fSum 5 :=
                        mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
                      exact mul_lt_mul h1 (le_of_lt hσ)
                        (fSum_pos (pow_ne_zero kq (by decide : (23 : ℕ) ≠ 0)))
                        (mul_nonneg (by norm_num)
                          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                    exact ne_of_lt (this.trans hprod)
                | inr hkt =>
                  have hkp2 : 2 ≤ kp := by omega
                  cases Nat.eq_or_lt_of_le hkp2 with
                  | inl hk2 =>
                    subst hk2
                    exact ne_of_gt (ge21_five_two_twentythree_gt_two ha hqkp)
                  | inr _ =>
                    exact ne_of_gt (ge21_five_ge3_lift ha (by decide) (by omega) hqkp
                      (ge21_five_cu_twentythree_gt_two ha hqkp))
              | inr hqne23 =>
                have hq29 : 29 ≤ q :=
                  prime_ge_twentynine_of_ge_twentythree_ne hq hq23 hqne23
                cases eq_or_ne q 29 with
                | inl hq29eq =>
                  subst hq29eq
                  have hkp12 : kp = 1 ∨ kp = 2 ∨ 3 ≤ kp := by omega
                  rcases hkp12 with hk1 | hk2 | hk3
                  · subst hk1
                    exact ne_of_lt
                      (ge21_five_le2_ge29_mid_lt_two ha (by decide) (by decide)
                        (Or.inl rfl))
                  · subst hk2
                    exact ne_of_lt
                      (ge21_five_le2_ge29_mid_lt_two ha (by decide) (by decide)
                        (Or.inr rfl))
                  · exact ne_of_gt (ge21_five_ge3_twentynine_gt_two ha hk3 hqkp)
                | inr hqne29 =>
                  have hq31 : 31 ≤ q := by
                    have : q ≠ 30 := fun h => not_prime_thirty (h ▸ hq)
                    omega
                  cases eq_or_ne q 31 with
                  | inl hq31eq =>
                    subst hq31eq
                    have hv5le : padicValRat 2 (fSum (5 ^ kp)) ≤ -1 :=
                      Int.le_sub_one_of_lt
                        (padicValRat_two_fSum_odd_prime_pow_neg
                          (by decide) (by decide) hpkp)
                    have hv31 := v2_fSum_thirtyone_le_neg_five hqkp
                    linarith
                  | inr hqne31 =>
                    have hq37 : 37 ≤ q := by
                      have n32 : q ≠ 32 := fun h => not_prime_thirtytwo (h ▸ hq)
                      have n33 : q ≠ 33 := fun h => not_prime_thirtythree (h ▸ hq)
                      have n34 : q ≠ 34 := fun h => not_prime_thirtyfour (h ▸ hq)
                      have n35 : q ≠ 35 := fun h => not_prime_thirtyfive (h ▸ hq)
                      have n36 : q ≠ 36 := fun h => not_prime_thirtysix (h ▸ hq)
                      omega
                    exact ne_of_lt (ge21_five_mid_ge37_any_lt_two ha hq hq37 hpkp)
  | inr hpne5 =>
    have hp7 : 7 ≤ p := by
      have : p ≠ 6 := fun h => not_prime_six (h ▸ hp)
      omega
    have hq7 : 7 ≤ q := le_trans hp7 hle
    cases eq_or_ne q 11 with
    | inl hq11eq =>
      subst hq11eq
      have hp7eq : p = 7 := by
        have : p ≠ 8 := fun h => not_prime_eight (h ▸ hp)
        have : p ≠ 9 := fun h => not_prime_nine (h ▸ hp)
        have : p ≠ 10 := fun h => not_prime_ten (h ▸ hp)
        have : p ≠ 11 := hpq
        omega
      subst hp7eq
      exact fSum_two_pow_ge21_seven_eleven_ne_two ha hpkp hqkp
    | inr hqne11 =>
      have hne7 : q ≠ 7 := fun h => hpq (le_antisymm hle (h ▸ hp7))
      have hq11 : 11 ≤ q := prime_ge_eleven_of_ge_seven_ne hq hq7 hne7
      have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hqne11
      exact ne_of_lt (ge21_no_five_neg_three_lt_two ha hp hq hp7 hq13)

lemma sum_Ico_mersenne_ge_fifteen_lt (b : ℕ) :
    ∑ k ∈ Ico 15 b, (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) < (1 : ℚ) / 16384 := by
  have hle :
      ∑ k ∈ Ico 15 b, (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≤
        ∑ k ∈ Ico 15 b, (1 / 2 : ℚ) ^ k := by
    refine sum_le_sum fun k hk => ?_
    have hk1 : 1 ≤ k := by
      have : 15 ≤ k := (mem_Ico.mp hk).1
      omega
    have hcmp := (mersenne_recip_lt hk1).le
    have hcast : ((2 ^ k : ℕ) : ℚ) = (2 : ℚ) ^ k := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    have : (1 : ℚ) / ((2 ^ k : ℕ) : ℚ) = (1 / 2 : ℚ) ^ k := by
      rw [hcast, div_pow, one_pow]
    rw [this] at hcmp
    exact hcmp
  have hgeom : ∑ k ∈ Ico 15 b, (1 / 2 : ℚ) ^ k < (1 : ℚ) / 16384 := by
    rw [sum_Ico_eq_sum_range]
    have hfac :
        ∑ i ∈ range (b - 15), (1 / 2 : ℚ) ^ (15 + i) =
          (1 / 2 : ℚ) ^ 15 * ∑ i ∈ range (b - 15), (1 / 2 : ℚ) ^ i := by
      refine (sum_congr rfl fun i _ => ?_).trans (mul_sum _ _ _).symm
      rw [pow_add]
    rw [hfac]
    have hgs := geom_sum_half_lt (b - 15)
    have : (1 / 2 : ℚ) ^ 15 = 1 / 32768 := by norm_num
    nlinarith
  linarith

lemma fSum_two_pow_fourteen_eq :
    fSum (2 ^ 14) =
      fSum (2 ^ 8) + (1 : ℚ) / 1023 + 1 / 2047 + 1 / 4095 + 1 / 8191 +
        1 / 16383 + 1 / 32767 := by
  have h9 : 9 ≤ 15 := by decide
  have hsplit :
      fSum (2 ^ 14) =
        fSum (2 ^ 8) +
          ∑ k ∈ Ico 9 15, (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
    rw [fSum_two_pow_eq, fSum_two_pow_eq]
    simpa using
      (sum_range_add_sum_Ico
        (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) h9).symm
  have hpeel :
      ∑ k ∈ Ico 9 15, (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) =
        (1 : ℚ) / 1023 + 1 / 2047 + 1 / 4095 + 1 / 8191 +
          1 / 16383 + 1 / 32767 := by
    have e9 : Ico 9 15 = insert 9 (Ico 10 15) := by
      ext x; simp [mem_Ico]; omega
    have e10 : Ico 10 15 = insert 10 (Ico 11 15) := by
      ext x; simp [mem_Ico]; omega
    have e11 : Ico 11 15 = insert 11 (Ico 12 15) := by
      ext x; simp [mem_Ico]; omega
    have e12 : Ico 12 15 = insert 12 (Ico 13 15) := by
      ext x; simp [mem_Ico]; omega
    have e13 : Ico 13 15 = insert 13 (Ico 14 15) := by
      ext x; simp [mem_Ico]; omega
    have e14 : Ico 14 15 = {14} := rfl
    rw [e9, sum_insert (by simp [mem_Ico]),
      e10, sum_insert (by simp [mem_Ico]),
      e11, sum_insert (by simp [mem_Ico]),
      e12, sum_insert (by simp [mem_Ico]),
      e13, sum_insert (by simp [mem_Ico]),
      e14, sum_singleton]
    norm_num
  rw [hsplit, hpeel]
  ring

lemma fSum_two_pow_fourteen_add_tail_lt :
    fSum (2 ^ 14) + (1 : ℚ) / 16384 < (4017 : ℚ) / 2500 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight]
  norm_num

lemma fSum_two_pow_lt_4017_2500 (a : ℕ) :
    fSum (2 ^ a) < (4017 : ℚ) / 2500 := by
  cases lt_or_ge a 15 with
  | inl hlt =>
    have hle : fSum (2 ^ a) ≤ fSum (2 ^ 14) := by
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with
      | inl h => exact (fSum_strict_mono_two h).le
      | inr h => rw [h]
    have : fSum (2 ^ 14) < (4017 : ℚ) / 2500 := by
      have hpos : (0 : ℚ) < 1 / 16384 := by norm_num
      linarith [fSum_two_pow_fourteen_add_tail_lt]
    exact lt_of_le_of_lt hle this
  | inr hge =>
    have h15 : 15 ≤ a + 1 := by omega
    have hsplit :
        fSum (2 ^ a) =
          fSum (2 ^ 14) +
            ∑ k ∈ Ico 15 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
      rw [fSum_two_pow_eq, fSum_two_pow_eq]
      simpa using
        (sum_range_add_sum_Ico
          (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) h15).symm
    have htail := sum_Ico_mersenne_ge_fifteen_lt (a + 1)
    linarith [fSum_two_pow_fourteen_add_tail_lt]

lemma fSum_thirty_one : fSum 31 = (33 : ℚ) / 32 := by
  rw [fSum_prime (by decide : Nat.Prime 31)]; norm_num

lemma fSum_thirtyone_sq : fSum (31 ^ 2) = (32801 : ℚ) / 31776 := by
  rw [fSum_prime_sq (by decide : Nat.Prime 31)]; norm_num

lemma fSum_five_le_five_succ (k : ℕ) :
    fSum (5 ^ k) ≤ fSum (5 ^ 5) + (1 : ℚ) / 12500 := by
  cases le_or_gt k 5 with
  | inl hle =>
    have : fSum (5 ^ k) ≤ fSum (5 ^ 5) :=
      fSum_le_of_exp_ge Nat.prime_five hle
    exact le_trans this
      (le_add_of_nonneg_right (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 12500))
  | inr hgt =>
    have h6 : 6 ≤ k + 1 := by omega
    have hsplit :
        fSum (5 ^ k) =
          fSum (5 ^ 5) +
            ∑ j ∈ Ico 6 (k + 1), (1 : ℚ) / (sigma 1 (5 ^ j) : ℚ) := by
      rw [fSum_prime_pow Nat.prime_five, fSum_prime_pow Nat.prime_five]
      simpa using
        (sum_range_add_sum_Ico
          (fun j => (1 : ℚ) / (sigma 1 (5 ^ j) : ℚ)) h6).symm
    have hle :
        ∑ j ∈ Ico 6 (k + 1), (1 : ℚ) / (sigma 1 (5 ^ j) : ℚ) ≤
          ∑ j ∈ Ico 6 (k + 1), (1 / 5 : ℚ) ^ j := by
      refine sum_le_sum fun j hj => ?_
      have hj1 : 1 ≤ j := by
        have : 6 ≤ j := (mem_Ico.mp hj).1
        omega
      have hcmp := (inv_sigma_lt_pow Nat.prime_five hj1).le
      rwa [← one_div_pow] at hcmp
    have hgeom :
        ∑ j ∈ Ico 6 (k + 1), (1 / 5 : ℚ) ^ j ≤
          ((1 / 5 : ℚ) ^ 6) / (1 - 1 / 5) :=
      geom_sum_Ico_le_of_lt_one (by positivity) (by norm_num)
    have hval : ((1 / 5 : ℚ) ^ 6) / (1 - 1 / 5) = 1 / 12500 := by norm_num
    linarith

lemma fs4017_f5five_succ_f31_lt_two :
    (4017 : ℚ) / 2500 * (fSum (5 ^ 5) + 1 / 12500) * ((33 : ℚ) / 32) < 2 := by
  rw [fSum_five_five_pow]; norm_num

lemma fs4017_f5cu_tight31_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 3) *
      (1 + 1 / ((31 : ℚ) + 1) + 1 / (31 * (31 - 1))) < 2 := by
  rw [fSum_five_cu]; norm_num

lemma eight03_f5four_f31sq_gt_two :
    2 < (803 : ℚ) / 500 * fSum (5 ^ 4) * fSum (31 ^ 2) := by
  rw [fSum_five_four, fSum_thirtyone_sq]; norm_num

lemma ge21_five_any_thirtyone_one_lt_two {a kp : ℕ} (ha : 21 ≤ a) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (31 ^ 1) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have h5b := fSum_five_le_five_succ kp
  have h31 : fSum (31 ^ 1) = (33 : ℚ) / 32 := by
    rw [pow_one, fSum_thirty_one]
  have hprod := fs4017_f5five_succ_f31_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) <
      (4017 : ℚ) / 2500 * (fSum (5 ^ 5) + 1 / 12500) :=
    mul_lt_mul h2b h5b (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0)))
      (by positivity)
  have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (31 ^ 1) <
      (4017 : ℚ) / 2500 * (fSum (5 ^ 5) + 1 / 12500) * ((33 : ℚ) / 32) := by
    rw [h31]
    exact mul_lt_mul_of_pos_right h1 (by norm_num)
  exact this.trans hprod

lemma ge21_five_cu_thirtyone_any_lt_two {a kq : ℕ} (ha : 21 ≤ a) :
    fSum (2 ^ a) * fSum (5 ^ 3) * fSum (31 ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hσ := fSum_prime_pow_lt_tight (p := 31) (k := kq) (by decide)
  have hprod := fs4017_f5cu_tight31_lt_two
  have h1 : fSum (2 ^ a) * fSum (5 ^ 3) < (4017 : ℚ) / 2500 * fSum (5 ^ 3) :=
    mul_lt_mul_of_pos_right h2b
      (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0)))
  have : fSum (2 ^ a) * fSum (5 ^ 3) * fSum (31 ^ kq) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 3) *
        (1 + 1 / ((31 : ℚ) + 1) + 1 / (31 * (31 - 1))) :=
    mul_lt_mul h1 (le_of_lt hσ)
      (fSum_pos (pow_ne_zero kq (by decide : (31 : ℕ) ≠ 0)))
      (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le)
  exact this.trans hprod

lemma ge21_five_ge4_thirtyone_ge2_gt_two {a kp kq : ℕ} (ha : 21 ≤ a)
    (hpkp : 4 ≤ kp) (hqkp : 2 ≤ kq) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (31 ^ kq) := by
  have hlo := fSum_two_pow_ge21_gt_803_500 ha
  have h54 : fSum (5 ^ 4) ≤ fSum (5 ^ kp) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) hpkp
  have h312 : fSum (31 ^ 2) ≤ fSum (31 ^ kq) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 31) hqkp
  have hmin : 2 < fSum (2 ^ a) * fSum (5 ^ 4) * fSum (31 ^ 2) := by
    have hgt0 := eight03_f5four_f31sq_gt_two
    have : (803 : ℚ) / 500 * fSum (5 ^ 4) * fSum (31 ^ 2) <
        fSum (2 ^ a) * fSum (5 ^ 4) * fSum (31 ^ 2) :=
      mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right hlo
          (fSum_pos (pow_ne_zero 4 (by decide : (5 : ℕ) ≠ 0))))
        (fSum_pos (pow_ne_zero 2 (by decide : (31 : ℕ) ≠ 0)))
    exact hgt0.trans this
  have hmono := mul3_gt_of le_rfl h54 h312
    (fSum_pos (pow_ne_zero 4 (by decide : (5 : ℕ) ≠ 0))).le
    (fSum_pos (pow_ne_zero a two_ne_zero)).le
    (fSum_pos (pow_ne_zero 2 (by decide : (31 : ℕ) ≠ 0))).le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))).le)
  exact lt_of_lt_of_le hmin hmono

/-- `a ≥ 21`, both odd primes `≥ 5`. No valuation hypothesis. -/
lemma fSum_ge21_family_neg_six_ne_two
    {a p kp q kq : ℕ} (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq) :
    fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) ≠ 2 := by
  haveI := two_fact
  wlog hle : p ≤ q generalizing p q kp kq
  · have hswap : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
        fSum (2 ^ a) * (fSum (q ^ kq) * fSum (p ^ kp)) := by ring
    rw [hswap]
    exact this hq hp hpq.symm hqo hpo hq5 hp5 hqkp hpkp
      (le_of_lt (lt_of_not_ge hle))
  have hassoc : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
      fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
  rw [hassoc]
  cases eq_or_ne p 5 with
  | inl hp5eq =>
    subst hp5eq
    have hq7 : 7 ≤ q := by
      have : q ≠ 5 := hpq.symm
      have : q ≠ 6 := fun h => not_prime_six (h ▸ hq)
      omega
    cases eq_or_ne q 7 with
    | inl hq7eq =>
      subst hq7eq
      exact ne_of_gt (ge21_five_seven_gt_two ha hpkp hqkp)
    | inr hqne7 =>
      have hq11 : 11 ≤ q := prime_ge_eleven_of_ge_seven_ne hq hq7 hqne7
      cases eq_or_ne q 11 with
      | inl hq11eq =>
        subst hq11eq
        exact ne_of_gt (ge21_five_eleven_gt_two ha hpkp hqkp)
      | inr hqne11 =>
        have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hqne11
        cases eq_or_ne q 13 with
        | inl hq13eq =>
          subst hq13eq
          exact ne_of_gt (ge21_five_thirteen_gt_two ha hpkp hqkp)
        | inr hqne13 =>
          have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
          cases eq_or_ne q 17 with
          | inl hq17eq =>
            subst hq17eq
            cases Nat.eq_or_lt_of_le hpkp with
            | inl hk1 =>
              subst hk1
              exact ne_of_lt (ge21_five_one_seventeen_mid_lt_two ha)
            | inr hkt =>
              have hkp2 : 2 ≤ kp := by omega
              cases Nat.eq_or_lt_of_le hkp2 with
              | inl hk2 =>
                subst hk2
                exact ne_of_gt (ge21_five_two_seventeen_gt_two ha hqkp)
              | inr hkp3' =>
                exact ne_of_gt (ge21_five_ge3_lift ha (by decide) (by omega) hqkp
                  (ge21_five_cu_seventeen_gt_two ha hqkp))
          | inr hqne17 =>
            have hq19 : 19 ≤ q := by
              have : q ≠ 18 := fun h => not_prime_eighteen (h ▸ hq)
              omega
            cases eq_or_ne q 19 with
            | inl hq19eq =>
              subst hq19eq
              cases Nat.eq_or_lt_of_le hpkp with
              | inl hk1 =>
                subst hk1
                exact ne_of_lt (ge21_five_one_nineteen_any_lt_two ha)
              | inr hkt =>
                have hkp2 : 2 ≤ kp := by omega
                cases Nat.eq_or_lt_of_le hkp2 with
                | inl hk2 =>
                  subst hk2
                  exact ne_of_gt (ge21_five_two_nineteen_gt_two ha hqkp)
                | inr _ =>
                  exact ne_of_gt (ge21_five_ge3_lift ha (by decide) (by omega) hqkp
                    (ge21_five_cu_nineteen_gt_two ha hqkp))
            | inr hqne19 =>
              have hq23 : 23 ≤ q :=
                prime_ge_twentythree_of_ge_nineteen_ne hq hq19 hqne19
              cases eq_or_ne q 23 with
              | inl hq23eq =>
                subst hq23eq
                cases Nat.eq_or_lt_of_le hpkp with
                | inl hk1 =>
                  subst hk1
                  have hkq2 : kq ≤ 2 ∨ 3 ≤ kq := by omega
                  cases hkq2 with
                  | inl hle2 =>
                    exact ne_of_lt (ge21_five_one_twentythree_lt_two ha hqkp hle2)
                  | inr _ =>
                    have hσ := fSum_prime_pow_lt_tight (p := 23) (k := kq)
                      (by decide)
                    have h2b := fSum_two_pow_lt_161_100 a
                    have hprod : (161 : ℚ) / 100 * fSum 5 *
                        (1 + 1 / ((23 : ℚ) + 1) + 1 / (23 * (23 - 1))) < 2 := by
                      rw [fSum_five]; norm_num
                    have : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (23 ^ kq) <
                        (161 : ℚ) / 100 * fSum 5 *
                          (1 + 1 / ((23 : ℚ) + 1) + 1 / (23 * (23 - 1))) := by
                      rw [pow_one]
                      have h1 : fSum (2 ^ a) * fSum 5 < (161 : ℚ) / 100 * fSum 5 :=
                        mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
                      exact mul_lt_mul h1 (le_of_lt hσ)
                        (fSum_pos (pow_ne_zero kq (by decide : (23 : ℕ) ≠ 0)))
                        (mul_nonneg (by norm_num)
                          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                    exact ne_of_lt (this.trans hprod)
                | inr hkt =>
                  have hkp2 : 2 ≤ kp := by omega
                  cases Nat.eq_or_lt_of_le hkp2 with
                  | inl hk2 =>
                    subst hk2
                    exact ne_of_gt (ge21_five_two_twentythree_gt_two ha hqkp)
                  | inr _ =>
                    exact ne_of_gt (ge21_five_ge3_lift ha (by decide) (by omega) hqkp
                      (ge21_five_cu_twentythree_gt_two ha hqkp))
              | inr hqne23 =>
                have hq29 : 29 ≤ q :=
                  prime_ge_twentynine_of_ge_twentythree_ne hq hq23 hqne23
                cases eq_or_ne q 29 with
                | inl hq29eq =>
                  subst hq29eq
                  have hkp12 : kp = 1 ∨ kp = 2 ∨ 3 ≤ kp := by omega
                  rcases hkp12 with hk1 | hk2 | hk3
                  · subst hk1
                    exact ne_of_lt
                      (ge21_five_le2_ge29_mid_lt_two ha (by decide) (by decide)
                        (Or.inl rfl))
                  · subst hk2
                    exact ne_of_lt
                      (ge21_five_le2_ge29_mid_lt_two ha (by decide) (by decide)
                        (Or.inr rfl))
                  · exact ne_of_gt (ge21_five_ge3_twentynine_gt_two ha hk3 hqkp)
                | inr hqne29 =>
                  have hq31 : 31 ≤ q := by
                    have : q ≠ 30 := fun h => not_prime_thirty (h ▸ hq)
                    omega
                  cases eq_or_ne q 31 with
                  | inl hq31eq =>
                    subst hq31eq
                    have hkp12 : kp = 1 ∨ kp = 2 ∨ kp = 3 ∨ 4 ≤ kp := by omega
                    rcases hkp12 with hk1 | hk2 | hk3 | hk4
                    · subst hk1
                      exact ne_of_lt
                        (ge21_five_le2_ge31_lt_two ha (by decide) (by decide)
                          (Or.inl rfl))
                    · subst hk2
                      exact ne_of_lt
                        (ge21_five_le2_ge31_lt_two ha (by decide) (by decide)
                          (Or.inr rfl))
                    · subst hk3
                      exact ne_of_lt (ge21_five_cu_thirtyone_any_lt_two ha)
                    · cases Nat.eq_or_lt_of_le hqkp with
                      | inl hl1 =>
                        subst hl1
                        exact ne_of_lt (ge21_five_any_thirtyone_one_lt_two ha)
                      | inr hl2 =>
                        exact ne_of_gt
                          (ge21_five_ge4_thirtyone_ge2_gt_two ha hk4 (by omega))
                  | inr hqne31 =>
                    have hq37 : 37 ≤ q := by
                      have n32 : q ≠ 32 := fun h => not_prime_thirtytwo (h ▸ hq)
                      have n33 : q ≠ 33 := fun h => not_prime_thirtythree (h ▸ hq)
                      have n34 : q ≠ 34 := fun h => not_prime_thirtyfour (h ▸ hq)
                      have n35 : q ≠ 35 := fun h => not_prime_thirtyfive (h ▸ hq)
                      have n36 : q ≠ 36 := fun h => not_prime_thirtysix (h ▸ hq)
                      omega
                    exact ne_of_lt (ge21_five_mid_ge37_any_lt_two ha hq hq37 hpkp)
  | inr hpne5 =>
    have hp7 : 7 ≤ p := by
      have : p ≠ 6 := fun h => not_prime_six (h ▸ hp)
      omega
    have hq7 : 7 ≤ q := le_trans hp7 hle
    cases eq_or_ne q 11 with
    | inl hq11eq =>
      subst hq11eq
      have hp7eq : p = 7 := by
        have : p ≠ 8 := fun h => not_prime_eight (h ▸ hp)
        have : p ≠ 9 := fun h => not_prime_nine (h ▸ hp)
        have : p ≠ 10 := fun h => not_prime_ten (h ▸ hp)
        have : p ≠ 11 := hpq
        omega
      subst hp7eq
      exact fSum_two_pow_ge21_seven_eleven_ne_two ha hpkp hqkp
    | inr hqne11 =>
      have hne7 : q ≠ 7 := fun h => hpq (le_antisymm hle (h ▸ hp7))
      have hq11 : 11 ≤ q := prime_ge_eleven_of_ge_seven_ne hq hq7 hne7
      have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hqne11
      exact ne_of_lt (ge21_no_five_neg_three_lt_two ha hp hq hp7 hq13)

lemma fSum_mod16_five_omega_two_big_ne_two
    {a p kp q kq : ℕ} (ha : 1 ≤ a) (ha5 : a ≡ 5 [MOD 16])
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (hbig : 3 ≤ kp ∨ 3 ≤ kq ∨ p ≡ 3 [MOD 4] ∨ q ≡ 3 [MOD 4])
    (hv3 : a = 5 ∨ padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -3) :
    fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) ≠ 2 := by
  have hage : 5 ≤ a := by
    have : a % 16 = 5 := by simpa [Nat.ModEq] using ha5
    omega
  have hassoc : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) =
      fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
  -- Split `a = 5` versus `a ≥ 21`.
  cases Nat.eq_or_lt_of_le hage with
  | inl haeq =>
    -- `a = 5`: evaluate against explicit bounds / small primes.
    subst haeq
    exact fSum_two_pow_five_two_odd_ne_two hp hq hpq hpo hqo hpkp hqkp hbig
  | inr halt =>
    have ha21 : 21 ≤ a := by
      have : a % 16 = 5 := by simpa [Nat.ModEq] using ha5
      omega
    have ha7 : 7 ≤ a := by omega
    have h27 := fSum_two_pow_ge_seven ha7
    have hp3or := odd_prime_eq_three_or_ge_five hp hpo
    have hq3or := odd_prime_eq_three_or_ge_five hq hqo
    -- If either prime is 3, then already `fSum(2^a)*fSum(3) > 2`.
    have h3gt : ∀ k : ℕ, 1 ≤ k →
        2 < fSum (2 ^ a) * fSum (3 ^ k) := by
      intro k hk
      have h3 : fSum 3 ≤ fSum (3 ^ k) := by
        cases Nat.eq_or_lt_of_le hk with
        | inl hk1 => subst hk1; rw [pow_one]
        | inr hkt =>
          simpa [pow_one] using
            (fSum_strict_mono_prime_pow Nat.prime_three hkt).le
      have heq2 : (8 : ℚ) / 5 * (5 / 4) = 2 := by norm_num
      have h3' : (5 : ℚ) / 4 ≤ fSum (3 ^ k) := by rwa [← fSum_three]
      have hmul : (8 : ℚ) / 5 * (5 / 4) < fSum (2 ^ a) * fSum (3 ^ k) :=
        mul_lt_mul h27 h3' (by norm_num) (by positivity)
      linarith [heq2]
    rcases hp3or with hp3 | hp5
    · subst hp3
      have : 2 < fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) := by
        have h1 := h3gt kp hpkp
        have h2 : 1 < fSum (q ^ kq) := fSum_gt_one_of_prime_pow hq hqkp
        nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
          fSum_pos (pow_ne_zero kp (by decide : (3 : ℕ) ≠ 0)),
          fSum_pos (pow_ne_zero kq hq.ne_zero)]
      rw [hassoc]
      exact ne_of_gt this
    · rcases hq3or with hq3 | hq5
      · subst hq3
        have : 2 < fSum (2 ^ a) * fSum (p ^ kp) * fSum (3 ^ kq) := by
          have h1 := h3gt kq hqkp
          have h2 : 1 < fSum (p ^ kp) := fSum_gt_one_of_prime_pow hp hpkp
          have hswap : fSum (2 ^ a) * fSum (p ^ kp) * fSum (3 ^ kq) =
              fSum (2 ^ a) * fSum (3 ^ kq) * fSum (p ^ kp) := by ring
          rw [hswap]
          nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
            fSum_pos (pow_ne_zero kq (by decide : (3 : ℕ) ≠ 0)),
            fSum_pos (pow_ne_zero kp hp.ne_zero)]
        rw [hassoc]
        exact ne_of_gt this
      · -- both primes ≥ 5, `a ≥ 21`: the caller guarantees `v₂ = -3`.
        have hv : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -3 :=
          hv3.elim (fun h => (Nat.ne_of_gt halt h).elim) id
        exact fSum_ge21_family_neg_three_ne_two
          ha21 hp hq hpq hpo hqo hp5 hq5 hpkp hqkp hv

lemma fSum_mod16_five_omega_two_big_not_int
    {a p kp q kq : ℕ} (ha : 1 ≤ a) (ha5 : a ≡ 5 [MOD 16])
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (hbig : 3 ≤ kp ∨ 3 ≤ kq ∨ p ≡ 3 [MOD 4] ∨ q ≡ 3 [MOD 4]) :
    (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))).den ≠ 1 := by
  haveI := two_fact
  have hgt : 1 < fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) := by
    have := fSum_two_mul_two_prime_pows_gt_one ha hp hq hpkp hqkp
    linarith
  have hlt : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) < 3 :=
    fSum_two_mul_two_prime_pows_lt_three' hp hq hpq hpo hqo
  have hlt' : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) < 3 := by
    convert hlt using 1; ring
  have hv2m : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) ≤ -3 := by
    rw [padicValRat.mul
      (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
      (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
    have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
      Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpkp)
    have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
      Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqkp)
    rcases hbig with hkp3 | hkq3 | hp3 | hq3
    · have : padicValRat 2 (fSum (p ^ kp)) ≤ -2 :=
        v2_fSum_odd_prime_pow_exp_ge_three hp hpo hkp3
      linarith
    · have : padicValRat 2 (fSum (q ^ kq)) ≤ -2 :=
        v2_fSum_odd_prime_pow_exp_ge_three hq hqo hkq3
      linarith
    · have : padicValRat 2 (fSum (p ^ kp)) ≤ -2 :=
        v2_fSum_odd_prime_pow_mod4_three hp hpo hp3 hpkp
      linarith
    · have : padicValRat 2 (fSum (q ^ kq)) ≤ -2 :=
        v2_fSum_odd_prime_pow_mod4_three hq hqo hq3 hqkp
      linarith
  cases mod16_five_of_mod32 ha5 with
  | inl ha5_32 =>
    have hv2a : padicValRat 2 (fSum (2 ^ a)) = 4 :=
      v2_fSum_two_pow_mod32_five ha5_32
    have hv2prod : padicValRat 2
        (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) =
        4 + padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) := by
      rw [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
        (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
          (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))), hv2a]
    by_cases hstrict : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) ≤ -4
    · have : padicValRat 2
          (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) ≠ 1 := by
        linarith
      exact den_ne_one_of_lt_three_v2_ne_one hgt hlt' this
    · have hv2m_eq : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -3 := by
        omega
      have hne2 := fSum_mod16_five_omega_two_big_ne_two
        ha ha5 hp hq hpq hpo hqo hpkp hqkp hbig (Or.inr hv2m_eq)
      exact den_ne_one_of_mem_Ioo_ne_two hgt hlt' hne2
  | inr ha21 =>
    have ha21n : 21 ≤ a := by
      have : a % 32 = 21 := by simpa [Nat.ModEq] using ha21
      omega
    -- If either prime is 3 then already `fSum(2^a) * fSum(3) > 2`.
    have hp3or := odd_prime_eq_three_or_ge_five hp hpo
    have hq3or := odd_prime_eq_three_or_ge_five hq hqo
    have h27 := fSum_two_pow_ge_seven (by omega : 7 ≤ a)
    have h3gt : ∀ k : ℕ, 1 ≤ k → 2 < fSum (2 ^ a) * fSum (3 ^ k) := by
      intro k hk
      have h3 : fSum 3 ≤ fSum (3 ^ k) := fSum_le_of_exp_ge_one Nat.prime_three hk
      have heq2 : (8 : ℚ) / 5 * (5 / 4) = 2 := by norm_num
      have h3' : (5 : ℚ) / 4 ≤ fSum (3 ^ k) := by rwa [← fSum_three]
      have hmul : (8 : ℚ) / 5 * (5 / 4) < fSum (2 ^ a) * fSum (3 ^ k) :=
        mul_lt_mul h27 h3' (by norm_num) (by positivity)
      linarith [heq2]
    rcases hp3or with hp3 | hp5'
    · subst hp3
      have : 2 < fSum (2 ^ a) * (fSum (3 ^ kp) * fSum (q ^ kq)) := by
        have h1 := h3gt kp hpkp
        have h2 : 1 < fSum (q ^ kq) := fSum_gt_one_of_prime_pow hq hqkp
        nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
          fSum_pos (pow_ne_zero kp (by decide : (3 : ℕ) ≠ 0)),
          fSum_pos (pow_ne_zero kq hq.ne_zero)]
      exact den_ne_one_of_mem_Ioo_ne_two hgt hlt' (ne_of_gt this)
    · rcases hq3or with hq3 | hq5'
      · subst hq3
        have : 2 < fSum (2 ^ a) * (fSum (p ^ kp) * fSum (3 ^ kq)) := by
          have h1 := h3gt kq hqkp
          have h2 : 1 < fSum (p ^ kp) := fSum_gt_one_of_prime_pow hp hpkp
          have hswap : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (3 ^ kq)) =
              fSum (2 ^ a) * fSum (3 ^ kq) * fSum (p ^ kp) := by ring
          rw [hswap]
          nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
            fSum_pos (pow_ne_zero kq (by decide : (3 : ℕ) ≠ 0)),
            fSum_pos (pow_ne_zero kp hp.ne_zero)]
        exact den_ne_one_of_mem_Ioo_ne_two hgt hlt' (ne_of_gt this)
      · have hv2prod_eq : padicValRat 2
            (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) =
            padicValRat 2 (fSum (2 ^ a)) +
              padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) := by
          rw [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
            (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
              (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))]
        cases mod32_twentyone_of_mod64 ha21 with
        | inl ha21_64 =>
          have hv2a : padicValRat 2 (fSum (2 ^ a)) = 5 :=
            v2_fSum_two_pow_mod64_twentyone ha21_64
          by_cases h3 : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -3
          · have : padicValRat 2
                (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) ≠ 1 := by
              rw [hv2prod_eq, hv2a, h3]; norm_num
            exact den_ne_one_of_lt_three_v2_ne_one hgt hlt' this
          · by_cases hle5 : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) ≤ -5
            · have : padicValRat 2
                  (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) ≠ 1 := by
                rw [hv2prod_eq, hv2a]; linarith
              exact den_ne_one_of_lt_three_v2_ne_one hgt hlt' this
            · have hv4 : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -4 := by
                omega
              have hne2 := fSum_ge21_family_neg_four_ne_two
                ha21n hp hq hpq hpo hqo hp5' hq5' hpkp hqkp hv4
              exact den_ne_one_of_mem_Ioo_ne_two hgt hlt' hne2
        | inr ha53 =>
          cases mod64_fiftythree_of_mod128 ha53 with
          | inl ha53_128 =>
            have hv2a : padicValRat 2 (fSum (2 ^ a)) = 6 :=
              v2_fSum_two_pow_mod128_fiftythree ha53_128
            by_cases h4 : -4 ≤ padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq))
            · have : padicValRat 2
                  (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) ≠ 1 := by
                rw [hv2prod_eq, hv2a]; linarith
              exact den_ne_one_of_lt_three_v2_ne_one hgt hlt' this
            · by_cases hle6 : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) ≤ -6
              · have : padicValRat 2
                    (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) ≠ 1 := by
                  rw [hv2prod_eq, hv2a]; linarith
                exact den_ne_one_of_lt_three_v2_ne_one hgt hlt' this
              · have hv5 : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) = -5 := by
                  omega
                have hne2 := fSum_ge21_family_neg_five_ne_two
                  ha21n hp hq hpq hpo hqo hp5' hq5' hpkp hqkp hv5
                exact den_ne_one_of_mem_Ioo_ne_two hgt hlt' hne2
          | inr ha117 =>
            have hv2a : 7 ≤ padicValRat 2 (fSum (2 ^ a)) :=
              v2_fSum_two_pow_mod128_onehundredseventeen ha117
            by_cases h5 : -5 ≤ padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq))
            · have : padicValRat 2
                  (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) ≠ 1 := by
                rw [hv2prod_eq]; linarith
              exact den_ne_one_of_lt_three_v2_ne_one hgt hlt' this
            · have hne2 := fSum_ge21_family_neg_six_ne_two
                ha21n hp hq hpq hpo hqo hp5' hq5' hpkp hqkp
              exact den_ne_one_of_mem_Ioo_ne_two hgt hlt' hne2

lemma den_ne_one_of_lt_four_ne_two_ne_three {q : ℚ}
    (h1 : 1 < q) (h4 : q < 4) (hne2 : q ≠ 2) (hne3 : q ≠ 3) : q.den ≠ 1 := by
  intro hd
  have hq : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hd
  rw [← hq] at h1 h4 hne2 hne3
  have h1z : (1 : ℤ) < q.num := by exact_mod_cast h1
  have h4z : (q.num : ℤ) < 4 := by exact_mod_cast h4
  have hn2 : q.num ≠ 2 := by
    intro h; apply hne2; exact_mod_cast h
  have hn3 : q.num ≠ 3 := by
    intro h; apply hne3; exact_mod_cast h
  omega

lemma fSum_two_three_two_ge5_lt_four {a k p l q s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) :
    fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) < 4 := by
  have hA := fSum_two_pow_lt_13_8 a
  have hB := fSum_three_pow_lt_three_halves k
  have hC := fSum_prime_pow_lt_73_60 p l hp hp5
  have hD := fSum_prime_pow_lt_73_60 q s hq hq5
  have hAp : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hBp : 0 < fSum (3 ^ k) := fSum_pos (pow_ne_zero k (by decide : (3 : ℕ) ≠ 0))
  have hCp : 0 < fSum (p ^ l) := fSum_pos (pow_ne_zero l hp.ne_zero)
  have hDp : 0 < fSum (q ^ s) := fSum_pos (pow_ne_zero s hq.ne_zero)
  have hAB : fSum (2 ^ a) * fSum (3 ^ k) < (13 : ℚ) / 8 * (3 / 2) :=
    mul_lt_mul'' hA hB hAp.le hBp.le
  have hABC : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) <
      (13 : ℚ) / 8 * (3 / 2) * (73 / 60) :=
    mul_lt_mul'' hAB hC (mul_nonneg hAp.le hBp.le) hCp.le
  have hABCD : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) <
      (13 : ℚ) / 8 * (3 / 2) * (73 / 60) * (73 / 60) :=
    mul_lt_mul'' hABC hD
      (mul_nonneg (mul_nonneg hAp.le hBp.le) hCp.le) hDp.le
  have : (13 : ℚ) / 8 * (3 / 2) * (73 / 60) * (73 / 60) < 4 := by norm_num
  linarith

lemma fSum_four_one_mod4_sq_lt_three {a p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hp5 : 5 ≤ p) (hq13 : 13 ≤ q) (hr17 : 17 ≤ r) (hs29 : 29 ≤ s) :
    fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) * fSum (s ^ 2) < 3 := by
  have hA := fSum_two_pow_lt_13_8 a
  have hB : fSum (p ^ 2) ≤ fSum (5 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 5) hp hp5
  have hC : fSum (q ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
  have hD : fSum (r ^ 2) ≤ fSum (17 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 17) hr hr17
  have hE : fSum (s ^ 2) ≤ fSum (29 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 29) hs hs29
  have hprod : (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) *
      fSum (17 ^ 2) * fSum (29 ^ 2) < 3 := by
    rw [fSum_five_sq, fSum_thirteen_sq, fSum_seventeen_sq, fSum_twenty_nine_sq]
    norm_num
  have hAp : 0 < fSum (2 ^ a) := fSum_pos (pow_ne_zero a two_ne_zero)
  have hp2 : 0 < fSum (p ^ 2) := fSum_pos (pow_ne_zero 2 hp.ne_zero)
  have hq2 : 0 < fSum (q ^ 2) := fSum_pos (pow_ne_zero 2 hq.ne_zero)
  have hr2 : 0 < fSum (r ^ 2) := fSum_pos (pow_ne_zero 2 hr.ne_zero)
  have hs2 : 0 < fSum (s ^ 2) := fSum_pos (pow_ne_zero 2 hs.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ 2) < (13 : ℚ) / 8 * fSum (5 ^ 2) :=
    mul_lt_mul hA hB hp2 (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) <
      (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h1 hC hq2 (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) <
      (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) :=
    mul_lt_mul h2 hD hr2 (by
      exact mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  have h4 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) *
      fSum (s ^ 2) <
      (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) *
        fSum (29 ^ 2) :=
    mul_lt_mul h3 hE hs2 (by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
  exact h4.trans hprod

lemma no_five_three_one_mod4_sq_lt_two {a p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp13 : 13 ≤ p) (hq17 : 17 ≤ q) (hr29 : 29 ≤ r) :
    fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) < 2 := by
  have hA := fSum_two_pow_lt_13_8 a
  have hB : fSum (p ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hp hp13
  have hC : fSum (q ^ 2) ≤ fSum (17 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 17) hq hq17
  have hD : fSum (r ^ 2) ≤ fSum (29 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 29) hr hr29
  have hprod : (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (17 ^ 2) * fSum (29 ^ 2) < 2 := by
    rw [fSum_thirteen_sq, fSum_seventeen_sq, fSum_twenty_nine_sq]; norm_num
  have hp2 : 0 < fSum (p ^ 2) := fSum_pos (pow_ne_zero 2 hp.ne_zero)
  have hq2 : 0 < fSum (q ^ 2) := fSum_pos (pow_ne_zero 2 hq.ne_zero)
  have hr2 : 0 < fSum (r ^ 2) := fSum_pos (pow_ne_zero 2 hr.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ 2) < (13 : ℚ) / 8 * fSum (13 ^ 2) :=
    mul_lt_mul hA hB hp2 (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (17 ^ 2) :=
    mul_lt_mul h1 hC hq2 (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (17 ^ 2) * fSum (29 ^ 2) :=
    mul_lt_mul h2 hD hr2 (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
  exact h3.trans hprod

lemma ge21_has_three_gt_two {a k : ℕ} (ha : 21 ≤ a) (hk : 1 ≤ k) :
    2 < fSum (2 ^ a) * fSum (3 ^ k) := by
  have h27 := fSum_two_pow_ge_seven (by omega : 7 ≤ a)
  have h3 : fSum 3 ≤ fSum (3 ^ k) := fSum_le_of_exp_ge_one Nat.prime_three hk
  have heq2 : (8 : ℚ) / 5 * (5 / 4) = 2 := by norm_num
  have h3' : (5 : ℚ) / 4 ≤ fSum (3 ^ k) := by rwa [← fSum_three]
  have hmul : (8 : ℚ) / 5 * (5 / 4) < fSum (2 ^ a) * fSum (3 ^ k) :=
    mul_lt_mul h27 h3' (by norm_num) (by positivity)
  linarith [heq2]

lemma eq_four_prime_pows_of_card_eq_four {m : ℕ} (hm : m ≠ 0)
    (h : m.primeFactors.card = 4) :
    ∃ p q r s : ℕ, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      m.primeFactors = {p, q, r, s} ∧
      m = p ^ m.factorization p * q ^ m.factorization q *
        r ^ m.factorization r * s ^ m.factorization s := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hs⟩ :=
    Finset.card_eq_four.mp h
  have hp : p.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp)
  have hq : q.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp [hpq])
  have hr : r.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp [hpr, hqr])
  have hss : s.Prime :=
    prime_of_mem_primeFactors (by rw [hs]; simp [hps, hqs, hrs])
  refine ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hp, hq, hr, hss, hs, ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Finsupp.prod, Nat.support_factorization, hs]
  rw [prod_insert (by simp [hpq, hpr, hps]),
    prod_insert (by simp [hqr, hqs]),
    prod_insert (by simp [hrs]), prod_singleton]
  ac_rfl

lemma fs138_f9_f5sq_f13sq_lt_three :
    (13 : ℚ) / 8 * fSum (3 ^ 2) * fSum (5 ^ 2) * fSum (13 ^ 2) < 3 := by
  rw [fSum_nine, fSum_five_sq, fSum_thirteen_sq]; norm_num

lemma fSum_two_three_two_one_mod4_lt_three {a k p l q s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hq13 : 13 ≤ q)
    (hk2 : k ≤ 2) (hl2 : l ≤ 2) (hs2 : s ≤ 2) :
    fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) < 3 := by
  have hA := fSum_two_pow_lt_13_8 a
  have hB : fSum (3 ^ k) ≤ fSum (3 ^ 2) :=
    fSum_le_of_exp_ge Nat.prime_three hk2
  have hC : fSum (p ^ l) ≤ fSum (p ^ 2) :=
    fSum_le_of_exp_ge hp hl2
  have hD : fSum (q ^ s) ≤ fSum (q ^ 2) :=
    fSum_le_of_exp_ge hq hs2
  have hps : fSum (p ^ 2) ≤ fSum (5 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 5) hp hp5
  have hqs : fSum (q ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
  have hC' : fSum (p ^ l) ≤ fSum (5 ^ 2) := le_trans hC hps
  have hD' : fSum (q ^ s) ≤ fSum (13 ^ 2) := le_trans hD hqs
  have hprod := fs138_f9_f5sq_f13sq_lt_three
  have hp3 : 0 < fSum (3 ^ k) :=
    fSum_pos (pow_ne_zero k (by decide : (3 : ℕ) ≠ 0))
  have hpp : 0 < fSum (p ^ l) := fSum_pos (pow_ne_zero l hp.ne_zero)
  have hqq : 0 < fSum (q ^ s) := fSum_pos (pow_ne_zero s hq.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (3 ^ k) < (13 : ℚ) / 8 * fSum (3 ^ 2) :=
    mul_lt_mul hA hB hp3 (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) <
      (13 : ℚ) / 8 * fSum (3 ^ 2) * fSum (5 ^ 2) :=
    mul_lt_mul h1 hC' hpp (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (3 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) <
      (13 : ℚ) / 8 * fSum (3 ^ 2) * fSum (5 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h2 hD' hqq (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (3 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  exact h3.trans hprod

lemma ge21_five_thirteen_third_gt_two {a kp kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_thirteen_gt_two ha hpkp hqkp
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (13 : ℕ) ≠ 0)))
  nlinarith

lemma fs4017_f5_f29sq_f37sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (29 ^ 2) * fSum (37 ^ 2) < 2 := by
  rw [fSum_five, fSum_twenty_nine_sq, fSum_prime_sq (by decide : Nat.Prime 37)]
  norm_num

lemma ge21_five_one_ge29_third_lt_two {a q kq r kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hr : r.Prime)
    (hq29 : 29 ≤ q) (hr37 : 37 ≤ r)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (r ^ kr) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hC : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
  have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
  have hqs : fSum (q ^ 2) ≤ fSum (29 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 29) hq hq29
  have hrs : fSum (r ^ 2) ≤ fSum (37 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 37) hr hr37
  have hC' : fSum (q ^ kq) ≤ fSum (29 ^ 2) := le_trans hC hqs
  have hD' : fSum (r ^ kr) ≤ fSum (37 ^ 2) := le_trans hD hrs
  have hprod := fs4017_f5_f29sq_f37sq_lt_two
  have h5p : 0 < fSum (5 ^ 1) := fSum_pos (by decide)
  have hqpos : 0 < fSum (q ^ kq) := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos : 0 < fSum (r ^ kr) := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (5 ^ 1) < (4017 : ℚ) / 2500 * fSum 5 := by
    rw [pow_one]
    exact mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
  have h2 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * fSum 5 * fSum (29 ^ 2) :=
    mul_lt_mul h1 hC' hqpos (mul_nonneg (by norm_num)
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
  have h3 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * fSum 5 * fSum (29 ^ 2) * fSum (37 ^ 2) :=
    mul_lt_mul h2 hD' hrpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0))).le)
  exact h3.trans hprod

lemma no_five_four_sq_lt_three {a p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hp13 : 13 ≤ p) (hq13 : 13 ≤ q) (hr13 : 13 ≤ r) (hs13 : 13 ≤ s) :
    fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) * fSum (s ^ 2) < 3 := by
  have hA := fSum_two_pow_lt_13_8 a
  have hB : fSum (p ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hp hp13
  have hC : fSum (q ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
  have hD : fSum (r ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hr hr13
  have hE : fSum (s ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hs hs13
  have hprod : (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (13 ^ 2) *
      fSum (13 ^ 2) * fSum (13 ^ 2) < 3 := by
    rw [fSum_thirteen_sq]; norm_num
  have hp2 : 0 < fSum (p ^ 2) := fSum_pos (pow_ne_zero 2 hp.ne_zero)
  have hq2 : 0 < fSum (q ^ 2) := fSum_pos (pow_ne_zero 2 hq.ne_zero)
  have hr2 : 0 < fSum (r ^ 2) := fSum_pos (pow_ne_zero 2 hr.ne_zero)
  have hs2 : 0 < fSum (s ^ 2) := fSum_pos (pow_ne_zero 2 hs.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ 2) < (13 : ℚ) / 8 * fSum (13 ^ 2) :=
    mul_lt_mul hA hB hp2 (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h1 hC hq2 (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (13 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h2 hD hr2 (by
      exact mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  have h4 : fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) *
      fSum (s ^ 2) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (13 ^ 2) * fSum (13 ^ 2) *
        fSum (13 ^ 2) :=
    mul_lt_mul h3 hE hs2 (by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  exact h4.trans hprod

lemma three_one_mod4_sorted_bounds {q r s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4]) (hs1 : s ≡ 1 [MOD 4])
    (hq5ne : q ≠ 5) (hr5ne : r ≠ 5) (hs5ne : s ≠ 5)
    (hle1 : q ≤ r) (hle2 : q ≤ s) (hle3 : r ≤ s) :
    13 ≤ q ∧ 17 ≤ r ∧ 29 ≤ s := by
  have hq13 : 13 ≤ q := by
    rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
    · exact (hq5ne h5).elim
    · exact h13.symm ▸ le_rfl
    · omega
    · omega
  have hr17 : 17 ≤ r := by
    have hrne13 : r ≠ 13 := by
      intro h
      have : q = 13 := by
        have : q ≤ 13 := h ▸ hle1
        omega
      exact hqr (this.trans h.symm)
    rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
    · exact (hr5ne h5).elim
    · exact (hrne13 h13).elim
    · exact h17.symm ▸ le_rfl
    · omega
  have hs29 : 29 ≤ s := by
    have hsne13 : s ≠ 13 := by
      intro h
      have : q = 13 := by
        have : q ≤ 13 := h ▸ hle2
        omega
      exact hqs (this.trans h.symm)
    have hsne17 : s ≠ 17 := by
      intro h
      have : r = 17 := by
        have : r ≤ 17 := h ▸ hle3
        omega
      exact hrs (this.trans h.symm)
    rcases prime_one_mod_four_cases hs hs1 with h5 | h13 | h17 | hge
    · exact (hs5ne h5).elim
    · exact (hsne13 h13).elim
    · exact (hsne17 h17).elim
    · exact hge
  exact ⟨hq13, hr17, hs29⟩

lemma fSum_five_three_sorted_lt_three {a q r s kq kr ks : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4]) (hs1 : s ≡ 1 [MOD 4])
    (hq5ne : q ≠ 5) (hr5ne : r ≠ 5) (hs5ne : s ≠ 5)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) (hks : ks = 1 ∨ ks = 2)
    (hle1 : q ≤ r) (hle2 : r ≤ s) :
    fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) < 3 := by
  have hle_qs : q ≤ s := le_trans hle1 hle2
  obtain ⟨hq13, hr17, hs29⟩ :=
    three_one_mod4_sorted_bounds hq hr hs hqr hqs hrs hq1 hr1 hs1
      hq5ne hr5ne hs5ne hle1 hle_qs hle2
  have hqle : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
  have hrle : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
  have hsle : fSum (s ^ ks) ≤ fSum (s ^ 2) := fSum_le_sq_of_exp_le_two hs hks
  have hqs' : fSum (q ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
  have hrs' : fSum (r ^ 2) ≤ fSum (17 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 17) hr hr17
  have hss' : fSum (s ^ 2) ≤ fSum (29 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 29) hs hs29
  have hq2 : 0 < fSum (q ^ kq) := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hr2 : 0 < fSum (r ^ kr) := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hs2 : 0 < fSum (s ^ ks) := fSum_pos (pow_ne_zero ks hs.ne_zero)
  have h5p : 0 < fSum (5 ^ 2) :=
    fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))
  have hC : fSum (q ^ kq) ≤ fSum (13 ^ 2) := le_trans hqle hqs'
  have hD : fSum (r ^ kr) ≤ fSum (17 ^ 2) := le_trans hrle hrs'
  have hE : fSum (s ^ ks) ≤ fSum (29 ^ 2) := le_trans hsle hss'
  have hA := fSum_two_pow_lt_13_8 a
  have h1 : fSum (2 ^ a) * fSum (5 ^ 2) < (13 : ℚ) / 8 * fSum (5 ^ 2) :=
    mul_lt_mul_of_pos_right hA h5p
  have h2 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) <
      (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h1 hC hq2 (mul_nonneg (by norm_num) h5p.le)
  have h3 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) <
      (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) :=
    mul_lt_mul h2 hD hr2 (mul_nonneg (mul_nonneg (by norm_num) h5p.le)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  have h4 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) <
      (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) *
        fSum (29 ^ 2) :=
    mul_lt_mul h3 hE hs2 (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h5p.le)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
  have hprod : (13 : ℚ) / 8 * fSum (5 ^ 2) * fSum (13 ^ 2) *
      fSum (17 ^ 2) * fSum (29 ^ 2) < 3 := by
    rw [fSum_five_sq, fSum_thirteen_sq, fSum_seventeen_sq, fSum_twenty_nine_sq]
    norm_num
  exact h4.trans hprod

lemma fSum_five_three_one_mod4_any_lt_three {a q r s kq kr ks : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4]) (hs1 : s ≡ 1 [MOD 4])
    (hq5ne : q ≠ 5) (hr5ne : r ≠ 5) (hs5ne : s ≠ 5)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) (hks : ks = 1 ∨ ks = 2) :
    fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) < 3 := by
  rcases le_total q r with hqr_le | hrq_le
  · rcases le_total r s with hrs_le | hsr_le
    · exact fSum_five_three_sorted_lt_three hq hr hs hqr hqs hrs hq1 hr1 hs1
        hq5ne hr5ne hs5ne hkq hkr hks hqr_le hrs_le
    · rcases le_total q s with hqs_le | hsq_le
      · have hswap :
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
              fSum (s ^ ks) =
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (s ^ ks) *
              fSum (r ^ kr) := by ring
        rw [hswap]
        exact fSum_five_three_sorted_lt_three hq hs hr hqs hqr hrs.symm
          hq1 hs1 hr1 hq5ne hs5ne hr5ne hkq hks hkr hqs_le hsr_le
      · have hswap :
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
              fSum (s ^ ks) =
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (s ^ ks) * fSum (q ^ kq) *
              fSum (r ^ kr) := by ring
        rw [hswap]
        exact fSum_five_three_sorted_lt_three hs hq hr hqs.symm hrs.symm hqr
          hs1 hq1 hr1 hs5ne hq5ne hr5ne hks hkq hkr hsq_le hqr_le
  · rcases le_total q s with hqs_le | hsq_le
    · have hswap :
          fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
            fSum (s ^ ks) =
          fSum (2 ^ a) * fSum (5 ^ 2) * fSum (r ^ kr) * fSum (q ^ kq) *
            fSum (s ^ ks) := by ring
      rw [hswap]
      exact fSum_five_three_sorted_lt_three hr hq hs hqr.symm hrs hqs
        hr1 hq1 hs1 hr5ne hq5ne hs5ne hkr hkq hks hrq_le hqs_le
    · rcases le_total r s with hrs_le | hsr_le
      · have hswap :
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
              fSum (s ^ ks) =
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (r ^ kr) * fSum (s ^ ks) *
              fSum (q ^ kq) := by ring
        rw [hswap]
        exact fSum_five_three_sorted_lt_three hr hs hq hrs hqr.symm hqs.symm
          hr1 hs1 hq1 hr5ne hs5ne hq5ne hkr hks hkq hrs_le hsq_le
      · have hswap :
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
              fSum (s ^ ks) =
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (s ^ ks) * fSum (r ^ kr) *
              fSum (q ^ kq) := by ring
        rw [hswap]
        exact fSum_five_three_sorted_lt_three hs hr hq hrs.symm hqs.symm hqr.symm
          hs1 hr1 hq1 hs5ne hr5ne hq5ne hks hkr hkq hsr_le hrq_le

lemma mul_le_of_second {A B C D E B' : ℚ}
    (hB : B ≤ B') (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    A * B * C * D * E ≤ A * B' * C * D * E := by
  have h1 : A * B ≤ A * B' := mul_le_mul_of_nonneg_left hB hA
  have h2 : A * B * C ≤ A * B' * C := mul_le_mul_of_nonneg_right h1 hC
  have h3 : A * B * C * D ≤ A * B' * C * D := mul_le_mul_of_nonneg_right h2 hD
  exact mul_le_mul_of_nonneg_right h3 hE

lemma mul_le_of_last4 {A B C D E B' C' D' E' : ℚ}
    (hB : B ≤ B') (hC : C ≤ C') (hD : D ≤ D') (hE : E ≤ E')
    (hA : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) (hE0 : 0 ≤ E)
    (hB' : 0 ≤ B') (hC' : 0 ≤ C') (hD' : 0 ≤ D') :
    A * B * C * D * E ≤ A * B' * C' * D' * E' := by
  have h1 : A * B ≤ A * B' := mul_le_mul_of_nonneg_left hB hA
  have h2 : A * B * C ≤ A * B' * C' :=
    mul_le_mul h1 hC hC0 (mul_nonneg hA hB')
  have h3 : A * B * C * D ≤ A * B' * C' * D' :=
    mul_le_mul h2 hD hD0 (mul_nonneg (mul_nonneg hA hB') hC')
  exact mul_le_mul h3 hE hE0 (mul_nonneg (mul_nonneg (mul_nonneg hA hB') hC') hD')

lemma fSum_four_one_mod4_any_lt_three {a p q r s kp kq kr ks : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hp1 : p ≡ 1 [MOD 4]) (hq1 : q ≡ 1 [MOD 4])
    (hr1 : r ≡ 1 [MOD 4]) (hs1 : s ≡ 1 [MOD 4])
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2)
    (hkr : kr = 1 ∨ kr = 2) (hks : ks = 1 ∨ ks = 2) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) < 3 := by
  have hple : fSum (p ^ kp) ≤ fSum (p ^ 2) := fSum_le_sq_of_exp_le_two hp hkp
  have hqle : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
  have hrle : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
  have hsle : fSum (s ^ ks) ≤ fSum (s ^ 2) := fSum_le_sq_of_exp_le_two hs hks
  have hp5' : 5 ≤ p := five_le_of_mod4_one hp hp1
  have hq5' : 5 ≤ q := five_le_of_mod4_one hq hq1
  have hr5' : 5 ≤ r := five_le_of_mod4_one hr hr1
  have hs5' : 5 ≤ s := five_le_of_mod4_one hs hs1
  by_cases hhas5 : p = 5 ∨ q = 5 ∨ r = 5 ∨ s = 5
  · rcases hhas5 with hp5 | hq5 | hr5 | hs5
    · subst hp5
      have : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
          fSum (s ^ ks) ≤
          fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) *
            fSum (s ^ ks) :=
        mul_le_of_second hple
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kq hq.ne_zero)).le
          (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
          (fSum_pos (pow_ne_zero ks hs.ne_zero)).le
      exact this.trans_lt
        (fSum_five_three_one_mod4_any_lt_three hq hr hs hqr hqs hrs
          hq1 hr1 hs1 hpq.symm hpr.symm hps.symm hkq hkr hks)
    · subst hq5
      have hswap :
          fSum (2 ^ a) * fSum (p ^ kp) * fSum (5 ^ kq) * fSum (r ^ kr) *
            fSum (s ^ ks) =
          fSum (2 ^ a) * fSum (5 ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) *
            fSum (s ^ ks) := by ring
      rw [hswap]
      have : fSum (2 ^ a) * fSum (5 ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) *
          fSum (s ^ ks) ≤
          fSum (2 ^ a) * fSum (5 ^ 2) * fSum (p ^ kp) * fSum (r ^ kr) *
            fSum (s ^ ks) :=
        mul_le_of_second hqle
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kp hp.ne_zero)).le
          (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
          (fSum_pos (pow_ne_zero ks hs.ne_zero)).le
      exact this.trans_lt
        (fSum_five_three_one_mod4_any_lt_three hp hr hs hpr hps hrs
          hp1 hr1 hs1 hpq hqr.symm hqs.symm hkp hkr hks)
    · subst hr5
      have hswap :
          fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (5 ^ kr) *
            fSum (s ^ ks) =
          fSum (2 ^ a) * fSum (5 ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) *
            fSum (s ^ ks) := by ring
      rw [hswap]
      have : fSum (2 ^ a) * fSum (5 ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) *
          fSum (s ^ ks) ≤
          fSum (2 ^ a) * fSum (5 ^ 2) * fSum (p ^ kp) * fSum (q ^ kq) *
            fSum (s ^ ks) :=
        mul_le_of_second hrle
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kp hp.ne_zero)).le
          (fSum_pos (pow_ne_zero kq hq.ne_zero)).le
          (fSum_pos (pow_ne_zero ks hs.ne_zero)).le
      exact this.trans_lt
        (fSum_five_three_one_mod4_any_lt_three hp hq hs hpq hps hqs
          hp1 hq1 hs1 hpr hqr hrs.symm hkp hkq hks)
    · subst hs5
      have hswap :
          fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
            fSum (5 ^ ks) =
          fSum (2 ^ a) * fSum (5 ^ ks) * fSum (p ^ kp) * fSum (q ^ kq) *
            fSum (r ^ kr) := by ring
      rw [hswap]
      have : fSum (2 ^ a) * fSum (5 ^ ks) * fSum (p ^ kp) * fSum (q ^ kq) *
          fSum (r ^ kr) ≤
          fSum (2 ^ a) * fSum (5 ^ 2) * fSum (p ^ kp) * fSum (q ^ kq) *
            fSum (r ^ kr) :=
        mul_le_of_second hsle
          (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (pow_ne_zero kp hp.ne_zero)).le
          (fSum_pos (pow_ne_zero kq hq.ne_zero)).le
          (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
      exact this.trans_lt
        (fSum_five_three_one_mod4_any_lt_three hp hq hr hpq hpr hqr
          hp1 hq1 hr1 hps hqs hrs hkp hkq hkr)
  · have hp13 : 13 ≤ p := by
      rcases prime_one_mod_four_cases hp hp1 with h5 | h13 | h17 | hge
      · exact (hhas5 (Or.inl h5)).elim
      · exact h13.symm ▸ le_rfl
      · omega
      · omega
    have hq13 : 13 ≤ q := by
      rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
      · exact (hhas5 (Or.inr (Or.inl h5))).elim
      · exact h13.symm ▸ le_rfl
      · omega
      · omega
    have hr13 : 13 ≤ r := by
      rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
      · exact (hhas5 (Or.inr (Or.inr (Or.inl h5)))).elim
      · exact h13.symm ▸ le_rfl
      · omega
      · omega
    have hs13 : 13 ≤ s := by
      rcases prime_one_mod_four_cases hs hs1 with h5 | h13 | h17 | hge
      · exact (hhas5 (Or.inr (Or.inr (Or.inr h5)))).elim
      · exact h13.symm ▸ le_rfl
      · omega
      · omega
    have : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
        fSum (s ^ ks) ≤
        fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) *
          fSum (s ^ 2) :=
      mul_le_of_last4 hple hqle hrle hsle
        (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (pow_ne_zero kp hp.ne_zero)).le
        (fSum_pos (pow_ne_zero kq hq.ne_zero)).le
        (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
        (fSum_pos (pow_ne_zero ks hs.ne_zero)).le
        (fSum_pos (pow_ne_zero 2 hp.ne_zero)).le
        (fSum_pos (pow_ne_zero 2 hq.ne_zero)).le
        (fSum_pos (pow_ne_zero 2 hr.ne_zero)).le
    exact this.trans_lt
      (no_five_four_sq_lt_three hp hq hr hs hp13 hq13 hr13 hs13)

lemma fSum_two_pow_ge_fourteen {a : ℕ} (ha : 14 ≤ a) :
    fSum (2 ^ 14) ≤ fSum (2 ^ a) := by
  cases Nat.lt_or_eq_of_le ha with
  | inl h => exact (fSum_strict_mono_two h).le
  | inr h => rw [h]

lemma fSum_two_pow_fourteen_gt_4016_2500 :
    (4016 : ℚ) / 2500 < fSum (2 ^ 14) := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight]
  norm_num

lemma fSum_two_pow_ge14_gt_4016_2500 {a : ℕ} (ha : 14 ≤ a) :
    (4016 : ℚ) / 2500 < fSum (2 ^ a) :=
  lt_of_lt_of_le fSum_two_pow_fourteen_gt_4016_2500 (fSum_two_pow_ge_fourteen ha)

lemma two_pow_sub_one_mul_65536 {k : ℕ} (hk : 15 ≤ k) :
    (2 ^ (k + 1) - 1) * 65536 ≥ 2 ^ (k + 1) * 65535 := by
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hge : (2 : ℕ) ^ 16 ≤ 2 ^ (k + 1) :=
    pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega : 16 ≤ k + 1)
  have h65536 : (65536 : ℕ) = 2 ^ 16 := by decide
  zify [hle]
  nlinarith

lemma mersenne_recip_le_scaled_of_ge_fifteen {k : ℕ} (hk : 15 ≤ k) :
    (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≤
      (65536 / 65535 : ℚ) * (1 / 2 : ℚ) ^ (k + 1) := by
  have hN := two_pow_sub_one_mul_65536 hk
  have hdenpos : (0 : ℚ) < ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero k))
  have hcast : ((2 ^ (k + 1) - 1 : ℕ) : ℚ) * (65536 : ℚ) ≥
      ((2 ^ (k + 1) : ℕ) : ℚ) * (65535 : ℚ) := by exact_mod_cast hN
  have h2eq : ((2 ^ (k + 1) : ℕ) : ℚ) = (2 : ℚ) ^ (k + 1) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [h2eq] at hcast
  have h2pos : (0 : ℚ) < (2 : ℚ) ^ (k + 1) := by positivity
  have hhalf : (1 / 2 : ℚ) ^ (k + 1) = 1 / (2 : ℚ) ^ (k + 1) := by
    rw [div_pow, one_pow]
  rw [hhalf, show (65536 / 65535 : ℚ) * (1 / (2 : ℚ) ^ (k + 1)) =
      65536 / (65535 * (2 : ℚ) ^ (k + 1)) by field_simp]
  rw [div_le_div_iff₀ hdenpos (mul_pos (by norm_num) h2pos)]
  linarith

lemma sum_Ico_mersenne_ge_fifteen_lt_tight (b : ℕ) :
    ∑ k ∈ Ico 15 b, (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) <
      (2 : ℚ) / 65535 := by
  have hle :
      ∑ k ∈ Ico 15 b, (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) ≤
        ∑ k ∈ Ico 15 b, (65536 / 65535 : ℚ) * (1 / 2 : ℚ) ^ (k + 1) := by
    refine sum_le_sum fun k hk => ?_
    have hk15 : 15 ≤ k := (mem_Ico.mp hk).1
    exact mersenne_recip_le_scaled_of_ge_fifteen hk15
  have hfac :
      ∑ k ∈ Ico 15 b, (65536 / 65535 : ℚ) * (1 / 2 : ℚ) ^ (k + 1) =
        (65536 / 65535 : ℚ) * ∑ k ∈ Ico 15 b, (1 / 2 : ℚ) ^ (k + 1) :=
    (mul_sum _ _ _).symm
  have hgeom : ∑ k ∈ Ico 15 b, (1 / 2 : ℚ) ^ (k + 1) < (1 : ℚ) / 32768 := by
    rw [sum_Ico_eq_sum_range]
    have hshift :
        ∑ i ∈ range (b - 15), (1 / 2 : ℚ) ^ (15 + i + 1) =
          (1 / 2 : ℚ) ^ 16 * ∑ i ∈ range (b - 15), (1 / 2 : ℚ) ^ i := by
      refine (sum_congr rfl fun i _ => ?_).trans (mul_sum _ _ _).symm
      rw [show 15 + i + 1 = 16 + i by omega, pow_add]
    rw [hshift]
    have hgs := geom_sum_half_lt (b - 15)
    have : (1 / 2 : ℚ) ^ 16 = 1 / 65536 := by norm_num
    nlinarith
  have : (65536 / 65535 : ℚ) * ((1 : ℚ) / 32768) = 2 / 65535 := by norm_num
  linarith

lemma fSum_two_pow_fourteen_add_tight_tail_lt :
    fSum (2 ^ 14) + (2 : ℚ) / 65535 < (16067 : ℚ) / 10000 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight]
  norm_num

lemma fSum_two_pow_lt_16067_10000 (a : ℕ) :
    fSum (2 ^ a) < (16067 : ℚ) / 10000 := by
  cases lt_or_ge a 15 with
  | inl hlt =>
    have hle : fSum (2 ^ a) ≤ fSum (2 ^ 14) := by
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with
      | inl h => exact (fSum_strict_mono_two h).le
      | inr h => rw [h]
    have : fSum (2 ^ 14) < (16067 : ℚ) / 10000 := by
      have hpos : (0 : ℚ) < 2 / 65535 := by norm_num
      linarith [fSum_two_pow_fourteen_add_tight_tail_lt]
    exact lt_of_le_of_lt hle this
  | inr hge =>
    have h15 : 15 ≤ a + 1 := by omega
    have hsplit :
        fSum (2 ^ a) =
          fSum (2 ^ 14) +
            ∑ k ∈ Ico 15 (a + 1), (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ) := by
      rw [fSum_two_pow_eq, fSum_two_pow_eq]
      simpa using
        (sum_range_add_sum_Ico
          (fun k => (1 : ℚ) / ((2 ^ (k + 1) - 1 : ℕ) : ℚ)) h15).symm
    have htail := sum_Ico_mersenne_ge_fifteen_lt_tight (a + 1)
    linarith [fSum_two_pow_fourteen_add_tight_tail_lt]

lemma prime_one_mod4_ge29_small_cases {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (h29 : 29 ≤ q) :
    q = 29 ∨ q = 37 ∨ q = 41 ∨ q = 53 ∨ q = 61 ∨ q = 73 ∨ q = 89 ∨ 97 ≤ q := by
  by_cases h97 : 97 ≤ q
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h97))))))
  · have : q < 97 := by omega
    interval_cases q
    all_goals
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      | exact absurd hq (by decide)
      | simp [Nat.ModEq] at h1

lemma prime_one_mod4_ge97_small_cases {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (h97 : 97 ≤ q) :
    q = 97 ∨ q = 101 ∨ q = 109 ∨ q = 113 ∨ 137 ≤ q := by
  by_cases h137 : 137 ≤ q
  · exact Or.inr (Or.inr (Or.inr (Or.inr h137)))
  · have : q < 137 := by omega
    interval_cases q
    all_goals
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact absurd hq (by decide)
      | simp [Nat.ModEq] at h1

lemma prime_one_mod4_ge29_mid_cases {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (h29 : 29 ≤ q) :
    q = 29 ∨ 37 ≤ q := by
  cases lt_or_ge q 37 with
  | inl hlt =>
    have : q < 37 := hlt
    interval_cases q
    · exact Or.inl rfl
    all_goals
      first
      | exact absurd hq (by decide)
      | simp [Nat.ModEq] at h1
  | inr hge => exact Or.inr hge

lemma four016_f5_f17_f89_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum 89 := by
  rw [fSum_five, fSum_seventeen, fSum_prime (by decide : Nat.Prime 89)]
  norm_num

lemma four017_f5_f17sq_f137sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (17 ^ 2) * fSum (137 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen_sq, fSum_prime_sq (by decide : Nat.Prime 137)]
  norm_num

lemma four016_f5_f17sq_f113_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum (17 ^ 2) * fSum 113 := by
  rw [fSum_five, fSum_seventeen_sq, fSum_prime (by decide : Nat.Prime 113)]
  norm_num

lemma four017_f5_f17_f97sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (97 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen, fSum_prime_sq (by decide : Nat.Prime 97)]
  norm_num

lemma four017_f5_f17_f101sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (101 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen, fSum_prime_sq (by decide : Nat.Prime 101)]
  norm_num

lemma four017_f5_f17_f109sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (109 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen, fSum_prime_sq (by decide : Nat.Prime 109)]
  norm_num

lemma four017_f5_f17_f113sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (113 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen, fSum_prime_sq (by decide : Nat.Prime 113)]
  norm_num

lemma four016_f5sq_f29_f197_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 29 * ((197 : ℚ) + 2) / (197 + 1) := by
  rw [fSum_five_sq, fSum_twenty_nine]
  norm_num

lemma four017_f5sq_f29_f229sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 29 *
      (1 + 1 / ((229 : ℚ) + 1) + 1 / ((229 : ℚ) ^ 2 + 229 + 1)) < 2 := by
  rw [fSum_five_sq, fSum_twenty_nine]
  norm_num

lemma f14_f5sq_f29sq_f269_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (29 ^ 2) *
      ((269 : ℚ) + 2) / (269 + 1) := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_sq, fSum_twenty_nine_sq]
  norm_num

lemma fs16067_f5sq_f29sq_f277sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 2) * fSum (29 ^ 2) *
      (1 + 1 / ((277 : ℚ) + 1) + 1 / ((277 : ℚ) ^ 2 + 277 + 1)) < 2 := by
  rw [fSum_five_sq, fSum_twenty_nine_sq]
  norm_num

lemma ge14_mul3_gt_two {n : ℕ} {A B C : ℚ}
    (hn : 14 ≤ n) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hth : 2 < (4016 : ℚ) / 2500 * A * B * C) :
    2 < fSum (2 ^ n) * A * B * C := by
  have hlo := fSum_two_pow_ge14_gt_4016_2500 hn
  have : (4016 : ℚ) / 2500 * A * B * C < fSum (2 ^ n) * A * B * C :=
    mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hlo hA) hB) hC
  exact hth.trans this

lemma fSum_prime_anti {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≤ q) :
    fSum q ≤ fSum p := by
  rw [fSum_prime hp, fSum_prime hq]
  have hp0 : (0 : ℚ) < (p : ℚ) + 1 := by positivity
  have hpq : (p : ℚ) ≤ (q : ℚ) := by exact_mod_cast h
  have hle : (p : ℚ) + 1 ≤ (q : ℚ) + 1 := by linarith [hpq]
  have : (1 : ℚ) / ((q : ℚ) + 1) ≤ 1 / ((p : ℚ) + 1) :=
    one_div_le_one_div_of_le hp0 hle
  have hpform : ((p : ℚ) + 2) / ((p : ℚ) + 1) = 1 + 1 / ((p : ℚ) + 1) := by
    field_simp; ring
  have hqform : ((q : ℚ) + 2) / ((q : ℚ) + 1) = 1 + 1 / ((q : ℚ) + 1) := by
    field_simp; ring
  rw [hpform, hqform]
  linarith

lemma ge21_five_one_seventeen_le89_gt_two {a r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hr89 : r ≤ 89) (hkr : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ 1) * fSum (r ^ kr) := by
  have h89P : Nat.Prime 89 := by decide
  have hrle : fSum r ≤ fSum (r ^ kr) := fSum_le_of_exp_ge_one hr hkr
  have hanti : fSum 89 ≤ fSum r := fSum_prime_anti hr h89P hr89
  have hC : fSum 89 ≤ fSum (r ^ kr) := le_trans hanti hrle
  have hmin :=
    ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 17) (C := fSum 89)
      (by omega) (fSum_pos (by decide)) (fSum_pos (by decide))
      (fSum_pos (by decide)) four016_f5_f17_f89_gt_two
  have hmono := mul3_gt_of le_rfl le_rfl hC
    (fSum_pos (by decide : (17 : ℕ) ≠ 0)).le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
    (fSum_pos (by decide : (89 : ℕ) ≠ 0)).le
    (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      (fSum_pos (by decide : (17 : ℕ) ≠ 0)).le)
  -- hmin : 2 < fSum(2^a) * f5 * f17 * f89
  -- need fSum(2^a) * f5^1 * f17^1 * f(r^kr)
  rw [pow_one, pow_one]
  exact lt_of_lt_of_le hmin hmono

lemma ge21_five_two_seventeen_third_gt_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hqkp : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum (17 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_two_seventeen_gt_two ha hqkp
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum (17 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0)))
  nlinarith

lemma ge21_five_one_seventeen_ge137_lt_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hr137 : 137 ≤ r) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hC : fSum (17 ^ kq) ≤ fSum (17 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 17) hkq
  have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
  have hrs : fSum (r ^ 2) ≤ fSum (137 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 137) hr hr137
  have hD' : fSum (r ^ kr) ≤ fSum (137 ^ 2) := le_trans hD hrs
  have hprod := four017_f5_f17sq_f137sq_lt_two
  have h5p : 0 < fSum (5 ^ 1) := fSum_pos (by decide)
  have h17p : 0 < fSum (17 ^ kq) :=
    fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))
  have hrpos : 0 < fSum (r ^ kr) := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (5 ^ 1) < (4017 : ℚ) / 2500 * fSum 5 := by
    rw [pow_one]
    exact mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
  have h2 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) <
      (4017 : ℚ) / 2500 * fSum 5 * fSum (17 ^ 2) :=
    mul_lt_mul h1 hC h17p (mul_nonneg (by norm_num)
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
  have h3 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * fSum 5 * fSum (17 ^ 2) * fSum (137 ^ 2) :=
    mul_lt_mul h2 hD' hrpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
  exact h3.trans hprod

lemma fSum_prime_as_one_add {p : ℕ} (hp : p.Prime) :
    fSum p = 1 + 1 / ((p : ℚ) + 1) := by
  rw [fSum_prime hp]
  field_simp
  ring

lemma fSum_prime_ge_form {p n : ℕ} (hp : p.Prime) (h : p ≤ n) :
    ((n : ℚ) + 2) / (n + 1) ≤ fSum p := by
  have hpform := fSum_prime_as_one_add hp
  have hnform : ((n : ℚ) + 2) / (n + 1) = 1 + 1 / ((n : ℚ) + 1) := by
    field_simp; ring
  have hp0 : (0 : ℚ) < (p : ℚ) + 1 := by positivity
  have hle : (p : ℚ) + 1 ≤ (n : ℚ) + 1 := by
    linarith [show (p : ℚ) ≤ n by exact_mod_cast h]
  have : (1 : ℚ) / ((n : ℚ) + 1) ≤ 1 / ((p : ℚ) + 1) :=
    one_div_le_one_div_of_le hp0 hle
  rw [hpform, hnform]
  linarith

lemma fSum_prime_sq_le_form {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (h : n ≤ p) :
    fSum (p ^ 2) ≤
      1 + 1 / ((n : ℚ) + 1) + 1 / ((n : ℚ) ^ 2 + n + 1) := by
  rw [fSum_prime_sq hp]
  have hpq : (n : ℚ) ≤ p := by exact_mod_cast h
  have hn0 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have h1 : (n : ℚ) + 1 ≤ (p : ℚ) + 1 := by linarith
  have : (1 : ℚ) / ((p : ℚ) + 1) ≤ 1 / ((n : ℚ) + 1) :=
    one_div_le_one_div_of_le hn0 h1
  have hsq : (n : ℚ) ^ 2 + n + 1 ≤ (p : ℚ) ^ 2 + p + 1 := by
    nlinarith [sq_nonneg (n : ℚ), sq_nonneg (p : ℚ)]
  have hn2 : (0 : ℚ) < (n : ℚ) ^ 2 + n + 1 := by positivity
  have : (1 : ℚ) / ((p : ℚ) ^ 2 + p + 1) ≤ 1 / ((n : ℚ) ^ 2 + n + 1) :=
    one_div_le_one_div_of_le hn2 hsq
  linarith

lemma fSum_thirty_seven : fSum 37 = (39 : ℚ) / 38 := by
  rw [fSum_prime (by decide : Nat.Prime 37)]; norm_num

lemma fSum_forty_one : fSum 41 = (43 : ℚ) / 42 := by
  rw [fSum_prime (by decide : Nat.Prime 41)]; norm_num

lemma fSum_fifty_three : fSum 53 = (55 : ℚ) / 54 := by
  rw [fSum_prime (by decide : Nat.Prime 53)]; norm_num

lemma fSum_sixty_one : fSum 61 = (63 : ℚ) / 62 := by
  rw [fSum_prime (by decide : Nat.Prime 61)]; norm_num

lemma fSum_seventy_three : fSum 73 = (75 : ℚ) / 74 := by
  rw [fSum_prime (by decide : Nat.Prime 73)]; norm_num

lemma fSum_thirty_seven_sq : fSum (37 ^ 2) =
    (1 : ℚ) + 1 / (37 + 1) + 1 / (37 ^ 2 + 37 + 1) :=
  fSum_prime_sq (by decide : Nat.Prime 37)

lemma fSum_forty_one_sq : fSum (41 ^ 2) =
    (1 : ℚ) + 1 / (41 + 1) + 1 / (41 ^ 2 + 41 + 1) :=
  fSum_prime_sq (by decide : Nat.Prime 41)

lemma fSum_fifty_three_sq : fSum (53 ^ 2) =
    (1 : ℚ) + 1 / (53 + 1) + 1 / (53 ^ 2 + 53 + 1) :=
  fSum_prime_sq (by decide : Nat.Prime 53)

lemma prime_one_mod4_ge29_four_cases {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (h29 : 29 ≤ q) :
    q = 29 ∨ q = 37 ∨ q = 41 ∨ 53 ≤ q := by
  by_cases h53 : 53 ≤ q
  · exact Or.inr (Or.inr (Or.inr h53))
  · have : q < 53 := by omega
    interval_cases q
    all_goals
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact absurd hq (by decide)
      | simp [Nat.ModEq] at h1

lemma prime_one_mod4_le197_or_ge229 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) :
    r ≤ 197 ∨ 229 ≤ r := by
  cases lt_or_ge r 198 with
  | inl h => exact Or.inl (by omega)
  | inr h =>
    cases lt_or_ge r 229 with
    | inl h2 =>
      have hr1 : r % 4 = 1 := by simpa [Nat.ModEq] using h1
      have : r = 201 ∨ r = 205 ∨ r = 209 ∨ r = 213 ∨ r = 217 ∨
          r = 221 ∨ r = 225 := by omega
      rcases this with h | h | h | h | h | h | h
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 67 = 201)
            (by decide) (by decide))
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 41 = 205)
            (by decide) (by decide))
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (11 : ℕ) * 19 = 209)
            (by decide) (by decide))
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 71 = 213)
            (by decide) (by decide))
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (7 : ℕ) * 31 = 217)
            (by decide) (by decide))
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (13 : ℕ) * 17 = 221)
            (by decide) (by decide))
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (9 : ℕ) * 25 = 225)
            (by decide) (by decide))
    | inr h2 => exact Or.inr h2

lemma prime_one_mod4_le269_or_ge277 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) :
    r ≤ 269 ∨ 277 ≤ r := by
  cases lt_or_ge r 270 with
  | inl h => exact Or.inl (by omega)
  | inr h =>
    cases lt_or_ge r 277 with
    | inl h2 =>
      have hr1 : r % 4 = 1 := by simpa [Nat.ModEq] using h1
      have : r = 273 := by omega
      subst this
      exact absurd hr
        (Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 91 = 273)
          (by decide) (by decide))
    | inr h2 => exact Or.inr h2

lemma prime_one_mod4_le73_or_89_or_ge97 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) (h29 : 29 ≤ r) :
    r ≤ 73 ∨ r = 89 ∨ 97 ≤ r := by
  by_cases h97 : 97 ≤ r
  · exact Or.inr (Or.inr h97)
  · have : r < 97 := by omega
    interval_cases r
    all_goals
      first
      | exact Or.inl (by omega)
      | exact Or.inr (Or.inl rfl)
      | exact absurd hr (by decide)
      | simp [Nat.ModEq] at h1

lemma prime_one_mod4_le61_or_73_or_ge89 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) (h29 : 29 ≤ r) :
    r ≤ 61 ∨ r = 73 ∨ 89 ≤ r := by
  by_cases h89 : 89 ≤ r
  · exact Or.inr (Or.inr h89)
  · have : r < 89 := by omega
    interval_cases r
    all_goals
      first
      | exact Or.inl (by omega)
      | exact Or.inr (Or.inl rfl)
      | exact absurd hr (by decide)
      | simp [Nat.ModEq] at h1

lemma four016_f5sq_f37_f73_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 37 * fSum 73 := by
  rw [fSum_five_sq, fSum_thirty_seven, fSum_seventy_three]; norm_num

lemma four017_f5sq_f37_f89sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 37 *
      (1 + 1 / ((89 : ℚ) + 1) + 1 / ((89 : ℚ) ^ 2 + 89 + 1)) < 2 := by
  rw [fSum_five_sq, fSum_thirty_seven]; norm_num

lemma f14_f5sq_f37sq_f89_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (37 ^ 2) * fSum 89 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_sq,
    fSum_thirty_seven_sq, fSum_prime (by decide : Nat.Prime 89)]
  norm_num

lemma four017_f5sq_f37sq_f97sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (37 ^ 2) * fSum (97 ^ 2) < 2 := by
  rw [fSum_five_sq, fSum_thirty_seven_sq,
    fSum_prime_sq (by decide : Nat.Prime 97)]
  norm_num

lemma four016_f5sq_f41_f61_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 41 * fSum 61 := by
  rw [fSum_five_sq, fSum_forty_one, fSum_sixty_one]; norm_num

lemma four017_f5sq_f41_f73sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 41 *
      (1 + 1 / ((73 : ℚ) + 1) + 1 / ((73 : ℚ) ^ 2 + 73 + 1)) < 2 := by
  rw [fSum_five_sq, fSum_forty_one]; norm_num

lemma fs16067_f5sq_f41sq_f73_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum 73 < 2 := by
  rw [fSum_five_sq, fSum_forty_one_sq, fSum_seventy_three]; norm_num

lemma f14_f5sq_f41sq_f73sq_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (73 ^ 2) := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_sq,
    fSum_forty_one_sq, fSum_prime_sq (by decide : Nat.Prime 73)]
  norm_num

lemma four017_f5sq_f41sq_f89sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (89 ^ 2) < 2 := by
  rw [fSum_five_sq, fSum_forty_one_sq,
    fSum_prime_sq (by decide : Nat.Prime 89)]
  norm_num

lemma four017_f5sq_f53sq_f53sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (53 ^ 2) * fSum (53 ^ 2) < 2 := by
  rw [fSum_five_sq, fSum_fifty_three_sq]; norm_num

lemma ge21_five_two_ge29_third_ne_two {a q kq r kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hq29 : 29 ≤ q) (hle : q ≤ r)
    (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  have h2pos := fSum_pos (pow_ne_zero a two_ne_zero)
  have h5pos := fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have h2b := fSum_two_pow_lt_4017_2500 a
  have h2b' := fSum_two_pow_lt_16067_10000 a
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hrle := fSum_le_sq_of_exp_le_two hr hkr
  have hqk : 1 ≤ kq := by omega
  have hrk : 1 ≤ kr := by omega
  rcases prime_one_mod4_ge29_four_cases hq hq1 hq29 with hq29eq | hq37 | hq41 | hq53
  · subst hq29eq
    cases hkq with
    | inl hk1 =>
      subst hk1
      rcases prime_one_mod4_le197_or_ge229 hr hr1 with hr197 | hr229
      · have hC : ((197 : ℚ) + 2) / (197 + 1) ≤ fSum r :=
          fSum_prime_ge_form hr hr197
        have hC' : ((197 : ℚ) + 2) / (197 + 1) ≤ fSum (r ^ kr) :=
          le_trans hC (fSum_ge_prime hr hkr)
        have hth : 2 < (4016 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 29 *
            (((197 : ℚ) + 2) / (197 + 1)) := by
          convert four016_f5sq_f29_f197_gt_two using 1
          ring
        have hmin :=
          ge14_mul3_gt_two (n := a) (A := fSum (5 ^ 2)) (B := fSum 29)
            (C := ((197 : ℚ) + 2) / (197 + 1))
            h14 h5pos (fSum_pos (by decide)) (by norm_num) hth
        have hmono := mul3_gt_of le_rfl le_rfl hC'
          (fSum_pos (by decide : (29 : ℕ) ≠ 0)).le
          (mul_nonneg h2pos.le h5pos.le)
          (by norm_num)
          (mul_nonneg (mul_nonneg h2pos.le h5pos.le)
            (fSum_pos (by decide : (29 : ℕ) ≠ 0)).le)
        rw [pow_one]
        exact ne_of_gt (lt_of_lt_of_le hmin hmono)
      · have hD : fSum (r ^ kr) ≤
            1 + 1 / ((229 : ℚ) + 1) + 1 / ((229 : ℚ) ^ 2 + 229 + 1) :=
          (fSum_le_sq_of_exp_le_two hr hkr).trans
            (fSum_prime_sq_le_form hr (by decide) hr229)
        have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (29 ^ 1) * fSum (r ^ kr) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 29 *
              (1 + 1 / ((229 : ℚ) + 1) + 1 / ((229 : ℚ) ^ 2 + 229 + 1)) := by
          rw [pow_one]
          have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
              (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
            mul_lt_mul_of_pos_right h2b h5pos
          have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum 29 <
              (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 29 :=
            mul_lt_mul_of_pos_right hA (fSum_pos (by decide))
          exact mul_lt_mul hB hD hrpos (by positivity)
        exact ne_of_lt (h1.trans four017_f5sq_f29_f229sq_lt_two)
    | inr hk2 =>
      subst hk2
      rcases prime_one_mod4_le269_or_ge277 hr hr1 with hr269 | hr277
      · have hC : ((269 : ℚ) + 2) / (269 + 1) ≤ fSum r :=
          fSum_prime_ge_form hr hr269
        have hC' : ((269 : ℚ) + 2) / (269 + 1) ≤ fSum (r ^ kr) :=
          le_trans hC (fSum_ge_prime hr hkr)
        have hlo : fSum (2 ^ 14) ≤ fSum (2 ^ a) := fSum_two_pow_ge_fourteen h14
        have h1 : fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (29 ^ 2) *
            (((269 : ℚ) + 2) / (269 + 1)) ≤
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (29 ^ 2) * fSum (r ^ kr) := by
          have hA : fSum (2 ^ 14) * fSum (5 ^ 2) ≤
              fSum (2 ^ a) * fSum (5 ^ 2) :=
            mul_le_mul_of_nonneg_right hlo h5pos.le
          have hB : fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (29 ^ 2) ≤
              fSum (2 ^ a) * fSum (5 ^ 2) * fSum (29 ^ 2) :=
            mul_le_mul_of_nonneg_right hA
              (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0))).le
          exact mul_le_mul hB hC' (by norm_num)
            (mul_nonneg (mul_nonneg
              (fSum_pos (pow_ne_zero a two_ne_zero)).le h5pos.le)
              (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0))).le)
        have hmin' : 2 < fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (29 ^ 2) *
            (((269 : ℚ) + 2) / (269 + 1)) := by
          convert f14_f5sq_f29sq_f269_gt_two using 1
          ring
        exact ne_of_gt (lt_of_lt_of_le hmin' h1)
      · have hD : fSum (r ^ kr) ≤
            1 + 1 / ((277 : ℚ) + 1) + 1 / ((277 : ℚ) ^ 2 + 277 + 1) :=
          (fSum_le_sq_of_exp_le_two hr hkr).trans
            (fSum_prime_sq_le_form hr (by decide) hr277)
        have hqs : fSum (29 ^ 2) = fSum (29 ^ 2) := rfl
        have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (29 ^ 2) * fSum (r ^ kr) <
            (16067 : ℚ) / 10000 * fSum (5 ^ 2) * fSum (29 ^ 2) *
              (1 + 1 / ((277 : ℚ) + 1) + 1 / ((277 : ℚ) ^ 2 + 277 + 1)) := by
          have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
              (16067 : ℚ) / 10000 * fSum (5 ^ 2) :=
            mul_lt_mul_of_pos_right h2b' h5pos
          have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (29 ^ 2) <
              (16067 : ℚ) / 10000 * fSum (5 ^ 2) * fSum (29 ^ 2) :=
            mul_lt_mul_of_pos_right hA
              (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0)))
          exact mul_lt_mul hB hD hrpos (by positivity)
        exact ne_of_lt (h1.trans fs16067_f5sq_f29sq_f277sq_lt_two)
  · subst hq37
    rcases prime_one_mod4_le73_or_89_or_ge97 hr hr1 (le_trans (by decide : 29 ≤ 37) hle)
      with hr73 | hr89 | hr97
    · have hC : fSum 73 ≤ fSum r := fSum_prime_anti hr (by decide : Nat.Prime 73) hr73
      have hC' : fSum 73 ≤ fSum (r ^ kr) := le_trans hC (fSum_ge_prime hr hkr)
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum (5 ^ 2)) (B := fSum 37) (C := fSum 73)
          h14 h5pos (fSum_pos (by decide)) (fSum_pos (by decide))
          four016_f5sq_f37_f73_gt_two
      have hB : fSum 37 ≤ fSum (37 ^ kq) := fSum_ge_prime (by decide) hkq
      have hmono := mul3_gt_of le_rfl hB hC'
        (fSum_pos (by decide : (37 : ℕ) ≠ 0)).le
        (mul_nonneg h2pos.le h5pos.le)
        (fSum_pos (by decide : (73 : ℕ) ≠ 0)).le
        (mul_nonneg (mul_nonneg h2pos.le h5pos.le)
          (fSum_pos (pow_ne_zero kq (by decide : (37 : ℕ) ≠ 0))).le)
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
    · subst hr89
      cases hkq with
      | inl hk1 =>
        subst hk1
        have hD : fSum (89 ^ kr) ≤
            1 + 1 / ((89 : ℚ) + 1) + 1 / ((89 : ℚ) ^ 2 + 89 + 1) := by
          have := fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 89) hkr
          have heq : fSum (89 ^ 2) =
              1 + 1 / ((89 : ℚ) + 1) + 1 / ((89 : ℚ) ^ 2 + 89 + 1) :=
            fSum_prime_sq (by decide : Nat.Prime 89)
          rwa [heq] at this
        have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (37 ^ 1) * fSum (89 ^ kr) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 37 *
              (1 + 1 / ((89 : ℚ) + 1) + 1 / ((89 : ℚ) ^ 2 + 89 + 1)) := by
          rw [pow_one]
          have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
              (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
            mul_lt_mul_of_pos_right h2b h5pos
          have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum 37 <
              (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 37 :=
            mul_lt_mul_of_pos_right hA (fSum_pos (by decide))
          exact mul_lt_mul hB hD
            (fSum_pos (pow_ne_zero kr (by decide : (89 : ℕ) ≠ 0)))
            (by positivity)
        exact ne_of_lt (h1.trans four017_f5sq_f37_f89sq_lt_two)
      | inr hk2 =>
        subst hk2
        have hC : fSum 89 ≤ fSum (89 ^ kr) :=
          fSum_ge_prime (by decide : Nat.Prime 89) hkr
        have hlo : fSum (2 ^ 14) ≤ fSum (2 ^ a) := fSum_two_pow_ge_fourteen h14
        have h1 : fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (37 ^ 2) * fSum 89 ≤
            fSum (2 ^ a) * fSum (5 ^ 2) * fSum (37 ^ 2) * fSum (89 ^ kr) := by
          have hA : fSum (2 ^ 14) * fSum (5 ^ 2) ≤
              fSum (2 ^ a) * fSum (5 ^ 2) :=
            mul_le_mul_of_nonneg_right hlo h5pos.le
          have hB : fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (37 ^ 2) ≤
              fSum (2 ^ a) * fSum (5 ^ 2) * fSum (37 ^ 2) :=
            mul_le_mul_of_nonneg_right hA
              (fSum_pos (pow_ne_zero 2 (by decide : (37 : ℕ) ≠ 0))).le
          exact mul_le_mul hB hC (fSum_pos (by decide)).le
            (mul_nonneg (mul_nonneg
              (fSum_pos (pow_ne_zero a two_ne_zero)).le h5pos.le)
              (fSum_pos (pow_ne_zero 2 (by decide : (37 : ℕ) ≠ 0))).le)
        exact ne_of_gt (lt_of_lt_of_le f14_f5sq_f37sq_f89_gt_two h1)
    · have hqs : fSum (37 ^ kq) ≤ fSum (37 ^ 2) :=
        fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 37) hkq
      have hrs : fSum (r ^ 2) ≤ fSum (97 ^ 2) :=
        fSum_prime_sq_anti (by decide : Nat.Prime 97) hr hr97
      have hD : fSum (r ^ kr) ≤ fSum (97 ^ 2) :=
        le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
      have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (37 ^ kq) * fSum (r ^ kr) <
          (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (37 ^ 2) * fSum (97 ^ 2) := by
        have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
          mul_lt_mul_of_pos_right h2b h5pos
        have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (37 ^ kq) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (37 ^ 2) :=
          mul_lt_mul hA hqs hqpos (mul_nonneg (by norm_num) h5pos.le)
        exact mul_lt_mul hB hD hrpos (mul_nonneg (mul_nonneg (by norm_num) h5pos.le)
          (fSum_pos (pow_ne_zero 2 (by decide : (37 : ℕ) ≠ 0))).le)
      exact ne_of_lt (h1.trans four017_f5sq_f37sq_f97sq_lt_two)
  · subst hq41
    rcases prime_one_mod4_le61_or_73_or_ge89 hr hr1 (le_trans (by decide : 29 ≤ 41) hle)
      with hr61 | hr73 | hr89
    · have hC : fSum 61 ≤ fSum r := fSum_prime_anti hr (by decide : Nat.Prime 61) hr61
      have hC' : fSum 61 ≤ fSum (r ^ kr) := le_trans hC (fSum_ge_prime hr hkr)
      have hB : fSum 41 ≤ fSum (41 ^ kq) := fSum_ge_prime (by decide) hkq
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum (5 ^ 2)) (B := fSum 41) (C := fSum 61)
          h14 h5pos (fSum_pos (by decide)) (fSum_pos (by decide))
          four016_f5sq_f41_f61_gt_two
      have hmono := mul3_gt_of le_rfl hB hC'
        (fSum_pos (by decide : (41 : ℕ) ≠ 0)).le
        (mul_nonneg h2pos.le h5pos.le)
        (fSum_pos (by decide : (61 : ℕ) ≠ 0)).le
        (mul_nonneg (mul_nonneg h2pos.le h5pos.le)
          (fSum_pos (pow_ne_zero kq (by decide : (41 : ℕ) ≠ 0))).le)
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
    · subst hr73
      cases hkq with
      | inl hk1 =>
        subst hk1
        have hD : fSum (73 ^ kr) ≤
            1 + 1 / ((73 : ℚ) + 1) + 1 / ((73 : ℚ) ^ 2 + 73 + 1) := by
          have := fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 73) hkr
          have heq : fSum (73 ^ 2) =
              1 + 1 / ((73 : ℚ) + 1) + 1 / ((73 : ℚ) ^ 2 + 73 + 1) :=
            fSum_prime_sq (by decide : Nat.Prime 73)
          rwa [heq] at this
        have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (41 ^ 1) * fSum (73 ^ kr) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 41 *
              (1 + 1 / ((73 : ℚ) + 1) + 1 / ((73 : ℚ) ^ 2 + 73 + 1)) := by
          rw [pow_one]
          have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
              (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
            mul_lt_mul_of_pos_right h2b h5pos
          have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum 41 <
              (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 41 :=
            mul_lt_mul_of_pos_right hA (fSum_pos (by decide))
          exact mul_lt_mul hB hD
            (fSum_pos (pow_ne_zero kr (by decide : (73 : ℕ) ≠ 0)))
            (by positivity)
        exact ne_of_lt (h1.trans four017_f5sq_f41_f73sq_lt_two)
      | inr hk2 =>
        subst hk2
        cases hkr with
        | inl hr1e =>
          subst hr1e
          have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (73 ^ 1) <
              (16067 : ℚ) / 10000 * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum 73 := by
            rw [pow_one]
            have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
                (16067 : ℚ) / 10000 * fSum (5 ^ 2) :=
              mul_lt_mul_of_pos_right h2b' h5pos
            have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (41 ^ 2) <
                (16067 : ℚ) / 10000 * fSum (5 ^ 2) * fSum (41 ^ 2) :=
              mul_lt_mul_of_pos_right hA
                (fSum_pos (pow_ne_zero 2 (by decide : (41 : ℕ) ≠ 0)))
            exact mul_lt_mul_of_pos_right hB (fSum_pos (by decide))
          exact ne_of_lt (h1.trans fs16067_f5sq_f41sq_f73_lt_two)
        | inr hr2e =>
          subst hr2e
          have hlo : fSum (2 ^ 14) ≤ fSum (2 ^ a) := fSum_two_pow_ge_fourteen h14
          have h1 : fSum (2 ^ 14) * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (73 ^ 2) ≤
              fSum (2 ^ a) * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (73 ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hlo h5pos.le)
                (fSum_pos (pow_ne_zero 2 (by decide : (41 : ℕ) ≠ 0))).le)
              (fSum_pos (pow_ne_zero 2 (by decide : (73 : ℕ) ≠ 0))).le
          exact ne_of_gt (lt_of_lt_of_le f14_f5sq_f41sq_f73sq_gt_two h1)
    · have hqs : fSum (41 ^ kq) ≤ fSum (41 ^ 2) :=
        fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 41) hkq
      have hrs : fSum (r ^ 2) ≤ fSum (89 ^ 2) :=
        fSum_prime_sq_anti (by decide : Nat.Prime 89) hr hr89
      have hD : fSum (r ^ kr) ≤ fSum (89 ^ 2) :=
        le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
      have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (41 ^ kq) * fSum (r ^ kr) <
          (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (89 ^ 2) := by
        have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
          mul_lt_mul_of_pos_right h2b h5pos
        have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (41 ^ kq) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (41 ^ 2) :=
          mul_lt_mul hA hqs hqpos (mul_nonneg (by norm_num) h5pos.le)
        exact mul_lt_mul hB hD hrpos (mul_nonneg (mul_nonneg (by norm_num) h5pos.le)
          (fSum_pos (pow_ne_zero 2 (by decide : (41 : ℕ) ≠ 0))).le)
      exact ne_of_lt (h1.trans four017_f5sq_f41sq_f89sq_lt_two)
  · have hqs : fSum (q ^ kq) ≤ fSum (q ^ 2) := hqle
    have hqs' : fSum (q ^ 2) ≤ fSum (53 ^ 2) :=
      fSum_prime_sq_anti (by decide : Nat.Prime 53) hq hq53
    have hC : fSum (q ^ kq) ≤ fSum (53 ^ 2) := le_trans hqs hqs'
    have hrs : fSum (r ^ 2) ≤ fSum (53 ^ 2) :=
      fSum_prime_sq_anti (by decide : Nat.Prime 53) hr (le_trans hq53 hle)
    have hD : fSum (r ^ kr) ≤ fSum (53 ^ 2) :=
      le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
    have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) <
        (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (53 ^ 2) * fSum (53 ^ 2) := by
      have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
          (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
        mul_lt_mul_of_pos_right h2b h5pos
      have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) <
          (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (53 ^ 2) :=
        mul_lt_mul hA hC hqpos (mul_nonneg (by norm_num) h5pos.le)
      exact mul_lt_mul hB hD hrpos (mul_nonneg (mul_nonneg (by norm_num) h5pos.le)
        (fSum_pos (pow_ne_zero 2 (by decide : (53 : ℕ) ≠ 0))).le)
    exact ne_of_lt (h1.trans four017_f5sq_f53sq_f53sq_lt_two)

lemma ge21_five_one_seventeen_mid_ne_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hmid : r = 97 ∨ r = 101 ∨ r = 109 ∨ r = 113)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  cases hkq with
  | inl h1 =>
    subst h1
    have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
    have h2b := fSum_two_pow_lt_4017_2500 a
    have h5p := fSum_pos (by decide : (5 : ℕ) ≠ 0)
    have h17p := fSum_pos (by decide : (17 : ℕ) ≠ 0)
    have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
    have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ 1) * fSum (r ^ kr) <
        (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (r ^ 2) := by
      rw [pow_one, pow_one]
      have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
        mul_lt_mul_of_pos_right h2b h5p
      have hB : fSum (2 ^ a) * fSum 5 * fSum 17 <
          (4017 : ℚ) / 2500 * fSum 5 * fSum 17 :=
        mul_lt_mul_of_pos_right hA h17p
      exact mul_lt_mul hB hD hrpos (by positivity)
    rcases hmid with h | h | h | h
    · subst h
      exact ne_of_lt (h1.trans four017_f5_f17_f97sq_lt_two)
    · subst h
      exact ne_of_lt (h1.trans four017_f5_f17_f101sq_lt_two)
    · subst h
      exact ne_of_lt (h1.trans four017_f5_f17_f109sq_lt_two)
    · subst h
      exact ne_of_lt (h1.trans four017_f5_f17_f113sq_lt_two)
  | inr h2 =>
    subst h2
    have hC : fSum r ≤ fSum (r ^ kr) := fSum_ge_prime hr hkr
    have h113 : fSum 113 ≤ fSum r := by
      have hle : r ≤ 113 := by
        rcases hmid with h | h | h | h <;> subst h <;> omega
      exact fSum_prime_anti hr (by decide : Nat.Prime 113) hle
    have hmin :=
      ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum (17 ^ 2)) (C := fSum 113)
        h14 (fSum_pos (by decide)) (fSum_pos (by decide))
        (fSum_pos (by decide)) four016_f5_f17sq_f113_gt_two
    have hle : fSum 113 ≤ fSum (r ^ kr) := le_trans h113 hC
    have hmono := mul3_gt_of le_rfl le_rfl hle
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le
      (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      (fSum_pos (by decide : (113 : ℕ) ≠ 0)).le
      (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
    rw [pow_one]
    exact ne_of_gt (lt_of_lt_of_le hmin hmono)

lemma no_five_three_one_mod4_any_lt_two {a p kp q kq r kr : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp13 : 13 ≤ p) (hq17 : 17 ≤ q) (hr29 : 29 ≤ r)
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) < 2 := by
  have hple : fSum (p ^ kp) ≤ fSum (p ^ 2) := fSum_le_sq_of_exp_le_two hp hkp
  have hqle : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
  have hrle : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
  have hbound := no_five_three_one_mod4_sq_lt_two (a := a) hp hq hr hp13 hq17 hr29
  have h1 : fSum (2 ^ a) * fSum (p ^ kp) ≤ fSum (2 ^ a) * fSum (p ^ 2) :=
    mul_le_mul_of_nonneg_left hple (fSum_pos (pow_ne_zero a two_ne_zero)).le
  have h2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) ≤
      fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) :=
    mul_le_mul h1 hqle (fSum_pos (pow_ne_zero kq hq.ne_zero)).le
      (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (pow_ne_zero 2 hp.ne_zero)).le)
  have h3 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≤
      fSum (2 ^ a) * fSum (p ^ 2) * fSum (q ^ 2) * fSum (r ^ 2) :=
    mul_le_mul h2 hrle (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
      (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (pow_ne_zero 2 hp.ne_zero)).le)
        (fSum_pos (pow_ne_zero 2 hq.ne_zero)).le)
  exact h3.trans_lt hbound

lemma ge21_three_one_mod4_sorted_ne_two {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp1 : p ≡ 1 [MOD 4]) (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2)
    (hle1 : p ≤ q) (hle2 : q ≤ r) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have hpk : 1 ≤ kp := by omega
  have hqk : 1 ≤ kq := by omega
  have hrk : 1 ≤ kr := by omega
  rcases prime_one_mod_four_cases hp hp1 with hp5eq | hp13eq | hp17eq | hpge
  · subst hp5eq
    rcases prime_one_mod_four_cases hq hq1 with hq5eq | hq13eq | hq17eq | hqge
    · exact (hpq hq5eq.symm).elim
    · subst hq13eq
      exact ne_of_gt (ge21_five_thirteen_third_gt_two ha hr hpk hqk hrk)
    · subst hq17eq
      cases hkp with
      | inl hk1 =>
        subst hk1
        have hr29 : 29 ≤ r := by
          have : r ≠ 17 := hqr.symm
          rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
          · omega
          · omega
          · exact (this h17).elim
          · exact hge
        rcases prime_one_mod4_le73_or_89_or_ge97 hr hr1 hr29 with hr73 | hr89 | hr97
        · have hr89' : r ≤ 89 := le_trans hr73 (by decide)
          have hgt := ge21_five_one_seventeen_le89_gt_two ha hr hr89' hrk
          have hB : fSum (17 ^ 1) ≤ fSum (17 ^ kq) :=
            fSum_ge_prime (by decide : Nat.Prime 17) hkq
          have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ 1) * fSum (r ^ kr) ≤
              fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hB
                (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
                  (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le))
              (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
          exact ne_of_gt (lt_of_lt_of_le hgt h1)
        · subst hr89
          have hgt := ge21_five_one_seventeen_le89_gt_two ha hr (by decide) hrk
          have hB : fSum (17 ^ 1) ≤ fSum (17 ^ kq) :=
            fSum_ge_prime (by decide : Nat.Prime 17) hkq
          have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ 1) * fSum (89 ^ kr) ≤
              fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (89 ^ kr) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hB
                (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
                  (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le))
              (fSum_pos (pow_ne_zero kr (by decide : (89 : ℕ) ≠ 0))).le
          exact ne_of_gt (lt_of_lt_of_le hgt h1)
        · rcases prime_one_mod4_ge97_small_cases hr hr1 hr97 with
            h97 | h101 | h109 | h113 | h137
          · exact ge21_five_one_seventeen_mid_ne_two ha hr (Or.inl h97) hkq hkr
          · exact ge21_five_one_seventeen_mid_ne_two ha hr (Or.inr (Or.inl h101)) hkq hkr
          · exact ge21_five_one_seventeen_mid_ne_two ha hr
              (Or.inr (Or.inr (Or.inl h109))) hkq hkr
          · exact ge21_five_one_seventeen_mid_ne_two ha hr
              (Or.inr (Or.inr (Or.inr h113))) hkq hkr
          · exact ne_of_lt
              (ge21_five_one_seventeen_ge137_lt_two ha hr h137 hkq hkr)
      | inr hk2 =>
        subst hk2
        exact ne_of_gt (ge21_five_two_seventeen_third_gt_two ha hr hqk hrk)
    · cases hkp with
      | inl hk1 =>
        subst hk1
        have hr37 : 37 ≤ r := by
          have hrge : 29 ≤ r := le_trans hqge hle2
          have hrne : r ≠ 29 := by
            intro h
            have hqeq : q = 29 := le_antisymm (h ▸ hle2) hqge
            exact hqr (hqeq.trans h.symm)
          rcases prime_one_mod4_ge29_mid_cases hr hr1 hrge with h29 | h37
          · exact (hrne h29).elim
          · exact h37
        exact ne_of_lt
          (ge21_five_one_ge29_third_lt_two ha hq hr hqge hr37 hkq hkr)
      | inr hk2 =>
        subst hk2
        exact ge21_five_two_ge29_third_ne_two ha hq hr hqr hqge hle2 hq1 hr1 hkq hkr
  · -- p = 13
    subst hp13eq
    have hq17 : 17 ≤ q := by
      have hqne13 : q ≠ 13 := hpq.symm
      rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
      · omega
      · exact (hqne13 h13).elim
      · exact h17.symm ▸ le_rfl
      · exact le_trans (by decide : 17 ≤ 29) hge
    have hr29 : 29 ≤ r := by
      have hrge17 : 17 ≤ r := le_trans hq17 hle2
      have hrne17 : r ≠ 17 := by
        intro h
        have hqle : q ≤ 17 := h ▸ hle2
        have hqeq : q = 17 := le_antisymm hqle hq17
        exact hqr (hqeq.trans h.symm)
      rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
      · omega
      · omega
      · exact (hrne17 h17).elim
      · exact hge
    exact ne_of_lt
      (no_five_three_one_mod4_any_lt_two hp hq hr (by decide) hq17 hr29 hkp hkq hkr)
  · -- p = 17
    subst hp17eq
    have hq17 : 17 ≤ q := le_trans (by decide : 17 ≤ 17) hle1
    have hr29 : 29 ≤ r := by
      have hrge17 : 17 ≤ r := le_trans hq17 hle2
      have hrne17 : r ≠ 17 := hpr.symm
      rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
      · omega
      · omega
      · exact (hrne17 h17).elim
      · exact hge
    exact ne_of_lt
      (no_five_three_one_mod4_any_lt_two hp hq hr (by decide) hq17 hr29 hkp hkq hkr)
  · -- p ≥ 29
    have hq17 : 17 ≤ q := le_trans (by omega : 17 ≤ p) hle1
    have hr29 : 29 ≤ r := le_trans hpge (le_trans hle1 hle2)
    exact ne_of_lt
      (no_five_three_one_mod4_any_lt_two hp hq hr (by omega) hq17 hr29 hkp hkq hkr)

lemma ge21_three_one_mod4_ne_two {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp1 : p ≡ 1 [MOD 4]) (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  rcases le_total p q with hpq_le | hqp_le
  · rcases le_total q r with hqr_le | hrq_le
    · exact ge21_three_one_mod4_sorted_ne_two ha hp hq hr hpq hpr hqr
        hp1 hq1 hr1 hkp hkq hkr hpq_le hqr_le
    · rcases le_total p r with hpr_le | hrp_le
      · have hswap : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ a) * fSum (p ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
        rw [hswap]
        exact ge21_three_one_mod4_sorted_ne_two ha hp hr hq hpr hpq hqr.symm
          hp1 hr1 hq1 hkp hkr hkq hpr_le hrq_le
      · have hswap : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ a) * fSum (r ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
        rw [hswap]
        exact ge21_three_one_mod4_sorted_ne_two ha hr hp hq hpr.symm hqr.symm hpq
          hr1 hp1 hq1 hkr hkp hkq hrp_le hpq_le
  · rcases le_total p r with hpr_le | hrp_le
    · have hswap : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
          fSum (2 ^ a) * fSum (q ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) := by ring
      rw [hswap]
      exact ge21_three_one_mod4_sorted_ne_two ha hq hp hr hpq.symm hqr hpr
        hq1 hp1 hr1 hkq hkp hkr hqp_le hpr_le
    · rcases le_total q r with hqr_le | hrq_le
      · have hswap : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ a) * fSum (q ^ kq) * fSum (r ^ kr) * fSum (p ^ kp) := by ring
        rw [hswap]
        exact ge21_three_one_mod4_sorted_ne_two ha hq hr hp hqr hpq.symm hpr.symm
          hq1 hr1 hp1 hkq hkr hkp hqr_le hrp_le
      · have hswap : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ a) * fSum (r ^ kr) * fSum (q ^ kq) * fSum (p ^ kp) := by ring
        rw [hswap]
        exact ge21_three_one_mod4_sorted_ne_two ha hr hq hp hqr.symm hpr.symm hpq.symm
          hr1 hq1 hp1 hkr hkq hkp hrq_le hqp_le

lemma f25_f5_f13_f17_gt_two :
    2 < fSum (2 ^ 5) * fSum 5 * fSum 13 * fSum 17 := by
  rw [fSum_two_pow_five, fSum_five, fSum_thirteen, fSum_seventeen]; norm_num

lemma f25_f5sq_f17_gt_two :
    2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 17 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_seventeen]; norm_num

lemma f25_f5_f17_f41_gt_two :
    2 < fSum (2 ^ 5) * fSum 5 * fSum 17 * fSum 41 := by
  rw [fSum_two_pow_five, fSum_five, fSum_seventeen, fSum_forty_one]; norm_num

lemma f25_f5_f17_f53sq_lt_two :
    fSum (2 ^ 5) * fSum 5 * fSum 17 * fSum (53 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five, fSum_seventeen, fSum_fifty_three_sq]; norm_num

lemma f25_f5_f17sq_f53_gt_two :
    2 < fSum (2 ^ 5) * fSum 5 * fSum (17 ^ 2) * fSum 53 := by
  rw [fSum_two_pow_five, fSum_five, fSum_seventeen_sq, fSum_fifty_three]; norm_num

lemma f25_f5_f17sq_f61sq_lt_two :
    fSum (2 ^ 5) * fSum 5 * fSum (17 ^ 2) * fSum (61 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five, fSum_seventeen_sq,
    fSum_prime_sq (by decide : Nat.Prime 61)]; norm_num

lemma f25_f5_f29sq_f37sq_lt_two :
    fSum (2 ^ 5) * fSum 5 * fSum (29 ^ 2) * fSum (37 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five, fSum_twenty_nine_sq, fSum_thirty_seven_sq]
  norm_num

lemma f25_f5sq_f29_f61_gt_two :
    2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 29 * fSum 61 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_twenty_nine, fSum_sixty_one]; norm_num

lemma f25_f5sq_f29_f73sq_lt_two :
    fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 29 * fSum (73 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_twenty_nine,
    fSum_prime_sq (by decide : Nat.Prime 73)]; norm_num

lemma f25_f5sq_f29sq_f73_lt_two :
    fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ 2) * fSum 73 < 2 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_twenty_nine_sq, fSum_seventy_three]
  norm_num

lemma f25_f5sq_f29sq_f73sq_gt_two :
    2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ 2) * fSum (73 ^ 2) := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_twenty_nine_sq,
    fSum_prime_sq (by decide : Nat.Prime 73)]; norm_num

lemma f25_f5sq_f29sq_f89sq_lt_two :
    fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ 2) * fSum (89 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_twenty_nine_sq,
    fSum_prime_sq (by decide : Nat.Prime 89)]; norm_num

lemma f25_f5sq_f37_f41_gt_two :
    2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 37 * fSum 41 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_thirty_seven, fSum_forty_one]; norm_num

lemma f25_f5sq_f37sq_f53sq_lt_two :
    fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (37 ^ 2) * fSum (53 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_thirty_seven_sq, fSum_fifty_three_sq]
  norm_num

lemma f25_f5sq_f41sq_f53sq_lt_two :
    fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (53 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_forty_one_sq, fSum_fifty_three_sq]
  norm_num

lemma f25_f5sq_f53sq_f53sq_lt_two :
    fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (53 ^ 2) * fSum (53 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_fifty_three_sq]; norm_num

lemma f25_f13sq_f17sq_f29sq_lt_two :
    fSum (2 ^ 5) * fSum (13 ^ 2) * fSum (17 ^ 2) * fSum (29 ^ 2) < 2 := by
  rw [fSum_two_pow_five, fSum_thirteen_sq, fSum_seventeen_sq, fSum_twenty_nine_sq]
  norm_num

lemma prime_one_mod4_le41_or_53_or_ge61 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) (h29 : 29 ≤ r) :
    r ≤ 41 ∨ r = 53 ∨ 61 ≤ r := by
  by_cases h61 : 61 ≤ r
  · exact Or.inr (Or.inr h61)
  · have : r < 61 := by omega
    interval_cases r
    all_goals
      first
      | exact Or.inl (by omega)
      | exact Or.inr (Or.inl rfl)
      | exact absurd hr (by decide)
      | simp [Nat.ModEq] at h1

lemma f25_f5sq_f13_gt_two :
    2 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 13 := by
  rw [fSum_two_pow_five, fSum_five_sq, fSum_thirteen]; norm_num

lemma f25_f5_f13_f173form_gt_two :
    2 < fSum (2 ^ 5) * fSum 5 * fSum 13 * (((173 : ℚ) + 2) / (173 + 1)) := by
  rw [fSum_two_pow_five, fSum_five, fSum_thirteen]; norm_num

lemma f25_f5_f13_geom181_lt_two :
    fSum (2 ^ 5) * fSum 5 * fSum 13 * ((181 : ℚ) / (181 - 1)) < 2 := by
  rw [fSum_two_pow_five, fSum_five, fSum_thirteen]; norm_num

lemma f25_f5_f13sq_f1777form_gt_two :
    2 < fSum (2 ^ 5) * fSum 5 * fSum (13 ^ 2) *
      (((1777 : ℚ) + 2) / (1777 + 1)) := by
  rw [fSum_two_pow_five, fSum_five, fSum_thirteen_sq]; norm_num

lemma f25_f5_f13sq_geom1789_lt_two :
    fSum (2 ^ 5) * fSum 5 * fSum (13 ^ 2) * ((1789 : ℚ) / (1789 - 1)) < 2 := by
  rw [fSum_two_pow_five, fSum_five, fSum_thirteen_sq]; norm_num

lemma prime_one_mod4_le173_or_ge181 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) :
    r ≤ 173 ∨ 181 ≤ r := by
  cases lt_or_ge r 174 with
  | inl h => exact Or.inl (by omega)
  | inr h =>
    cases lt_or_ge r 181 with
    | inl h2 =>
      have hr1 : r % 4 = 1 := by simpa [Nat.ModEq] using h1
      have : r = 177 := by omega
      subst this
      exact absurd hr
        (Nat.not_prime_of_mul_eq (by norm_num : (3 : ℕ) * 59 = 177)
          (by decide) (by decide))
    | inr h2 => exact Or.inr h2

lemma prime_one_mod4_le1777_or_ge1789 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) :
    r ≤ 1777 ∨ 1789 ≤ r := by
  cases lt_or_ge r 1778 with
  | inl h => exact Or.inl (by omega)
  | inr h =>
    cases lt_or_ge r 1789 with
    | inl h2 =>
      have hr1 : r % 4 = 1 := by simpa [Nat.ModEq] using h1
      have : r = 1781 ∨ r = 1785 := by omega
      rcases this with h | h
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (13 : ℕ) * 137 = 1781)
            (by decide) (by decide))
      · subst h; exact absurd hr
          (Nat.not_prime_of_mul_eq (by norm_num : (5 : ℕ) * 357 = 1785)
            (by decide) (by decide))
    | inr h2 => exact Or.inr h2

lemma five_three_one_mod4_sorted_ne_two {p kp q kq r kr : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp1 : p ≡ 1 [MOD 4]) (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2)
    (hle1 : p ≤ q) (hle2 : q ≤ r) :
    fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have hpk : 1 ≤ kp := by omega
  have hqk : 1 ≤ kq := by omega
  have hrk : 1 ≤ kr := by omega
  have h5pos := fSum_pos (pow_ne_zero 5 two_ne_zero)
  rcases prime_one_mod_four_cases hp hp1 with hp5eq | hp13eq | hp17eq | hpge
  · subst hp5eq
    rcases prime_one_mod_four_cases hq hq1 with hq5eq | hq13eq | hq17eq | hqge
    · exact (hpq hq5eq.symm).elim
    · subst hq13eq
      have hr17 : 17 ≤ r := by
        have hrne13 : r ≠ 13 := hqr.symm
        rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
        · omega
        · exact (hrne13 h13).elim
        · exact h17.symm ▸ le_rfl
        · exact le_trans (by decide : 17 ≤ 29) hge
      cases hkp with
      | inl hk1 =>
        subst hk1
        cases hkq with
        | inl hq1e =>
          subst hq1e
          rcases prime_one_mod4_le173_or_ge181 hr hr1 with hr173 | hr181
          · have hC : ((173 : ℚ) + 2) / (173 + 1) ≤ fSum r :=
              fSum_prime_ge_form hr hr173
            have hC' : ((173 : ℚ) + 2) / (173 + 1) ≤ fSum (r ^ kr) :=
              le_trans hC (fSum_ge_prime hr hkr)
            have h1 : fSum (2 ^ 5) * fSum 5 * fSum 13 *
                (((173 : ℚ) + 2) / (173 + 1)) ≤
                fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (13 ^ 1) * fSum (r ^ kr) := by
              rw [pow_one, pow_one]
              exact mul_le_mul_of_nonneg_left hC'
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                  (fSum_pos (by decide : (13 : ℕ) ≠ 0)).le)
            exact ne_of_gt (lt_of_lt_of_le f25_f5_f13_f173form_gt_two h1)
          · have hσ := fSum_prime_pow_lt_geom (l := kr) hr
            have hrge : (181 : ℚ) ≤ r := by exact_mod_cast hr181
            have hq1Q : (1 : ℚ) < r := by exact_mod_cast hr.one_lt
            have hgeom : (r : ℚ) / (r - 1) ≤ (181 : ℚ) / (181 - 1) := by
              have hden : (0 : ℚ) < r - 1 := sub_pos.mpr hq1Q
              have hden181 : (0 : ℚ) < (181 : ℚ) - 1 := by norm_num
              rw [div_le_div_iff₀ hden hden181]
              nlinarith
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (13 ^ 1) * fSum (r ^ kr) <
                fSum (2 ^ 5) * fSum 5 * fSum 13 * ((181 : ℚ) / (181 - 1)) := by
              rw [pow_one, pow_one]
              have hlt : fSum (r ^ kr) < (181 : ℚ) / (181 - 1) :=
                hσ.trans_le hgeom
              exact mul_lt_mul_of_pos_left hlt
                (mul_pos (mul_pos h5pos (fSum_pos (by decide : (5 : ℕ) ≠ 0)))
                  (fSum_pos (by decide : (13 : ℕ) ≠ 0)))
            exact ne_of_lt (h1.trans f25_f5_f13_geom181_lt_two)
        | inr hq2e =>
          subst hq2e
          rcases prime_one_mod4_le1777_or_ge1789 hr hr1 with hr1777 | hr1789
          · have hC : ((1777 : ℚ) + 2) / (1777 + 1) ≤ fSum r :=
              fSum_prime_ge_form hr hr1777
            have hC' : ((1777 : ℚ) + 2) / (1777 + 1) ≤ fSum (r ^ kr) :=
              le_trans hC (fSum_ge_prime hr hkr)
            have h1 : fSum (2 ^ 5) * fSum 5 * fSum (13 ^ 2) *
                (((1777 : ℚ) + 2) / (1777 + 1)) ≤
                fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (13 ^ 2) * fSum (r ^ kr) := by
              rw [pow_one]
              exact mul_le_mul_of_nonneg_left hC'
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                  (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
            exact ne_of_gt (lt_of_lt_of_le f25_f5_f13sq_f1777form_gt_two h1)
          · have hσ := fSum_prime_pow_lt_geom (l := kr) hr
            have hrge : (1789 : ℚ) ≤ r := by exact_mod_cast hr1789
            have hq1Q : (1 : ℚ) < r := by exact_mod_cast hr.one_lt
            have hgeom : (r : ℚ) / (r - 1) ≤ (1789 : ℚ) / (1789 - 1) := by
              have hden : (0 : ℚ) < r - 1 := sub_pos.mpr hq1Q
              have hden1789 : (0 : ℚ) < (1789 : ℚ) - 1 := by norm_num
              rw [div_le_div_iff₀ hden hden1789]
              nlinarith
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (13 ^ 2) * fSum (r ^ kr) <
                fSum (2 ^ 5) * fSum 5 * fSum (13 ^ 2) *
                  ((1789 : ℚ) / (1789 - 1)) := by
              rw [pow_one]
              have hlt : fSum (r ^ kr) < (1789 : ℚ) / (1789 - 1) :=
                hσ.trans_le hgeom
              exact mul_lt_mul_of_pos_left hlt
                (mul_pos (mul_pos h5pos (fSum_pos (by decide : (5 : ℕ) ≠ 0)))
                  (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))))
            exact ne_of_lt (h1.trans f25_f5_f13sq_geom1789_lt_two)
      | inr hk2 =>
        subst hk2
        have h0 := f25_f5sq_f13_gt_two
        have hB : fSum 13 ≤ fSum (13 ^ kq) :=
          fSum_ge_prime (by decide : Nat.Prime 13) hkq
        have hC : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
        have hpos : 0 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (13 ^ kq) :=
          mul_pos (mul_pos h5pos
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))))
            (fSum_pos (pow_ne_zero kq (by decide : (13 : ℕ) ≠ 0)))
        have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 13 ≤
            fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (13 ^ kq) :=
          mul_le_mul_of_nonneg_left hB
            (mul_nonneg h5pos.le
              (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
        nlinarith [h0, h1, hC, hpos]
    · subst hq17eq
      cases hkp with
      | inl hk1 =>
        subst hk1
        have hr29 : 29 ≤ r := by
          have hrne17 : r ≠ 17 := hqr.symm
          rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
          · omega
          · omega
          · exact (hrne17 h17).elim
          · exact hge
        rcases prime_one_mod4_le41_or_53_or_ge61 hr hr1 hr29 with hr41 | hr53 | hr61
        · have hC : fSum 41 ≤ fSum r :=
            fSum_prime_anti hr (by decide : Nat.Prime 41) hr41
          have hC' : fSum 41 ≤ fSum (r ^ kr) := le_trans hC (fSum_ge_prime hr hkr)
          have hB : fSum 17 ≤ fSum (17 ^ kq) := fSum_ge_prime (by decide) hkq
          have h1 : fSum (2 ^ 5) * fSum 5 * fSum 17 * fSum 41 ≤
              fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) := by
            rw [pow_one]
            have hB' : fSum (2 ^ 5) * fSum 5 * fSum 17 ≤
                fSum (2 ^ 5) * fSum 5 * fSum (17 ^ kq) :=
              mul_le_mul_of_nonneg_left hB
                (mul_nonneg h5pos.le (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
            exact mul_le_mul hB' hC' (fSum_pos (by decide)).le
              (mul_nonneg (mul_nonneg h5pos.le
                (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))).le)
          exact ne_of_gt (lt_of_lt_of_le f25_f5_f17_f41_gt_two h1)
        · subst hr53
          cases hkq with
          | inl hq1e =>
            subst hq1e
            have hD : fSum (53 ^ kr) ≤ fSum (53 ^ 2) :=
              fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 53) hkr
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (17 ^ 1) * fSum (53 ^ kr) ≤
                fSum (2 ^ 5) * fSum 5 * fSum 17 * fSum (53 ^ 2) := by
              rw [pow_one, pow_one]
              exact mul_le_mul_of_nonneg_left hD
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                  (fSum_pos (by decide : (17 : ℕ) ≠ 0)).le)
            exact ne_of_lt (h1.trans_lt f25_f5_f17_f53sq_lt_two)
          | inr hq2e =>
            subst hq2e
            have hC : fSum 53 ≤ fSum (53 ^ kr) :=
              fSum_ge_prime (by decide : Nat.Prime 53) hkr
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (17 ^ 2) * fSum 53 ≤
                fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (17 ^ 2) * fSum (53 ^ kr) :=
              mul_le_mul_of_nonneg_left hC
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                  (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
            rw [pow_one] at h1 ⊢
            exact ne_of_gt (lt_of_lt_of_le f25_f5_f17sq_f53_gt_two h1)
        · have hqs : fSum (17 ^ kq) ≤ fSum (17 ^ 2) :=
            fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 17) hkq
          have hrs : fSum (r ^ 2) ≤ fSum (61 ^ 2) :=
            fSum_prime_sq_anti (by decide : Nat.Prime 61) hr hr61
          have hD : fSum (r ^ kr) ≤ fSum (61 ^ 2) :=
            le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
          have h1 : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) ≤
              fSum (2 ^ 5) * fSum 5 * fSum (17 ^ 2) * fSum (61 ^ 2) := by
            rw [pow_one]
            have hB : fSum (2 ^ 5) * fSum 5 * fSum (17 ^ kq) ≤
                fSum (2 ^ 5) * fSum 5 * fSum (17 ^ 2) :=
              mul_le_mul_of_nonneg_left hqs
                (mul_nonneg h5pos.le (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
            exact mul_le_mul hB hD
              (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
              (mul_nonneg (mul_nonneg h5pos.le
                (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
                (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
          exact ne_of_lt (h1.trans_lt f25_f5_f17sq_f61sq_lt_two)
      | inr hk2 =>
        subst hk2
        have h0 := f25_f5sq_f17_gt_two
        have hB : fSum 17 ≤ fSum (17 ^ kq) :=
          fSum_ge_prime (by decide : Nat.Prime 17) hkq
        have hC : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
        have hpos : 0 < fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (17 ^ kq) :=
          mul_pos (mul_pos h5pos
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))))
            (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0)))
        have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 17 ≤
            fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (17 ^ kq) :=
          mul_le_mul_of_nonneg_left hB
            (mul_nonneg h5pos.le
              (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
        nlinarith [h0, h1, hC, hpos]
    · cases hkp with
      | inl hk1 =>
        subst hk1
        have hr37 : 37 ≤ r := by
          have hrge : 29 ≤ r := le_trans hqge hle2
          have hrne : r ≠ 29 := by
            intro h
            have hqeq : q = 29 := le_antisymm (h ▸ hle2) hqge
            exact hqr (hqeq.trans h.symm)
          rcases prime_one_mod4_ge29_mid_cases hr hr1 hrge with h29 | h37
          · exact (hrne h29).elim
          · exact h37
        have hqs : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
        have hqs' : fSum (q ^ 2) ≤ fSum (29 ^ 2) :=
          fSum_prime_sq_anti (by decide : Nat.Prime 29) hq hqge
        have hC : fSum (q ^ kq) ≤ fSum (29 ^ 2) := le_trans hqs hqs'
        have hrs : fSum (r ^ 2) ≤ fSum (37 ^ 2) :=
          fSum_prime_sq_anti (by decide : Nat.Prime 37) hr hr37
        have hD : fSum (r ^ kr) ≤ fSum (37 ^ 2) :=
          le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
        have h1 : fSum (2 ^ 5) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (r ^ kr) ≤
            fSum (2 ^ 5) * fSum 5 * fSum (29 ^ 2) * fSum (37 ^ 2) := by
          rw [pow_one]
          have hB : fSum (2 ^ 5) * fSum 5 * fSum (q ^ kq) ≤
              fSum (2 ^ 5) * fSum 5 * fSum (29 ^ 2) :=
            mul_le_mul_of_nonneg_left hC
              (mul_nonneg h5pos.le (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          exact mul_le_mul hB hD
            (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
            (mul_nonneg (mul_nonneg h5pos.le
              (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
              (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0))).le)
        exact ne_of_lt (h1.trans_lt f25_f5_f29sq_f37sq_lt_two)
      | inr hk2 =>
        subst hk2
        rcases prime_one_mod4_ge29_four_cases hq hq1 hqge with hq29eq | hq37 | hq41 | hq53
        · subst hq29eq
          rcases prime_one_mod4_le61_or_73_or_ge89 hr hr1 hle2 with hr61 | hr73 | hr89
          · have hC : fSum 61 ≤ fSum r :=
              fSum_prime_anti hr (by decide : Nat.Prime 61) hr61
            have hC' : fSum 61 ≤ fSum (r ^ kr) := le_trans hC (fSum_ge_prime hr hkr)
            have hB : fSum 29 ≤ fSum (29 ^ kq) := fSum_ge_prime (by decide) hkq
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 29 * fSum 61 ≤
                fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ kq) * fSum (r ^ kr) := by
              have hB' : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 29 ≤
                  fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ kq) :=
                mul_le_mul_of_nonneg_left hB
                  (mul_nonneg h5pos.le
                    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
              exact mul_le_mul hB' hC' (fSum_pos (by decide)).le
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
                  (fSum_pos (pow_ne_zero kq (by decide : (29 : ℕ) ≠ 0))).le)
            exact ne_of_gt (lt_of_lt_of_le f25_f5sq_f29_f61_gt_two h1)
          · subst hr73
            cases hkq with
            | inl hq1e =>
              subst hq1e
              have hD : fSum (73 ^ kr) ≤ fSum (73 ^ 2) :=
                fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 73) hkr
              have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ 1) * fSum (73 ^ kr) ≤
                  fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 29 * fSum (73 ^ 2) := by
                rw [pow_one]
                exact mul_le_mul_of_nonneg_left hD
                  (mul_nonneg (mul_nonneg h5pos.le
                    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
                    (fSum_pos (by decide : (29 : ℕ) ≠ 0)).le)
              exact ne_of_lt (h1.trans_lt f25_f5sq_f29_f73sq_lt_two)
            | inr hq2e =>
              subst hq2e
              cases hkr with
              | inl hr1e =>
                subst hr1e
                rw [pow_one]
                exact ne_of_lt f25_f5sq_f29sq_f73_lt_two
              | inr hr2e =>
                subst hr2e
                exact ne_of_gt f25_f5sq_f29sq_f73sq_gt_two
          · have hqs : fSum (29 ^ kq) ≤ fSum (29 ^ 2) :=
              fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 29) hkq
            have hrs : fSum (r ^ 2) ≤ fSum (89 ^ 2) :=
              fSum_prime_sq_anti (by decide : Nat.Prime 89) hr hr89
            have hD : fSum (r ^ kr) ≤ fSum (89 ^ 2) :=
              le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ kq) * fSum (r ^ kr) ≤
                fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ 2) * fSum (89 ^ 2) := by
              have hB : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ kq) ≤
                  fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (29 ^ 2) :=
                mul_le_mul_of_nonneg_left hqs
                  (mul_nonneg h5pos.le
                    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
              exact mul_le_mul hB hD
                (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
                  (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0))).le)
            exact ne_of_lt (h1.trans_lt f25_f5sq_f29sq_f89sq_lt_two)
        · subst hq37
          have : r ≠ 37 := hqr.symm
          have hr41or : r = 41 ∨ 53 ≤ r := by
            rcases prime_one_mod4_ge29_four_cases hr hr1 (le_trans (by decide : 29 ≤ 37) hle2)
              with h29 | h37 | h41 | h53
            · omega
            · exact (this h37).elim
            · exact Or.inl h41
            · exact Or.inr h53
          rcases hr41or with hr41 | hr53
          · subst hr41
            have hB : fSum 37 ≤ fSum (37 ^ kq) := fSum_ge_prime (by decide) hkq
            have hC : fSum 41 ≤ fSum (41 ^ kr) := fSum_ge_prime (by decide) hkr
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 37 * fSum 41 ≤
                fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (37 ^ kq) * fSum (41 ^ kr) := by
              have hB' : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum 37 ≤
                  fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (37 ^ kq) :=
                mul_le_mul_of_nonneg_left hB
                  (mul_nonneg h5pos.le
                    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
              exact mul_le_mul hB' hC (fSum_pos (by decide)).le
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
                  (fSum_pos (pow_ne_zero kq (by decide : (37 : ℕ) ≠ 0))).le)
            exact ne_of_gt (lt_of_lt_of_le f25_f5sq_f37_f41_gt_two h1)
          · have hqs : fSum (37 ^ kq) ≤ fSum (37 ^ 2) :=
              fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 37) hkq
            have hrs : fSum (r ^ 2) ≤ fSum (53 ^ 2) :=
              fSum_prime_sq_anti (by decide : Nat.Prime 53) hr hr53
            have hD : fSum (r ^ kr) ≤ fSum (53 ^ 2) :=
              le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
            have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (37 ^ kq) * fSum (r ^ kr) ≤
                fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (37 ^ 2) * fSum (53 ^ 2) := by
              have hB : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (37 ^ kq) ≤
                  fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (37 ^ 2) :=
                mul_le_mul_of_nonneg_left hqs
                  (mul_nonneg h5pos.le
                    (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
              exact mul_le_mul hB hD
                (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
                (mul_nonneg (mul_nonneg h5pos.le
                  (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
                  (fSum_pos (pow_ne_zero 2 (by decide : (37 : ℕ) ≠ 0))).le)
            exact ne_of_lt (h1.trans_lt f25_f5sq_f37sq_f53sq_lt_two)
        · subst hq41
          have hr53 : 53 ≤ r := by
            have : r ≠ 41 := hqr.symm
            rcases prime_one_mod4_ge29_four_cases hr hr1 (le_trans (by decide : 29 ≤ 41) hle2)
              with h29 | h37 | h41 | h53
            · omega
            · omega
            · exact (this h41).elim
            · exact h53
          have hqs : fSum (41 ^ kq) ≤ fSum (41 ^ 2) :=
            fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 41) hkq
          have hrs : fSum (r ^ 2) ≤ fSum (53 ^ 2) :=
            fSum_prime_sq_anti (by decide : Nat.Prime 53) hr hr53
          have hD : fSum (r ^ kr) ≤ fSum (53 ^ 2) :=
            le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
          have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (41 ^ kq) * fSum (r ^ kr) ≤
              fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (41 ^ 2) * fSum (53 ^ 2) := by
            have hB : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (41 ^ kq) ≤
                fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (41 ^ 2) :=
              mul_le_mul_of_nonneg_left hqs
                (mul_nonneg h5pos.le
                  (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
            exact mul_le_mul hB hD
              (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
              (mul_nonneg (mul_nonneg h5pos.le
                (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
                (fSum_pos (pow_ne_zero 2 (by decide : (41 : ℕ) ≠ 0))).le)
          exact ne_of_lt (h1.trans_lt f25_f5sq_f41sq_f53sq_lt_two)
        · have hqs : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
          have hqs' : fSum (q ^ 2) ≤ fSum (53 ^ 2) :=
            fSum_prime_sq_anti (by decide : Nat.Prime 53) hq hq53
          have hC : fSum (q ^ kq) ≤ fSum (53 ^ 2) := le_trans hqs hqs'
          have hrs : fSum (r ^ 2) ≤ fSum (53 ^ 2) :=
            fSum_prime_sq_anti (by decide : Nat.Prime 53) hr (le_trans hq53 hle2)
          have hD : fSum (r ^ kr) ≤ fSum (53 ^ 2) :=
            le_trans (fSum_le_sq_of_exp_le_two hr hkr) hrs
          have h1 : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) ≤
              fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (53 ^ 2) * fSum (53 ^ 2) := by
            have hB : fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (q ^ kq) ≤
                fSum (2 ^ 5) * fSum (5 ^ 2) * fSum (53 ^ 2) :=
              mul_le_mul_of_nonneg_left hC
                (mul_nonneg h5pos.le
                  (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
            exact mul_le_mul hB hD
              (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
              (mul_nonneg (mul_nonneg h5pos.le
                (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
                (fSum_pos (pow_ne_zero 2 (by decide : (53 : ℕ) ≠ 0))).le)
          exact ne_of_lt (h1.trans_lt f25_f5sq_f53sq_f53sq_lt_two)
  · -- p = 13, no 5
    subst hp13eq
    have hq17 : 17 ≤ q := by
      have hqne13 : q ≠ 13 := hpq.symm
      rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
      · omega
      · exact (hqne13 h13).elim
      · exact h17.symm ▸ le_rfl
      · exact le_trans (by decide : 17 ≤ 29) hge
    have hr29 : 29 ≤ r := by
      have hrge17 : 17 ≤ r := le_trans hq17 hle2
      have hrne17 : r ≠ 17 := by
        intro h
        have hqeq : q = 17 := le_antisymm (h ▸ hle2) hq17
        exact hqr (hqeq.trans h.symm)
      rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
      · omega
      · omega
      · exact (hrne17 h17).elim
      · exact hge
    exact ne_of_lt (no_five_three_one_mod4_any_lt_two hp hq hr
      (by decide) hq17 hr29 hkp hkq hkr)
  · -- p = 17
    subst hp17eq
    have hq17 : 17 ≤ q := le_trans (by decide : 17 ≤ 17) hle1
    have hr29 : 29 ≤ r := by
      have hrge17 : 17 ≤ r := le_trans hq17 hle2
      have hrne17 : r ≠ 17 := hpr.symm
      rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
      · omega
      · omega
      · exact (hrne17 h17).elim
      · exact hge
    exact ne_of_lt (no_five_three_one_mod4_any_lt_two hp hq hr
      (by decide) hq17 hr29 hkp hkq hkr)
  · -- p ≥ 29
    have hq17 : 17 ≤ q := le_trans (by omega : 17 ≤ p) hle1
    have hr29 : 29 ≤ r := le_trans hpge (le_trans hle1 hle2)
    exact ne_of_lt (no_five_three_one_mod4_any_lt_two hp hq hr
      (by omega) hq17 hr29 hkp hkq hkr)

lemma five_three_one_mod4_ne_two {p kp q kq r kr : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp1 : p ≡ 1 [MOD 4]) (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  rcases le_total p q with hpq_le | hqp_le
  · rcases le_total q r with hqr_le | hrq_le
    · exact five_three_one_mod4_sorted_ne_two hp hq hr hpq hpr hqr
        hp1 hq1 hr1 hkp hkq hkr hpq_le hqr_le
    · rcases le_total p r with hpr_le | hrp_le
      · have hswap : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ 5) * fSum (p ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
        rw [hswap]
        exact five_three_one_mod4_sorted_ne_two hp hr hq hpr hpq hqr.symm
          hp1 hr1 hq1 hkp hkr hkq hpr_le hrq_le
      · have hswap : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ 5) * fSum (r ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
        rw [hswap]
        exact five_three_one_mod4_sorted_ne_two hr hp hq hpr.symm hqr.symm hpq
          hr1 hp1 hq1 hkr hkp hkq hrp_le hpq_le
  · rcases le_total p r with hpr_le | hrp_le
    · have hswap : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
          fSum (2 ^ 5) * fSum (q ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) := by ring
      rw [hswap]
      exact five_three_one_mod4_sorted_ne_two hq hp hr hpq.symm hqr hpr
        hq1 hp1 hr1 hkq hkp hkr hqp_le hpr_le
    · rcases le_total q r with hqr_le | hrq_le
      · have hswap : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ 5) * fSum (q ^ kq) * fSum (r ^ kr) * fSum (p ^ kp) := by ring
        rw [hswap]
        exact five_three_one_mod4_sorted_ne_two hq hr hp hqr hpq.symm hpr.symm
          hq1 hr1 hp1 hkq hkr hkp hqr_le hrp_le
      · have hswap : fSum (2 ^ 5) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ 5) * fSum (r ^ kr) * fSum (q ^ kq) * fSum (p ^ kp) := by ring
        rw [hswap]
        exact five_three_one_mod4_sorted_ne_two hr hq hp hqr.symm hpr.symm hpq.symm
          hr1 hq1 hp1 hkr hkq hkp hrq_le hqp_le

lemma card_eq_five {α : Type*} [DecidableEq α] {s : Finset α} :
    s.card = 5 ↔ ∃ a b c d e,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
      s = {a, b, c, d, e} := by
  constructor
  · intro h
    obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp h
    obtain ⟨b, c, d, e, hbc, hbd, hbe, hcd, hce, hde, rfl⟩ :=
      Finset.card_eq_four.mp ht
    refine ⟨a, b, c, d, e, ?_, ?_, ?_, ?_, hbc, hbd, hbe, hcd, hce, hde, rfl⟩
    · intro h; subst h; exact hat (by simp)
    · intro h; subst h; exact hat (by simp [hbc])
    · intro h; subst h; exact hat (by simp [hbd])
    · intro h; subst h; exact hat (by simp [hbe])
  · rintro ⟨a, b, c, d, e, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde, rfl⟩
    simp [hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

lemma eq_five_prime_pows_of_card_eq_five {m : ℕ} (hm : m ≠ 0)
    (h : m.primeFactors.card = 5) :
    ∃ p q r s t : ℕ, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ t ∧
      q ≠ r ∧ q ≠ s ∧ q ≠ t ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t ∧
      p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ t.Prime ∧
      m.primeFactors = {p, q, r, s, t} ∧
      m = p ^ m.factorization p * q ^ m.factorization q *
        r ^ m.factorization r * s ^ m.factorization s *
        t ^ m.factorization t := by
  obtain ⟨p, q, r, s, t, hpq, hpr, hps, hpt, hqr, hqs, hqt, hrs, hrt, hst, hs⟩ :=
    card_eq_five.mp h
  have hp : p.Prime := prime_of_mem_primeFactors (by rw [hs]; simp)
  have hq : q.Prime := prime_of_mem_primeFactors (by rw [hs]; simp [hpq])
  have hr : r.Prime := prime_of_mem_primeFactors (by rw [hs]; simp [hpr, hqr])
  have hss : s.Prime := prime_of_mem_primeFactors (by rw [hs]; simp [hps, hqs, hrs])
  have ht : t.Prime := prime_of_mem_primeFactors (by rw [hs]; simp [hpt, hqt, hrt, hst])
  refine ⟨p, q, r, s, t, hpq, hpr, hps, hpt, hqr, hqs, hqt, hrs, hrt, hst,
    hp, hq, hr, hss, ht, hs, ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Finsupp.prod, Nat.support_factorization, hs]
  rw [prod_insert (by simp [hpq, hpr, hps, hpt]),
    prod_insert (by simp [hqr, hqs, hqt]),
    prod_insert (by simp [hrs, hrt]),
    prod_insert (by simp [hst]), prod_singleton]
  ac_rfl

lemma eight_five_f5_f17_f19_gt_two :
    2 < (8 : ℚ) / 5 * fSum 5 * fSum 17 * fSum 19 := by
  rw [fSum_five, fSum_seventeen, fSum_nineteen]; norm_num

lemma eight_five_f5_f17_f29_gt_two :
    2 < (8 : ℚ) / 5 * fSum 5 * fSum 17 * fSum 29 := by
  rw [fSum_five, fSum_seventeen, fSum_twenty_nine]; norm_num

lemma eight_five_f5_f29_f37_f41_gt_two :
    2 < (8 : ℚ) / 5 * fSum 5 * fSum 29 * fSum 37 * fSum 41 := by
  rw [fSum_five, fSum_twenty_nine, fSum_thirty_seven, fSum_forty_one]; norm_num

lemma eight_five_f7_f11_f13_gt_two :
    2 < (8 : ℚ) / 5 * fSum 7 * fSum 11 * fSum 13 := by
  rw [fSum_seven, fSum_eleven, fSum_thirteen]; norm_num

lemma eight_five_f7_f13_f17_gt_two :
    2 < (8 : ℚ) / 5 * fSum 7 * fSum 13 * fSum 17 := by
  rw [fSum_seven, fSum_thirteen, fSum_seventeen]; norm_num

lemma fs138_fsq13_fsq17_fsq29_fsq37_lt_two :
    (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (17 ^ 2) * fSum (29 ^ 2) *
      fSum (37 ^ 2) < 2 := by
  rw [fSum_thirteen_sq, fSum_seventeen_sq, fSum_twenty_nine_sq, fSum_thirty_seven_sq]
  norm_num

lemma fs4017_fsq11_fsq13_fsq17_lt_two :
    (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) < 2 := by
  rw [fSum_eleven_sq, fSum_thirteen_sq, fSum_seventeen_sq]; norm_num

lemma fs138_f9_f5sq_f13sq_f17sq_lt_three :
    (13 : ℚ) / 8 * fSum (3 ^ 2) * fSum (5 ^ 2) * fSum (13 ^ 2) *
      fSum (17 ^ 2) < 3 := by
  rw [fSum_nine, fSum_five_sq, fSum_thirteen_sq, fSum_seventeen_sq]; norm_num

lemma fs4017_fsq5_fsq13_fsq17_fsq29_fsq37_lt_three :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) *
      fSum (29 ^ 2) * fSum (37 ^ 2) < 3 := by
  rw [fSum_five_sq, fSum_thirteen_sq, fSum_seventeen_sq, fSum_twenty_nine_sq,
    fSum_thirty_seven_sq]; norm_num

lemma fs4017_fsq13_fsq17_fsq29_fsq37_fsq41_lt_two :
    (4017 : ℚ) / 2500 * fSum (13 ^ 2) * fSum (17 ^ 2) * fSum (29 ^ 2) *
      fSum (37 ^ 2) * fSum (41 ^ 2) < 2 := by
  rw [fSum_thirteen_sq, fSum_seventeen_sq, fSum_twenty_nine_sq, fSum_thirty_seven_sq,
    fSum_forty_one_sq]; norm_num

lemma fs138_fsq11_fsq5_fsq13_fsq17_lt_three :
    (13 : ℚ) / 8 * fSum (11 ^ 2) * fSum (5 ^ 2) * fSum (13 ^ 2) *
      fSum (17 ^ 2) < 3 := by
  rw [fSum_eleven_sq, fSum_five_sq, fSum_thirteen_sq, fSum_seventeen_sq]; norm_num

lemma ge21_no_five_three_k_le_two_lt_two {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp11 : 11 ≤ p) (hq13 : 13 ≤ q) (hr17 : 17 ≤ r)
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hple := fSum_le_sq_of_exp_le_two hp hkp
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hrle := fSum_le_sq_of_exp_le_two hr hkr
  have hps := fSum_prime_sq_anti (by decide : Nat.Prime 11) hp hp11
  have hqs := fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
  have hrs := fSum_prime_sq_anti (by decide : Nat.Prime 17) hr hr17
  have hC : fSum (p ^ kp) ≤ fSum (11 ^ 2) := le_trans hple hps
  have hD : fSum (q ^ kq) ≤ fSum (13 ^ 2) := le_trans hqle hqs
  have hE : fSum (r ^ kr) ≤ fSum (17 ^ 2) := le_trans hrle hrs
  have hppos := fSum_pos (pow_ne_zero kp hp.ne_zero)
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ kp) < (4017 : ℚ) / 2500 * fSum (11 ^ 2) :=
    mul_lt_mul h2b hC hppos (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h1 hD hqpos (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (11 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) :=
    mul_lt_mul h2 hE hrpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (11 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  exact h3.trans fs4017_fsq11_fsq13_fsq17_lt_two

lemma fs4017_13_12_f17sq_f29sq_lt_two :
    (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) * fSum (17 ^ 2) * fSum (29 ^ 2) < 2 := by
  rw [fSum_seventeen_sq, fSum_twenty_nine_sq]; norm_num

lemma ge21_no_five_one_high_two_le2_lt_two {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp13 : 13 ≤ p) (hq17 : 17 ≤ q) (hr29 : 29 ≤ r)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hσ := fSum_prime_pow_lt_geom (l := kp) hp
  have hpge : (13 : ℚ) ≤ p := by exact_mod_cast hp13
  have hq1Q : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hgeom : (p : ℚ) / (p - 1) ≤ (13 : ℚ) / 12 := by
    have hden : (0 : ℚ) < p - 1 := sub_pos.mpr hq1Q
    have hden13 : (0 : ℚ) < (13 : ℚ) - 1 := by norm_num
    rw [show (13 : ℚ) / 12 = (13 : ℚ) / (13 - 1) by norm_num]
    rw [div_le_div_iff₀ hden hden13]
    nlinarith
  have hC : fSum (p ^ kp) < (13 : ℚ) / 12 := hσ.trans_le hgeom
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hrle := fSum_le_sq_of_exp_le_two hr hkr
  have hqs := fSum_prime_sq_anti (by decide : Nat.Prime 17) hq hq17
  have hrs := fSum_prime_sq_anti (by decide : Nat.Prime 29) hr hr29
  have hD : fSum (q ^ kq) ≤ fSum (17 ^ 2) := le_trans hqle hqs
  have hE : fSum (r ^ kr) ≤ fSum (29 ^ 2) := le_trans hrle hrs
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hppos := fSum_pos (pow_ne_zero kp hp.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ kp) < (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) :=
    mul_lt_mul h2b hC.le hppos (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) * fSum (17 ^ 2) :=
    mul_lt_mul h1 hD hqpos (mul_nonneg (by norm_num) (by norm_num))
  have h3 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) * fSum (17 ^ 2) * fSum (29 ^ 2) :=
    mul_lt_mul h2 hE hrpos (mul_nonneg (mul_nonneg (by norm_num) (by norm_num))
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
  exact h3.trans fs4017_13_12_f17sq_f29sq_lt_two

lemma ge21_has_five_thirteen_any_gt_two {a kp kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) * fSum (r ^ kr) :=
  ge21_five_thirteen_third_gt_two ha hr hpk hqk hrk

lemma ge21_has_five_seven_any_gt_two {a kp kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (7 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_seven_gt_two ha hpk hqk
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (7 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (7 : ℕ) ≠ 0)))
  nlinarith

lemma ge21_has_five_eleven_any_gt_two {a kp kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (11 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_eleven_gt_two ha hpk hqk
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (11 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (11 : ℕ) ≠ 0)))
  nlinarith

lemma prime_ge_seven_of_ge_five_ne5 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hne : p ≠ 5) :
    7 ≤ p := by
  have : p ≠ 6 := fun h => (by
    have : ¬ Nat.Prime 6 := Nat.not_prime_of_mul_eq (by norm_num : (2 : ℕ) * 3 = 6)
      (by decide) (by decide)
    exact this (h ▸ hp))
  omega

lemma prime_ge_eleven_of_ge_seven_ne7 {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hne : p ≠ 7) :
    11 ≤ p := prime_ge_eleven_of_ge_seven_ne hp h7 hne

lemma fSum_three_pow_six : fSum (3 ^ 6) = (656558503 : ℚ) / 481400920 := by
  rw [fSum_prime_pow Nat.prime_three, sum_range_succ, sum_range_succ, sum_range_succ,
    sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one]
  rw [pow_zero, sigma_one, pow_one, sigma_prime Nat.prime_three]
  rw [sigma_three_pow 2, sigma_three_pow 3, sigma_three_pow 4,
    sigma_three_pow 5, sigma_three_pow 6]
  norm_num

lemma fs4017_f36_f5sq_f13sq_lt_three :
    (4017 : ℚ) / 2500 * fSum (3 ^ 6) * fSum (5 ^ 2) * fSum (13 ^ 2) < 3 := by
  rw [fSum_three_pow_six, fSum_five_sq, fSum_thirteen_sq]; norm_num

lemma fs4017_f9_geom5_f13sq_lt_three :
    (4017 : ℚ) / 2500 * fSum (3 ^ 2) * ((5 : ℚ) / 4) * fSum (13 ^ 2) < 3 := by
  rw [fSum_nine, fSum_thirteen_sq]; norm_num

lemma fs4017_f9_f11sq_f5sq_lt_three :
    (4017 : ℚ) / 2500 * fSum (3 ^ 2) * fSum (11 ^ 2) * fSum (5 ^ 2) < 3 := by
  rw [fSum_nine, fSum_eleven_sq, fSum_five_sq]; norm_num

/-- `3^{k≤6}` times two `1 (mod 4)` prime powers of exponent `≤ 2` is `< 3`. -/
lemma ge21_three_le6_two_vneg1_lt_three {a k p l q s : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq13 : 13 ≤ q)
    (hk6 : k ≤ 6) (hl2 : l ≤ 2) (hs2 : s ≤ 2) :
    fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) < 3 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have h3le : fSum (3 ^ k) ≤ fSum (3 ^ 6) :=
    fSum_le_of_exp_ge Nat.prime_three hk6
  have hple : fSum (p ^ l) ≤ fSum (p ^ 2) :=
    fSum_le_of_exp_ge hp hl2
  have hqle : fSum (q ^ s) ≤ fSum (q ^ 2) :=
    fSum_le_of_exp_ge hq hs2
  have hps : fSum (p ^ 2) ≤ fSum (5 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 5) hp hp5
  have hqs : fSum (q ^ 2) ≤ fSum (13 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
  have hC : fSum (p ^ l) ≤ fSum (5 ^ 2) := le_trans hple hps
  have hD : fSum (q ^ s) ≤ fSum (13 ^ 2) := le_trans hqle hqs
  have hp3 := fSum_pos (pow_ne_zero k (by decide : (3 : ℕ) ≠ 0))
  have hpp := fSum_pos (pow_ne_zero l hp.ne_zero)
  have hqq := fSum_pos (pow_ne_zero s hq.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (3 ^ k) < (4017 : ℚ) / 2500 * fSum (3 ^ 6) :=
    mul_lt_mul h2b h3le hp3 (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) <
      (4017 : ℚ) / 2500 * fSum (3 ^ 6) * fSum (5 ^ 2) :=
    mul_lt_mul h1 hC hpp (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 6 (by decide : (3 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) <
      (4017 : ℚ) / 2500 * fSum (3 ^ 6) * fSum (5 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h2 hD hqq (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 6 (by decide : (3 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  exact h3.trans fs4017_f36_f5sq_f13sq_lt_three

lemma fs4017_f9_geom7_f5sq_lt_three :
    (4017 : ℚ) / 2500 * fSum (3 ^ 2) * ((7 : ℚ) / 6) * fSum (5 ^ 2) < 3 := by
  rw [fSum_nine, fSum_five_sq]; norm_num

/-- Geom bound `p/(p-1) ≤ n/(n-1)` for primes `p ≥ n ≥ 2`. -/
lemma geom_le_of_prime_ge {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hpn : n ≤ p) :
    (p : ℚ) / (p - 1) ≤ (n : ℚ) / (n - 1) := by
  have hp1Q : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hn1 : (1 : ℕ) < n := by omega
  have hn1Q : (1 : ℚ) < n := by exact_mod_cast hn1
  have hden : (0 : ℚ) < p - 1 := sub_pos.mpr hp1Q
  have hdenn : (0 : ℚ) < (n : ℚ) - 1 := sub_pos.mpr hn1Q
  rw [div_le_div_iff₀ hden hdenn]
  nlinarith [show (n : ℚ) ≤ p by exact_mod_cast hpn]

/-- `3^{k≤2}` times an extra prime power `p^l` (`p≥5`) and a `1 (mod 4)` factor `q^s`. -/
lemma ge21_three_le2_extra_vneg1_lt_three {a k p l q s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp5 : 5 ≤ p) (hq1 : q ≡ 1 [MOD 4])
    (hk2 : k ≤ 2) (hs2 : s ≤ 2) :
    fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) < 3 := by
  have hq5 : 5 ≤ q := five_le_of_mod4_one hq hq1
  have h2b := fSum_two_pow_lt_4017_2500 a
  have h3le : fSum (3 ^ k) ≤ fSum (3 ^ 2) :=
    fSum_le_of_exp_ge Nat.prime_three hk2
  have hp3 := fSum_pos (pow_ne_zero k (by decide : (3 : ℕ) ≠ 0))
  have hpp := fSum_pos (pow_ne_zero l hp.ne_zero)
  have hqq := fSum_pos (pow_ne_zero s hq.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (3 ^ k) < (4017 : ℚ) / 2500 * fSum (3 ^ 2) :=
    mul_lt_mul h2b h3le hp3 (by norm_num)
  have hσp := fSum_prime_pow_lt_geom (l := l) hp
  cases eq_or_ne q 5 with
  | inl hq5eq =>
    subst hq5eq
    have hp7 : 7 ≤ p := prime_ge_seven_of_ge_five_ne5 hp hp5 hpq
    have hgeom : (p : ℚ) / (p - 1) ≤ (7 : ℚ) / 6 := by
      have := geom_le_of_prime_ge hp (by decide : 2 ≤ 7) hp7
      convert this using 1
      norm_num
    have hC : fSum (p ^ l) < (7 : ℚ) / 6 := hσp.trans_le hgeom
    have hD : fSum (5 ^ s) ≤ fSum (5 ^ 2) :=
      fSum_le_of_exp_ge (by decide : Nat.Prime 5) hs2
    have h2 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) <
        (4017 : ℚ) / 2500 * fSum (3 ^ 2) * ((7 : ℚ) / 6) :=
      mul_lt_mul h1 hC.le hpp (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (3 : ℕ) ≠ 0))).le)
    have h3 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (5 ^ s) <
        (4017 : ℚ) / 2500 * fSum (3 ^ 2) * ((7 : ℚ) / 6) * fSum (5 ^ 2) :=
      mul_lt_mul h2 hD hqq (mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (3 : ℕ) ≠ 0))).le) (by norm_num))
    exact h3.trans fs4017_f9_geom7_f5sq_lt_three
  | inr hqne5 =>
    have hq13 : 13 ≤ q := by
      rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
      · exact (hqne5 h5).elim
      · exact h13.symm ▸ le_rfl
      · omega
      · omega
    have hgeom : (p : ℚ) / (p - 1) ≤ (5 : ℚ) / 4 := by
      have := geom_le_of_prime_ge hp (by decide : 2 ≤ 5) hp5
      convert this using 1
      norm_num
    have hC : fSum (p ^ l) < (5 : ℚ) / 4 := hσp.trans_le hgeom
    have hD : fSum (q ^ s) ≤ fSum (q ^ 2) := fSum_le_of_exp_ge hq hs2
    have hqs : fSum (q ^ 2) ≤ fSum (13 ^ 2) :=
      fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
    have hD' : fSum (q ^ s) ≤ fSum (13 ^ 2) := le_trans hD hqs
    have h2 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) <
        (4017 : ℚ) / 2500 * fSum (3 ^ 2) * ((5 : ℚ) / 4) :=
      mul_lt_mul h1 hC.le hpp (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (3 : ℕ) ≠ 0))).le)
    have h3 : fSum (2 ^ a) * fSum (3 ^ k) * fSum (p ^ l) * fSum (q ^ s) <
        (4017 : ℚ) / 2500 * fSum (3 ^ 2) * ((5 : ℚ) / 4) * fSum (13 ^ 2) :=
      mul_lt_mul h2 hD' hqq (mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (3 : ℕ) ≠ 0))).le) (by norm_num))
    exact h3.trans fs4017_f9_geom5_f13sq_lt_three

lemma v2_eq_neg_two_classification {p k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hk : 1 ≤ k)
    (hv : padicValRat 2 (fSum (p ^ k)) = -2) :
    (p ≡ 3 [MOD 8] ∧ (k = 1 ∨ k = 2)) ∨
    (p ≡ 1 [MOD 4] ∧ 3 ≤ k ∧ k ≤ 6) := by
  haveI := two_fact
  have hform := v2_fSum_eq_one_sub hp hpo hk
  rw [hform] at hv
  rcases odd_mod8 hpo with h1 | h3 | h5 | h7
  · have h14 : p ≡ 1 [MOD 4] := p_mod4_one_of_mod8_one h1
    have hv2p : padicValNat 2 (p + 1) = 1 :=
      padicValNat_two_add_one_of_mod4_one hpo h14
    have hlog : Nat.log 2 (k + 1) = 2 := by omega
    have ⟨hk3, hk6⟩ := exp_mid_of_log_eq_two hk hlog
    exact Or.inr ⟨h14, hk3, hk6⟩
  · have hv2p : padicValNat 2 (p + 1) = 2 :=
      padicValNat_two_add_one_of_mod8_three hpo h3
    have hlog : Nat.log 2 (k + 1) = 1 := by omega
    have hk2 : k ≤ 2 := exp_le_two_of_log_eq_one hk hlog
    exact Or.inl ⟨h3, by omega⟩
  · have h14 : p ≡ 1 [MOD 4] := p_mod4_one_of_mod8_five h5
    have hv2p : padicValNat 2 (p + 1) = 1 :=
      padicValNat_two_add_one_of_mod4_one hpo h14
    have hlog : Nat.log 2 (k + 1) = 2 := by omega
    have ⟨hk3, hk6⟩ := exp_mid_of_log_eq_two hk hlog
    exact Or.inr ⟨h14, hk3, hk6⟩
  · have hvle : padicValRat 2 (fSum (p ^ k)) ≤ -3 :=
      v2_fSum_odd_prime_pow_mod8_seven_small hp hpo h7 hk
    omega

lemma eq_three_or_ge_eleven_of_mod8_three {p : ℕ}
    (hp : p.Prime) (h3 : p ≡ 3 [MOD 8]) :
    p = 3 ∨ 11 ≤ p := by
  have h2 : p ≠ 2 := by
    intro h; have : (2 : ℕ) % 8 = 3 := by simpa [h, Nat.ModEq] using h3
    norm_num at this
  have hp3 : 3 ≤ p := by
    have : 2 ≤ p := hp.two_le
    omega
  by_cases h11 : 11 ≤ p
  · exact Or.inr h11
  · have : p < 11 := by omega
    interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by decide)
    · simp [Nat.ModEq] at h3
    · exact absurd hp (by decide)
    · simp [Nat.ModEq] at h3
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)

/-- Four `1 (mod 4)` prime powers, no factor `5`, all exponents `≤ 2`: product `< 2`. -/
lemma ge21_four_no_five_k_le_two_lt_two {a p kp q kq r kr s ks : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hp13 : 13 ≤ p) (hq17 : 17 ≤ q) (hr29 : 29 ≤ r) (hs37 : 37 ≤ s)
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2)
    (hkr : kr = 1 ∨ kr = 2) (hks : ks = 1 ∨ ks = 2) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) < 2 := by
  have h2b := fSum_two_pow_lt_13_8 a
  have hple := fSum_le_sq_of_exp_le_two hp hkp
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hrle := fSum_le_sq_of_exp_le_two hr hkr
  have hsle := fSum_le_sq_of_exp_le_two hs hks
  have hps := fSum_prime_sq_anti (by decide : Nat.Prime 13) hp hp13
  have hqs := fSum_prime_sq_anti (by decide : Nat.Prime 17) hq hq17
  have hrs := fSum_prime_sq_anti (by decide : Nat.Prime 29) hr hr29
  have hss := fSum_prime_sq_anti (by decide : Nat.Prime 37) hs hs37
  have hC : fSum (p ^ kp) ≤ fSum (13 ^ 2) := le_trans hple hps
  have hD : fSum (q ^ kq) ≤ fSum (17 ^ 2) := le_trans hqle hqs
  have hE : fSum (r ^ kr) ≤ fSum (29 ^ 2) := le_trans hrle hrs
  have hF : fSum (s ^ ks) ≤ fSum (37 ^ 2) := le_trans hsle hss
  have hppos := fSum_pos (pow_ne_zero kp hp.ne_zero)
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hspos := fSum_pos (pow_ne_zero ks hs.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ kp) < (13 : ℚ) / 8 * fSum (13 ^ 2) :=
    mul_lt_mul h2b hC hppos (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (17 ^ 2) :=
    mul_lt_mul h1 hD hqpos (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (17 ^ 2) * fSum (29 ^ 2) :=
    mul_lt_mul h2 hE hrpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
  have h4 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) <
      (13 : ℚ) / 8 * fSum (13 ^ 2) * fSum (17 ^ 2) * fSum (29 ^ 2) *
        fSum (37 ^ 2) :=
    mul_lt_mul h3 hF hspos (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0))).le)
  exact h4.trans fs138_fsq13_fsq17_fsq29_fsq37_lt_two

lemma ge21_four_has_five_thirteen_gt_two {a kp kq r kr s ks : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hs : s.Prime)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) (hsk : 1 ≤ ks) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) := by
  have h0 := ge21_five_thirteen_gt_two ha hpk hqk
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have h2 : 1 < fSum (s ^ ks) := fSum_gt_one_of_prime_pow hs hsk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (13 : ℕ) ≠ 0)))
  have hmid : 2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) * fSum (r ^ kr) := by
    nlinarith
  have hpos2 : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) * fSum (r ^ kr) :=
    mul_pos hpos (fSum_pos (pow_ne_zero kr hr.ne_zero))
  nlinarith

/-- Five `1 (mod 4)` squares starting at `5`: product `< 3`. -/
lemma ge21_five_primes_k_le_two_lt_three {a p kp q kq r kr s ks t kt : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hp5 : 5 ≤ p) (hq13 : 13 ≤ q) (hr17 : 17 ≤ r) (hs29 : 29 ≤ s) (ht37 : 37 ≤ t)
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2)
    (hkr : kr = 1 ∨ kr = 2) (hks : ks = 1 ∨ ks = 2) (hkt : kt = 1 ∨ kt = 2) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) * fSum (t ^ kt) < 3 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hple := fSum_le_sq_of_exp_le_two hp hkp
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hrle := fSum_le_sq_of_exp_le_two hr hkr
  have hsle := fSum_le_sq_of_exp_le_two hs hks
  have htle := fSum_le_sq_of_exp_le_two ht hkt
  have hps := fSum_prime_sq_anti (by decide : Nat.Prime 5) hp hp5
  have hqs := fSum_prime_sq_anti (by decide : Nat.Prime 13) hq hq13
  have hrs := fSum_prime_sq_anti (by decide : Nat.Prime 17) hr hr17
  have hss := fSum_prime_sq_anti (by decide : Nat.Prime 29) hs hs29
  have hts := fSum_prime_sq_anti (by decide : Nat.Prime 37) ht ht37
  have hC : fSum (p ^ kp) ≤ fSum (5 ^ 2) := le_trans hple hps
  have hD : fSum (q ^ kq) ≤ fSum (13 ^ 2) := le_trans hqle hqs
  have hE : fSum (r ^ kr) ≤ fSum (17 ^ 2) := le_trans hrle hrs
  have hF : fSum (s ^ ks) ≤ fSum (29 ^ 2) := le_trans hsle hss
  have hG : fSum (t ^ kt) ≤ fSum (37 ^ 2) := le_trans htle hts
  have hppos := fSum_pos (pow_ne_zero kp hp.ne_zero)
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hspos := fSum_pos (pow_ne_zero ks hs.ne_zero)
  have htpos := fSum_pos (pow_ne_zero kt ht.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ kp) < (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
    mul_lt_mul h2b hC hppos (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (13 ^ 2) :=
    mul_lt_mul h1 hD hqpos (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) :=
    mul_lt_mul h2 hE hrpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  have h4 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) *
        fSum (29 ^ 2) :=
    mul_lt_mul h3 hF hspos (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
  have h5 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) * fSum (t ^ kt) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (13 ^ 2) * fSum (17 ^ 2) *
        fSum (29 ^ 2) * fSum (37 ^ 2) :=
    mul_lt_mul h4 hG htpos (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 (by decide : (29 : ℕ) ≠ 0))).le)
  exact h5.trans fs4017_fsq5_fsq13_fsq17_fsq29_fsq37_lt_three

/-- `3^{kp}` together with two other odd primes, `v₂` sum `= -5`, product `< 3`. -/
lemma ge21_three_first_v2m_neg_five_lt_three
    {a kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r)
    (hqo : Odd q) (hro : Odd r)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hq5 : 5 ≤ q) (hr5 : 5 ≤ r)
    (hvsum : padicValRat 2 (fSum (3 ^ kp)) +
             padicValRat 2 (fSum (q ^ kq)) +
             padicValRat 2 (fSum (r ^ kr)) = -5) :
    fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) < 3 := by
  haveI := two_fact
  have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
  have hv2r : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
  have hform3 := v2_fSum_eq_one_sub Nat.prime_three (by decide : Odd 3) hpk
  have hv34 : padicValNat 2 (3 + 1) = 2 := padicValNat_two_four
  have hlogle : Nat.log 2 (kp + 1) ≤ 2 := by
    have : padicValRat 2 (fSum (3 ^ kp)) ≥ -3 := by omega
    rw [hform3] at this
    omega
  have hlogpos : 1 ≤ Nat.log 2 (kp + 1) := Nat.log_pos (by decide) (by omega)
  have hk6 : kp ≤ 6 := by
    have : Nat.log 2 (kp + 1) = 1 ∨ Nat.log 2 (kp + 1) = 2 := by omega
    rcases this with h | h
    · exact (exp_le_two_of_log_eq_one hpk h).trans (by decide : (2 : ℕ) ≤ 6)
    · exact (exp_mid_of_log_eq_two hpk h).2
  by_cases hk2 : kp ≤ 2
  · have hv3eq : padicValRat 2 (fSum (3 ^ kp)) = -2 := by
      rw [hform3, hv34]
      have hlog : Nat.log 2 (kp + 1) = 1 :=
        log_two_eq_one_of_mem_two_three (by omega) (by omega)
      omega
    by_cases hqneg2 : padicValRat 2 (fSum (q ^ kq)) ≤ -2
    · have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -2 := by omega
      have hvreq : padicValRat 2 (fSum (r ^ kr)) = -1 := by omega
      have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hvreq
      have hkr12 := exp_le_two_of_v2_eq_neg_one hr hro hrk hvreq
      exact ge21_three_le2_extra_vneg1_lt_three hq hr hqr hq5 hr1 hk2 hkr12
    · have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by omega
      have hvreq : padicValRat 2 (fSum (r ^ kr)) = -2 := by omega
      have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hvqeq
      have hkq12 := exp_le_two_of_v2_eq_neg_one hq hqo hqk hvqeq
      have hswap :
          fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
          fSum (2 ^ a) * fSum (3 ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
      rw [hswap]
      exact ge21_three_le2_extra_vneg1_lt_three hr hq hqr.symm hr5 hq1 hk2 hkq12
  · have hv3eq : padicValRat 2 (fSum (3 ^ kp)) = -3 := by
      rw [hform3, hv34]
      have hlog : Nat.log 2 (kp + 1) = 2 := by
        have : 2 ≤ Nat.log 2 (kp + 1) := log_two_of_ge_four (by omega)
        omega
      omega
    have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by omega
    have hvreq : padicValRat 2 (fSum (r ^ kr)) = -1 := by omega
    have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hvqeq
    have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hvreq
    have hkq12 := exp_le_two_of_v2_eq_neg_one hq hqo hqk hvqeq
    have hkr12 := exp_le_two_of_v2_eq_neg_one hr hro hrk hvreq
    cases le_total q r with
    | inl hle =>
      have hr13 : 13 ≤ r := by
        have : r ≠ 5 := by
          intro h
          have : q = 5 := by
            have : q ≤ 5 := h ▸ hle
            have : 5 ≤ q := five_le_of_mod4_one hq hq1
            omega
          exact hqr (this.trans h.symm)
        rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
        · exact (this h5).elim
        · exact h13.symm ▸ le_rfl
        · omega
        · omega
      exact ge21_three_le6_two_vneg1_lt_three hq hr hq5 hr13 hk6 hkq12 hkr12
    | inr hle =>
      have hq13 : 13 ≤ q := by
        have : q ≠ 5 := by
          intro h
          have : r = 5 := by
            have : r ≤ 5 := h ▸ hle
            have : 5 ≤ r := five_le_of_mod4_one hr hr1
            omega
          exact hqr (h.trans this.symm)
        rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
        · exact (this h5).elim
        · exact h13.symm ▸ le_rfl
        · omega
        · omega
      have hswap :
          fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
          fSum (2 ^ a) * fSum (3 ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
      rw [hswap]
      exact ge21_three_le6_two_vneg1_lt_three hr hq hr5 hq13 hk6 hkr12 hkq12

lemma ge21_has_three_v2m_neg_five_lt_three
    {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpo : Odd p) (hqo : Odd q) (hro : Odd r)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hhas3 : p = 3 ∨ q = 3 ∨ r = 3)
    (hvsum : padicValRat 2 (fSum (p ^ kp)) +
             padicValRat 2 (fSum (q ^ kq)) +
             padicValRat 2 (fSum (r ^ kr)) = -5) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) < 3 := by
  have hp3or := odd_prime_eq_three_or_ge_five hp hpo
  have hq3or := odd_prime_eq_three_or_ge_five hq hqo
  have hr3or := odd_prime_eq_three_or_ge_five hr hro
  rcases hhas3 with hp3 | hq3 | hr3
  · subst hp3
    have hq5 : 5 ≤ q := by
      rcases hq3or with hq3' | hq5
      · exact (hpq hq3'.symm).elim
      · exact hq5
    have hr5 : 5 ≤ r := by
      rcases hr3or with hr3' | hr5
      · exact (hpr hr3'.symm).elim
      · exact hr5
    exact ge21_three_first_v2m_neg_five_lt_three ha hq hr hqr hqo hro
      hpk hqk hrk hq5 hr5 hvsum
  · subst hq3
    have hp5 : 5 ≤ p := by
      rcases hp3or with hp3' | hp5
      · exact (hpq hp3').elim
      · exact hp5
    have hr5 : 5 ≤ r := by
      rcases hr3or with hr3' | hr5
      · exact (hqr hr3'.symm).elim
      · exact hr5
    have hswap :
        fSum (2 ^ a) * fSum (p ^ kp) * fSum (3 ^ kq) * fSum (r ^ kr) =
        fSum (2 ^ a) * fSum (3 ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) := by ring
    rw [hswap]
    exact ge21_three_first_v2m_neg_five_lt_three ha hp hr hpr hpo hro
      hqk hpk hrk hp5 hr5 (by linarith)
  · subst hr3
    have hp5 : 5 ≤ p := by
      rcases hp3or with hp3' | hp5
      · exact (hpr hp3').elim
      · exact hp5
    have hq5 : 5 ≤ q := by
      rcases hq3or with hq3' | hq5
      · exact (hqr hq3').elim
      · exact hq5
    have hswap :
        fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (3 ^ kr) =
        fSum (2 ^ a) * fSum (3 ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
    rw [hswap]
    exact ge21_three_first_v2m_neg_five_lt_three ha hp hq hpq hpo hqo
      hrk hpk hqk hp5 hq5 (by linarith)

lemma one_mod4_ge13_of_ne5 {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (hne : q ≠ 5) : 13 ≤ q := by
  rcases prime_one_mod_four_cases hq h1 with h5 | h13 | h17 | hge
  · exact (hne h5).elim
  · exact h13.symm ▸ le_rfl
  · omega
  · omega

lemma one_mod4_ge17_of_ne5_ne13 {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (hne5 : q ≠ 5) (hne13 : q ≠ 13) : 17 ≤ q := by
  have hq13 := one_mod4_ge13_of_ne5 hq h1 hne5
  exact prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hne13

lemma one_mod4_ge29_of_ge17_ne17 {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (hq17 : 17 ≤ q) (hne : q ≠ 17) : 29 ≤ q := by
  rcases prime_eq_seventeen_or_ge_twentynine_of_one_mod4 hq h1 hq17 with h | h
  · exact (hne h).elim
  · exact h

lemma fs4017_f5sq_geom13_pow4_lt_three :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) ^ 4 < 3 := by
  rw [fSum_five_sq]; norm_num

lemma fs4017_geom13_pow5_lt_three :
    (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 5 < 3 := by norm_num

lemma fSum_pow_lt_geom_of_ge {p k n : ℕ}
    (hp : p.Prime) (hn : 2 ≤ n) (hpn : n ≤ p) :
    fSum (p ^ k) < (n : ℚ) / (n - 1) :=
  (fSum_prime_pow_lt_geom hp).trans_le (geom_le_of_prime_ge hp hn hpn)

lemma fSum_lt_geom13 {p k : ℕ} (hp : p.Prime) (h : 13 ≤ p) :
    fSum (p ^ k) < (13 : ℚ) / 12 := by
  have := fSum_pow_lt_geom_of_ge (n := 13) hp (by decide) h (k := k)
  convert this using 1
  norm_num

/-- Five prime powers, one of them `5^{≤2}` and the others `≥ 13`: product `< 3`. -/
lemma ge21_five_has5_rest_ge13_lt_three {a kp q kq r kr s ks t kt : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hq13 : 13 ≤ q) (hr13 : 13 ≤ r) (hs13 : 13 ≤ s) (ht13 : 13 ≤ t)
    (hkp : kp = 1 ∨ kp = 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) * fSum (t ^ kt) < 3 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have h5le : fSum (5 ^ kp) ≤ fSum (5 ^ 2) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) (by omega)
  have hqg := fSum_lt_geom13 hq hq13 (k := kq)
  have hrg := fSum_lt_geom13 hr hr13 (k := kr)
  have hsg := fSum_lt_geom13 hs hs13 (k := ks)
  have htg := fSum_lt_geom13 ht ht13 (k := kt)
  have h5p := fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hspos := fSum_pos (pow_ne_zero ks hs.ne_zero)
  have htpos := fSum_pos (pow_ne_zero kt ht.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) < (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
    mul_lt_mul h2b h5le h5p (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) :=
    mul_lt_mul h1 hqg.le hqpos (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
  have h3 : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) * ((13 : ℚ) / 12) :=
    mul_lt_mul h2 hrg.le hrpos (by
      refine mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le) ?_
      norm_num)
  have h4 : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) ^ 3 := by
    have : (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) *
        ((13 : ℚ) / 12) * ((13 : ℚ) / 12) =
        (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) ^ 3 := by ring
    have h := mul_lt_mul h3 hsg.le hspos (by
      refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le) (by norm_num))
        (by norm_num))
    rwa [this] at h
  have h5 : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) * fSum (t ^ kt) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) ^ 4 := by
    have : (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) ^ 3 *
        ((13 : ℚ) / 12) =
        (4017 : ℚ) / 2500 * fSum (5 ^ 2) * ((13 : ℚ) / 12) ^ 4 := by ring
    have h := mul_lt_mul h4 htg.le htpos (mul_nonneg
      (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
      (pow_nonneg (by norm_num) 3))
    rwa [this] at h
  exact h5.trans fs4017_f5sq_geom13_pow4_lt_three

/-- Five prime powers all `≥ 13`: product `< 3`. -/
lemma ge21_five_all_ge13_lt_three {a p kp q kq r kr s ks t kt : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hp13 : 13 ≤ p) (hq13 : 13 ≤ q) (hr13 : 13 ≤ r) (hs13 : 13 ≤ s) (ht13 : 13 ≤ t) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) * fSum (t ^ kt) < 3 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hpg := fSum_lt_geom13 hp hp13 (k := kp)
  have hqg := fSum_lt_geom13 hq hq13 (k := kq)
  have hrg := fSum_lt_geom13 hr hr13 (k := kr)
  have hsg := fSum_lt_geom13 hs hs13 (k := ks)
  have htg := fSum_lt_geom13 ht ht13 (k := kt)
  have hppos := fSum_pos (pow_ne_zero kp hp.ne_zero)
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hspos := fSum_pos (pow_ne_zero ks hs.ne_zero)
  have htpos := fSum_pos (pow_ne_zero kt ht.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ kp) < (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) :=
    mul_lt_mul h2b hpg.le hppos (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 2 := by
    have : (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) * ((13 : ℚ) / 12) =
        (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 2 := by ring
    have h := mul_lt_mul h1 hqg.le hqpos (mul_nonneg (by norm_num) (by norm_num))
    rwa [this] at h
  have h3 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 3 := by
    have : (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 2 * ((13 : ℚ) / 12) =
        (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 3 := by ring
    have h := mul_lt_mul h2 hrg.le hrpos
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 2))
    rwa [this] at h
  have h4 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 4 := by
    have : (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 3 * ((13 : ℚ) / 12) =
        (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 4 := by ring
    have h := mul_lt_mul h3 hsg.le hspos
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 3))
    rwa [this] at h
  have h5 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
      fSum (s ^ ks) * fSum (t ^ kt) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 5 := by
    have : (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 4 * ((13 : ℚ) / 12) =
        (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) ^ 5 := by ring
    have h := mul_lt_mul h4 htg.le htpos
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 4))
    rwa [this] at h
  exact h5.trans fs4017_geom13_pow5_lt_three

lemma fSum_mod64_twentyone_omega_five_not_int
    {a m : ℕ} (ha21 : a ≡ 21 [MOD 64])
    (hodd : Odd m) (hm : 1 < m) (hω : m.primeFactors.card = 5)
    (hnonneg : ¬ padicValRat 2 (fSum (2 ^ a) * fSum m) < 0) :
    (fSum (2 ^ a) * fSum m).den ≠ 1 := by
  haveI := two_fact
  have hm0 : m ≠ 0 := by omega
  have ha21n : 21 ≤ a := by
    have : a % 64 = 21 := by simpa [Nat.ModEq] using ha21
    omega
  have hv2a : padicValRat 2 (fSum (2 ^ a)) = 5 :=
    v2_fSum_two_pow_mod64_twentyone ha21
  have hv2prod_eq : padicValRat 2 (fSum (2 ^ a) * fSum m) =
      padicValRat 2 (fSum (2 ^ a)) + padicValRat 2 (fSum m) :=
    padicValRat.mul (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
      (fSum_ne_zero hm0)
  have hgt : 1 < fSum (2 ^ a) * fSum m := by
    have h1 := fSum_two_pow_gt_one (by omega : 1 ≤ a)
    have h2 : 1 < fSum m := fSum_gt_one hm
    nlinarith [fSum_pos (pow_ne_zero a two_ne_zero), fSum_pos hm0]
  have h2n : 2 ∉ m.primeFactors := by
    intro h
    exact Nat.not_even_iff_odd.mpr hodd
      (even_iff_two_dvd.mpr (dvd_of_mem_primeFactors h))
  obtain ⟨p, q, r, s, t, hpq, hpr, hps, hpt, hqr, hqs, hqt, hrs, hrt, hst,
      hp, hq, hr, hss, ht, hset, hm_eq⟩ :=
    eq_five_prime_pows_of_card_eq_five hm0 hω
  set kp := m.factorization p
  set kq := m.factorization q
  set kr := m.factorization r
  set ks := m.factorization s
  set kt := m.factorization t
  have hpk : 1 ≤ kp := by
    have : p ∈ m.primeFactors := by simp [hset]
    exact factorization_pos_of_mem_primeFactors this
  have hqk : 1 ≤ kq := by
    have : q ∈ m.primeFactors := by simp [hset]
    exact factorization_pos_of_mem_primeFactors this
  have hrk : 1 ≤ kr := by
    have : r ∈ m.primeFactors := by simp [hset]
    exact factorization_pos_of_mem_primeFactors this
  have hsk : 1 ≤ ks := by
    have : s ∈ m.primeFactors := by simp [hset]
    exact factorization_pos_of_mem_primeFactors this
  have htk : 1 ≤ kt := by
    have : t ∈ m.primeFactors := by simp [hset]
    exact factorization_pos_of_mem_primeFactors this
  have hpo : Odd p := hp.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
  have hqo : Odd q := hq.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
  have hro : Odd r := hr.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
  have hso : Odd s := hss.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
  have hto : Odd t := ht.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
  have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) := Nat.coprime_pow_primes kp kq hp hq hpq
  have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
    refine Nat.Coprime.mul_left ?_ ?_
    · exact Nat.coprime_pow_primes kp kr hp hr hpr
    · exact Nat.coprime_pow_primes kq kr hq hr hqr
  have hcop3 : Nat.Coprime (p ^ kp * q ^ kq * r ^ kr) (s ^ ks) := by
    refine Nat.Coprime.mul_left ?_ ?_
    · refine Nat.Coprime.mul_left ?_ ?_
      · exact Nat.coprime_pow_primes kp ks hp hss hps
      · exact Nat.coprime_pow_primes kq ks hq hss hqs
    · exact Nat.coprime_pow_primes kr ks hr hss hrs
  have hcop4 : Nat.Coprime (p ^ kp * q ^ kq * r ^ kr * s ^ ks) (t ^ kt) := by
    refine Nat.Coprime.mul_left ?_ ?_
    · refine Nat.Coprime.mul_left ?_ ?_
      · refine Nat.Coprime.mul_left ?_ ?_
        · exact Nat.coprime_pow_primes kp kt hp ht hpt
        · exact Nat.coprime_pow_primes kq kt hq ht hqt
      · exact Nat.coprime_pow_primes kr kt hr ht hrt
    · exact Nat.coprime_pow_primes ks kt hss ht hst
  have hfm : fSum m =
      fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) * fSum (s ^ ks) *
        fSum (t ^ kt) := by
    rw [hm_eq, fSum_mul hcop4, fSum_mul hcop3, fSum_mul hcop2, fSum_mul hcop1]
  have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
  have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
  have hv2r : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
  have hv2s : padicValRat 2 (fSum (s ^ ks)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hss hso hsk)
  have hv2t : padicValRat 2 (fSum (t ^ kt)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg ht hto htk)
  have hv2msum : padicValRat 2 (fSum m) =
      padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
        padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) +
        padicValRat 2 (fSum (t ^ kt)) := by
    rw [hfm]
    rw [padicValRat.mul
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
              (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
            (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)))
          (fSum_ne_zero (pow_ne_zero _ hss.ne_zero)))
        (fSum_ne_zero (pow_ne_zero _ ht.ne_zero))]
    rw [padicValRat.mul
        (mul_ne_zero
          (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
            (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
          (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)))
        (fSum_ne_zero (pow_ne_zero _ hss.ne_zero))]
    rw [padicValRat.mul
        (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
          (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
        (fSum_ne_zero (pow_ne_zero _ hr.ne_zero))]
    rw [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
        (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
  have hvle : padicValRat 2 (fSum m) ≤ -5 := by
    rw [hv2msum]; linarith
  have hv2prod : padicValRat 2 (fSum (2 ^ a) * fSum m) =
      5 + padicValRat 2 (fSum m) := by rw [hv2prod_eq, hv2a]
  by_cases hextra : padicValRat 2 (fSum m) ≤ -6
  · have hneg : padicValRat 2 (fSum (2 ^ a) * fSum m) < 0 := by linarith
    exact (hnonneg hneg).elim
  · have hv5 : padicValRat 2 (fSum m) = -5 := by omega
    have hv0 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 0 := by
      rw [hv2prod, hv5]; norm_num
    have hv2peq : padicValRat 2 (fSum (p ^ kp)) = -1 := by
      have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
          padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) +
          padicValRat 2 (fSum (t ^ kt)) = -5 := by rw [← hv2msum, hv5]
      omega
    have hv2qeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by
      have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
          padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) +
          padicValRat 2 (fSum (t ^ kt)) = -5 := by rw [← hv2msum, hv5]
      omega
    have hv2req : padicValRat 2 (fSum (r ^ kr)) = -1 := by
      have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
          padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) +
          padicValRat 2 (fSum (t ^ kt)) = -5 := by rw [← hv2msum, hv5]
      omega
    have hv2seq : padicValRat 2 (fSum (s ^ ks)) = -1 := by
      have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
          padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) +
          padicValRat 2 (fSum (t ^ kt)) = -5 := by rw [← hv2msum, hv5]
      omega
    have hv2teq : padicValRat 2 (fSum (t ^ kt)) = -1 := by
      have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
          padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) +
          padicValRat 2 (fSum (t ^ kt)) = -5 := by rw [← hv2msum, hv5]
      omega
    have hp1 := mod4_one_of_v2_eq_neg_one hp hpo hpk hv2peq
    have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hv2qeq
    have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hv2req
    have hs1 := mod4_one_of_v2_eq_neg_one hss hso hsk hv2seq
    have ht1 := mod4_one_of_v2_eq_neg_one ht hto htk hv2teq
    have hkp12 := exp_le_two_of_v2_eq_neg_one hp hpo hpk hv2peq
    have hkq12 := exp_le_two_of_v2_eq_neg_one hq hqo hqk hv2qeq
    have hkr12 := exp_le_two_of_v2_eq_neg_one hr hro hrk hv2req
    have hks12 := exp_le_two_of_v2_eq_neg_one hss hso hsk hv2seq
    have hkt12 := exp_le_two_of_v2_eq_neg_one ht hto htk hv2teq
    have hkp12' : kp = 1 ∨ kp = 2 := by omega
    have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
      have hassoc :
          fSum (2 ^ a) * fSum m =
            fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
              fSum (s ^ ks) * fSum (t ^ kt) := by rw [hfm]; ring
      rw [hassoc]
      by_cases hhas5 : p = 5 ∨ q = 5 ∨ r = 5 ∨ s = 5 ∨ t = 5
      · -- one of them is 5; the others are ≥ 13
        rcases hhas5 with hp5 | hq5 | hr5 | hs5 | ht5
        · subst hp5
          have hq13 := one_mod4_ge13_of_ne5 hq hq1 hpq.symm
          have hr13 := one_mod4_ge13_of_ne5 hr hr1 hpr.symm
          have hs13 := one_mod4_ge13_of_ne5 hss hs1 hps.symm
          have ht13 := one_mod4_ge13_of_ne5 ht ht1 hpt.symm
          exact ge21_five_has5_rest_ge13_lt_three hq hr hss ht
            hq13 hr13 hs13 ht13 hkp12'
        · subst hq5
          have hp13 := one_mod4_ge13_of_ne5 hp hp1 hpq
          have hr13 := one_mod4_ge13_of_ne5 hr hr1 hqr.symm
          have hs13 := one_mod4_ge13_of_ne5 hss hs1 hqs.symm
          have ht13 := one_mod4_ge13_of_ne5 ht ht1 hqt.symm
          have hswap :
              fSum (2 ^ a) * fSum (p ^ kp) * fSum (5 ^ kq) * fSum (r ^ kr) *
                fSum (s ^ ks) * fSum (t ^ kt) =
              fSum (2 ^ a) * fSum (5 ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) *
                fSum (s ^ ks) * fSum (t ^ kt) := by ring
          rw [hswap]
          exact ge21_five_has5_rest_ge13_lt_three hp hr hss ht
            hp13 hr13 hs13 ht13 (by omega)
        · subst hr5
          have hp13 := one_mod4_ge13_of_ne5 hp hp1 hpr
          have hq13 := one_mod4_ge13_of_ne5 hq hq1 hqr
          have hs13 := one_mod4_ge13_of_ne5 hss hs1 hrs.symm
          have ht13 := one_mod4_ge13_of_ne5 ht ht1 hrt.symm
          have hswap :
              fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (5 ^ kr) *
                fSum (s ^ ks) * fSum (t ^ kt) =
              fSum (2 ^ a) * fSum (5 ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) *
                fSum (s ^ ks) * fSum (t ^ kt) := by ring
          rw [hswap]
          exact ge21_five_has5_rest_ge13_lt_three hp hq hss ht
            hp13 hq13 hs13 ht13 (by omega)
        · subst hs5
          have hp13 := one_mod4_ge13_of_ne5 hp hp1 hps
          have hq13 := one_mod4_ge13_of_ne5 hq hq1 hqs
          have hr13 := one_mod4_ge13_of_ne5 hr hr1 hrs
          have ht13 := one_mod4_ge13_of_ne5 ht ht1 hst.symm
          have hswap :
              fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
                fSum (5 ^ ks) * fSum (t ^ kt) =
              fSum (2 ^ a) * fSum (5 ^ ks) * fSum (p ^ kp) * fSum (q ^ kq) *
                fSum (r ^ kr) * fSum (t ^ kt) := by ring
          rw [hswap]
          exact ge21_five_has5_rest_ge13_lt_three hp hq hr ht
            hp13 hq13 hr13 ht13 (by omega)
        · subst ht5
          have hp13 := one_mod4_ge13_of_ne5 hp hp1 hpt
          have hq13 := one_mod4_ge13_of_ne5 hq hq1 hqt
          have hr13 := one_mod4_ge13_of_ne5 hr hr1 hrt
          have hs13 := one_mod4_ge13_of_ne5 hss hs1 hst
          have hswap :
              fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) *
                fSum (s ^ ks) * fSum (5 ^ kt) =
              fSum (2 ^ a) * fSum (5 ^ kt) * fSum (p ^ kp) * fSum (q ^ kq) *
                fSum (r ^ kr) * fSum (s ^ ks) := by ring
          rw [hswap]
          exact ge21_five_has5_rest_ge13_lt_three hp hq hr hss
            hp13 hq13 hr13 hs13 (by omega)
      · have hp13 := one_mod4_ge13_of_ne5 hp hp1 (by
          intro h; exact hhas5 (Or.inl h))
        have hq13 := one_mod4_ge13_of_ne5 hq hq1 (by
          intro h; exact hhas5 (Or.inr (Or.inl h)))
        have hr13 := one_mod4_ge13_of_ne5 hr hr1 (by
          intro h; exact hhas5 (Or.inr (Or.inr (Or.inl h))))
        have hs13 := one_mod4_ge13_of_ne5 hss hs1 (by
          intro h; exact hhas5 (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        have ht13 := one_mod4_ge13_of_ne5 ht ht1 (by
          intro h; exact hhas5 (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        exact ge21_five_all_ge13_lt_three hp hq hr hss ht
          hp13 hq13 hr13 hs13 ht13
    exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 (by rw [hv0]; decide)

lemma v2_sum_three_eq_neg_four {x y z : ℤ}
    (hx : x ≤ -1) (hy : y ≤ -1) (hz : z ≤ -1) (hsum : x + y + z = -4) :
    (x = -2 ∧ y = -1 ∧ z = -1) ∨
    (x = -1 ∧ y = -2 ∧ z = -1) ∨
    (x = -1 ∧ y = -1 ∧ z = -2) := by omega

lemma ge21_five_ge3_thirteen_third_gt_two {a kp kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hpk : 3 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_ge3_lift ha (by decide : Nat.Prime 13) hpk hqk
    (ge21_five_cu_thirteen_gt_two ha hqk)
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (13 : ℕ) ≠ 0)))
  nlinarith

lemma ge21_five_ge3_seventeen_third_gt_two {a kp kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hpk : 3 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (17 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_ge3_lift ha (by decide : Nat.Prime 17) hpk hqk
    (ge21_five_cu_seventeen_gt_two ha hqk)
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (17 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0)))
  nlinarith

lemma ge21_five_ge3_twentynine_third_gt_two {a kp kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hpk : 3 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (29 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_ge3_twentynine_gt_two ha hpk hqk
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (29 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (29 : ℕ) ≠ 0)))
  nlinarith

lemma ge21_five_two_nineteen_third_gt_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum (19 ^ kq) * fSum (r ^ kr) := by
  have h0 := ge21_five_two_nineteen_gt_two ha hqk
  have h1 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
  have hpos : 0 < fSum (2 ^ a) * fSum (5 ^ 2) * fSum (19 ^ kq) :=
    mul_pos (mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
      (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (pow_ne_zero kq (by decide : (19 : ℕ) ≠ 0)))
  nlinarith

lemma four016_f5_f17sq_f107_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum (17 ^ 2) * fSum 107 := by
  rw [fSum_five, fSum_seventeen_sq, fSum_prime (by decide : Nat.Prime 107)]
  norm_num

lemma four017_f5_f17_f107sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (107 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen, fSum_prime_sq (by decide : Nat.Prime 107)]
  norm_num

lemma four017_f5_f17_f131sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (131 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen, fSum_prime_sq (by decide : Nat.Prime 131)]
  norm_num

lemma fs16067_f5_f17sq_f131sq_lt_two :
    (16067 : ℚ) / 10000 * fSum 5 * fSum (17 ^ 2) * fSum (131 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen_sq, fSum_prime_sq (by decide : Nat.Prime 131)]
  norm_num

lemma ge21_five_one_seventeen_107_or_131_ne_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hmid : r = 107 ∨ r = 131)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  rcases hmid with h | h
  · subst h
    cases hkq with
    | inl h1 =>
      subst h1
      have hD : fSum (107 ^ kr) ≤ fSum (107 ^ 2) :=
        fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 107) hkr
      have h2b := fSum_two_pow_lt_4017_2500 a
      have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ 1) * fSum (107 ^ kr) <
          (4017 : ℚ) / 2500 * fSum 5 * fSum 17 * fSum (107 ^ 2) := by
        rw [pow_one, pow_one]
        have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
          mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
        have hB : fSum (2 ^ a) * fSum 5 * fSum 17 <
            (4017 : ℚ) / 2500 * fSum 5 * fSum 17 :=
          mul_lt_mul_of_pos_right hA (fSum_pos (by decide))
        exact mul_lt_mul hB hD
          (fSum_pos (pow_ne_zero kr (by decide : (107 : ℕ) ≠ 0)))
          (mul_nonneg (mul_nonneg (by norm_num)
            (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
            (fSum_pos (by decide : (17 : ℕ) ≠ 0)).le)
      exact ne_of_lt (h1.trans four017_f5_f17_f107sq_lt_two)
    | inr h2 =>
      subst h2
      have hC : fSum 107 ≤ fSum (107 ^ kr) :=
        fSum_ge_prime (by decide : Nat.Prime 107) hkr
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum (17 ^ 2)) (C := fSum 107)
          h14 (fSum_pos (by decide)) (fSum_pos (by decide))
          (fSum_pos (by decide)) four016_f5_f17sq_f107_gt_two
      have hmono := mul3_gt_of le_rfl le_rfl hC
        (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le
        (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (by decide : (107 : ℕ) ≠ 0)).le
        (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
      rw [pow_one]
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
  · subst h
    have h2b := fSum_two_pow_lt_16067_10000 a
    have hC : fSum (17 ^ kq) ≤ fSum (17 ^ 2) :=
      fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 17) hkq
    have hD : fSum (131 ^ kr) ≤ fSum (131 ^ 2) :=
      fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 131) hkr
    have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (131 ^ kr) <
        (16067 : ℚ) / 10000 * fSum 5 * fSum (17 ^ 2) * fSum (131 ^ 2) := by
      rw [pow_one]
      have hA : fSum (2 ^ a) * fSum 5 < (16067 : ℚ) / 10000 * fSum 5 :=
        mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
      have hB : fSum (2 ^ a) * fSum 5 * fSum (17 ^ kq) <
          (16067 : ℚ) / 10000 * fSum 5 * fSum (17 ^ 2) :=
        mul_lt_mul hA hC (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0)))
          (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      exact mul_lt_mul hB hD
        (fSum_pos (pow_ne_zero kr (by decide : (131 : ℕ) ≠ 0)))
        (mul_nonneg (mul_nonneg (by norm_num)
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le)
    exact ne_of_lt (h1.trans fs16067_f5_f17sq_f131sq_lt_two)

lemma fs4017_f11sq_f13_6_f17sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 6) * fSum (17 ^ 2) < 2 := by
  rw [fSum_eleven_sq, fSum_seventeen_sq]
  rw [fSum_prime_pow (by decide : Nat.Prime 13)]
  simp [sum_range_succ, sigma_one, sigma_prime (show Nat.Prime 13 by decide),
    sigma_eq_geom (show Nat.Prime 13 by decide)]
  norm_num

lemma ge21_no_five_eleven_high13_le2_lt_two {a kp q kq : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hq17 : 17 ≤ q)
    (hkp : kp = 1 ∨ kp = 2) (hkq : kq = 1 ∨ kq = 2) :
    fSum (2 ^ a) * fSum (11 ^ kp) * fSum (13 ^ 6) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hple := fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 11) hkp
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hqs := fSum_prime_sq_anti (by decide : Nat.Prime 17) hq hq17
  have hD : fSum (q ^ kq) ≤ fSum (17 ^ 2) := le_trans hqle hqs
  have h13le : fSum (13 ^ 6) ≤ fSum (13 ^ 6) := le_rfl
  have hppos := fSum_pos (pow_ne_zero kp (by decide : (11 : ℕ) ≠ 0))
  have h13pos := fSum_pos (pow_ne_zero 6 (by decide : (13 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (11 ^ kp) < (4017 : ℚ) / 2500 * fSum (11 ^ 2) :=
    mul_lt_mul h2b hple hppos (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (11 ^ kp) * fSum (13 ^ 6) <
      (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 6) :=
    mul_lt_mul_of_pos_right h1 h13pos
  have h3 : fSum (2 ^ a) * fSum (11 ^ kp) * fSum (13 ^ 6) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 6) * fSum (17 ^ 2) :=
    mul_lt_mul h2 hD hqpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 2 (by decide : (11 : ℕ) ≠ 0))).le) h13pos.le)
  exact h3.trans fs4017_f11sq_f13_6_f17sq_lt_two

lemma fs4017_f11sq_geom17_f17sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (11 ^ 2) * ((17 : ℚ) / 16) * fSum (17 ^ 2) < 2 := by
  rw [fSum_eleven_sq, fSum_seventeen_sq]; norm_num

lemma ge21_no_five_eleven_one_high_lt_two {a kp p k q kq : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime)
    (hp13 : 13 ≤ p) (hq17 : 17 ≤ q)
    (hkp : kp = 1 ∨ kp = 2) (hk6 : k ≤ 6) (hkq : kq = 1 ∨ kq = 2) :
    fSum (2 ^ a) * fSum (11 ^ kp) * fSum (p ^ k) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hple := fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 11) hkp
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hqs := fSum_prime_sq_anti (by decide : Nat.Prime 17) hq hq17
  have hD : fSum (q ^ kq) ≤ fSum (17 ^ 2) := le_trans hqle hqs
  have hppos := fSum_pos (pow_ne_zero kp (by decide : (11 : ℕ) ≠ 0))
  have hPpos := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  cases lt_or_ge p 17 with
  | inl hlt =>
    have hp13eq : p = 13 := by
      have : p < 17 := hlt
      have : 13 ≤ p := hp13
      interval_cases p
      · exact rfl
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
    subst hp13eq
    have hle : fSum (13 ^ k) ≤ fSum (13 ^ 6) :=
      fSum_le_of_exp_ge (by decide : Nat.Prime 13) hk6
    have h1 : fSum (2 ^ a) * fSum (11 ^ kp) < (4017 : ℚ) / 2500 * fSum (11 ^ 2) :=
      mul_lt_mul h2b hple hppos (by norm_num)
    have h2 : fSum (2 ^ a) * fSum (11 ^ kp) * fSum (13 ^ k) <
        (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 6) :=
      mul_lt_mul h1 hle hPpos (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (11 : ℕ) ≠ 0))).le)
    have h3 : fSum (2 ^ a) * fSum (11 ^ kp) * fSum (13 ^ k) * fSum (q ^ kq) <
        (4017 : ℚ) / 2500 * fSum (11 ^ 2) * fSum (13 ^ 6) * fSum (17 ^ 2) :=
      mul_lt_mul h2 hD hqpos (mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (11 : ℕ) ≠ 0))).le)
        (fSum_pos (pow_ne_zero 6 (by decide : (13 : ℕ) ≠ 0))).le)
    exact h3.trans fs4017_f11sq_f13_6_f17sq_lt_two
  | inr hp17 =>
    have hσ := fSum_prime_pow_lt_geom (l := k) hp
    have hgeom : (p : ℚ) / (p - 1) ≤ (17 : ℚ) / 16 := by
      have := geom_le_of_prime_ge hp (by decide : 2 ≤ 17) hp17
      convert this using 1
      norm_num
    have hC : fSum (p ^ k) < (17 : ℚ) / 16 := hσ.trans_le hgeom
    have h1 : fSum (2 ^ a) * fSum (11 ^ kp) < (4017 : ℚ) / 2500 * fSum (11 ^ 2) :=
      mul_lt_mul h2b hple hppos (by norm_num)
    have h2 : fSum (2 ^ a) * fSum (11 ^ kp) * fSum (p ^ k) <
        (4017 : ℚ) / 2500 * fSum (11 ^ 2) * ((17 : ℚ) / 16) :=
      mul_lt_mul h1 hC.le hPpos (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (11 : ℕ) ≠ 0))).le)
    have h3 : fSum (2 ^ a) * fSum (11 ^ kp) * fSum (p ^ k) * fSum (q ^ kq) <
        (4017 : ℚ) / 2500 * fSum (11 ^ 2) * ((17 : ℚ) / 16) * fSum (17 ^ 2) :=
      mul_lt_mul h2 hD hqpos (mul_nonneg (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 2 (by decide : (11 : ℕ) ≠ 0))).le) (by norm_num))
    exact h3.trans fs4017_f11sq_geom17_f17sq_lt_two

lemma four016_f5_f19_f53_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 19 * fSum 53 := by
  rw [fSum_five, fSum_nineteen, fSum_prime (by decide : Nat.Prime 53)]
  norm_num

lemma four017_f5_f19sq_f89sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) * fSum (89 ^ 2) < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 19),
    fSum_prime_sq (by decide : Nat.Prime 89)]
  norm_num

lemma four016_f5_f19sq_f61_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) * fSum 61 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 19),
    fSum_prime (by decide : Nat.Prime 61)]
  norm_num

lemma four016_f5_f19_f61sq_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 19 * fSum (61 ^ 2) := by
  rw [fSum_five, fSum_nineteen, fSum_prime_sq (by decide : Nat.Prime 61)]
  norm_num

lemma fs16067_f5_f19_f61_lt_two :
    (16067 : ℚ) / 10000 * fSum 5 * fSum 19 * fSum 61 < 2 := by
  rw [fSum_five, fSum_nineteen, fSum_prime (by decide : Nat.Prime 61)]
  norm_num

lemma four017_f5_f19sq_f73_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) * fSum 73 < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 19),
    fSum_prime (by decide : Nat.Prime 73)]
  norm_num

lemma four017_f5_f19_f73sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum 19 * fSum (73 ^ 2) < 2 := by
  rw [fSum_five, fSum_nineteen, fSum_prime_sq (by decide : Nat.Prime 73)]
  norm_num

lemma fSum_five_six : fSum (5 ^ 6) = (1869650911757 : ℚ) / 1549105874316 := by
  rw [fSum_prime_pow Nat.prime_five]
  simp [sum_range_succ, sigma_one, sigma_prime Nat.prime_five, sigma_eq_geom Nat.prime_five]
  norm_num

lemma fs4017_f5_geom29_f37sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * ((29 : ℚ) / 28) * fSum (37 ^ 2) < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 37)]
  norm_num

lemma ge21_five_one_high_ge29_third_lt_two {a p k q kq : ℕ}
    (ha : 21 ≤ a) (hp : p.Prime) (hq : q.Prime)
    (hp29 : 29 ≤ p) (hq37 : 37 ≤ q) (hkq : kq = 1 ∨ kq = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (p ^ k) * fSum (q ^ kq) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hσ := fSum_prime_pow_lt_geom (l := k) hp
  have hgeom : (p : ℚ) / (p - 1) ≤ (29 : ℚ) / 28 := by
    have := geom_le_of_prime_ge hp (by decide : 2 ≤ 29) hp29
    convert this using 1
    norm_num
  have hC : fSum (p ^ k) < (29 : ℚ) / 28 := hσ.trans_le hgeom
  have hqle := fSum_le_sq_of_exp_le_two hq hkq
  have hqs := fSum_prime_sq_anti (by decide : Nat.Prime 37) hq hq37
  have hD : fSum (q ^ kq) ≤ fSum (37 ^ 2) := le_trans hqle hqs
  have h5pos := fSum_pos (by decide : (5 : ℕ) ≠ 0)
  have hppos := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (5 ^ 1) < (4017 : ℚ) / 2500 * fSum 5 := by
    rw [pow_one]
    exact mul_lt_mul_of_pos_right h2b h5pos
  have h2 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (p ^ k) <
      (4017 : ℚ) / 2500 * fSum 5 * ((29 : ℚ) / 28) :=
    mul_lt_mul h1 hC.le hppos (mul_nonneg (by norm_num) h5pos.le)
  have h3 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (p ^ k) * fSum (q ^ kq) <
      (4017 : ℚ) / 2500 * fSum 5 * ((29 : ℚ) / 28) * fSum (37 ^ 2) :=
    mul_lt_mul h2 hD hqpos (mul_nonneg (mul_nonneg (by norm_num) h5pos.le) (by norm_num))
  exact h3.trans fs4017_f5_geom29_f37sq_lt_two

lemma f14_f5_f19sq_f73sq_gt_two :
    2 < fSum (2 ^ 14) * fSum 5 * fSum (19 ^ 2) * fSum (73 ^ 2) := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five,
    fSum_prime_sq (by decide : Nat.Prime 19),
    fSum_prime_sq (by decide : Nat.Prime 73)]
  norm_num

lemma ge21_five_one_nineteen_le53_gt_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hr53 : r ≤ 53)
    (hkq : 1 ≤ kq) (hkr : 1 ≤ kr) :
    2 < fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) * fSum (r ^ kr) := by
  have h14 : 14 ≤ a := by omega
  have hC : fSum 19 ≤ fSum (19 ^ kq) :=
    fSum_le_of_exp_ge_one (by decide : Nat.Prime 19) hkq
  have hR : fSum r ≤ fSum (r ^ kr) := fSum_le_of_exp_ge_one hr hkr
  have hanti : fSum 53 ≤ fSum r :=
    fSum_prime_anti hr (by decide : Nat.Prime 53) hr53
  have hC' : fSum 53 ≤ fSum (r ^ kr) := le_trans hanti hR
  have hmin :=
    ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 19) (C := fSum 53)
      h14 (fSum_pos (by decide)) (fSum_pos (by decide))
      (fSum_pos (by decide)) four016_f5_f19_f53_gt_two
  have hmono := mul3_gt_of le_rfl hC hC'
    (fSum_pos (by decide : (19 : ℕ) ≠ 0)).le
    (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
    (fSum_pos (by decide : (53 : ℕ) ≠ 0)).le
    (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
      (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      (fSum_pos (pow_ne_zero kq (by decide : (19 : ℕ) ≠ 0))).le)
  rw [pow_one]
  exact lt_of_lt_of_le hmin hmono

lemma ge21_five_one_nineteen_ge89_lt_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime) (hr89 : 89 ≤ r)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) * fSum (r ^ kr) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have h5pos := fSum_pos (by decide : (5 : ℕ) ≠ 0)
  have h19pos := fSum_pos (pow_ne_zero kq (by decide : (19 : ℕ) ≠ 0))
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hC : fSum (19 ^ kq) ≤ fSum (19 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 19) hkq
  have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
  have hrs : fSum (r ^ 2) ≤ fSum (89 ^ 2) :=
    fSum_prime_sq_anti (by decide : Nat.Prime 89) hr hr89
  have hD' : fSum (r ^ kr) ≤ fSum (89 ^ 2) := le_trans hD hrs
  have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) * fSum (89 ^ 2) := by
    rw [pow_one]
    have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
      mul_lt_mul_of_pos_right h2b h5pos
    have hB : fSum (2 ^ a) * fSum 5 * fSum (19 ^ kq) <
        (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) :=
      mul_lt_mul hA hC h19pos (mul_nonneg (by norm_num) h5pos.le)
    exact mul_lt_mul hB hD' hrpos (mul_nonneg (mul_nonneg (by norm_num) h5pos.le)
      (fSum_pos (pow_ne_zero 2 (by decide : (19 : ℕ) ≠ 0))).le)
  exact h1.trans four017_f5_f19sq_f89sq_lt_two

lemma ge21_five_one_nineteen_third_ne_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hr1 : r ≡ 1 [MOD 4]) (hr29 : 29 ≤ r)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  have h2pos := fSum_pos (pow_ne_zero a two_ne_zero)
  have h5pos := fSum_pos (by decide : (5 : ℕ) ≠ 0)
  have hqk : 1 ≤ kq := by omega
  have hrk : 1 ≤ kr := by omega
  rcases prime_one_mod4_ge29_small_cases hr hr1 hr29 with
    h29 | h37 | h41 | h53 | h61 | h73 | h89 | h97
  · subst h29
    exact ne_of_gt (ge21_five_one_nineteen_le53_gt_two ha hr (by decide) hqk hrk)
  · subst h37
    exact ne_of_gt (ge21_five_one_nineteen_le53_gt_two ha hr (by decide) hqk hrk)
  · subst h41
    exact ne_of_gt (ge21_five_one_nineteen_le53_gt_two ha hr (by decide) hqk hrk)
  · subst h53
    exact ne_of_gt (ge21_five_one_nineteen_le53_gt_two ha hr (by decide) hqk hrk)
  · subst h61
    cases hkq with
    | inl hk1 =>
      subst hk1
      cases hkr with
      | inl hr1e =>
        subst hr1e
        have h2b := fSum_two_pow_lt_16067_10000 a
        have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ 1) * fSum (61 ^ 1) <
            (16067 : ℚ) / 10000 * fSum 5 * fSum 19 * fSum 61 := by
          rw [pow_one, pow_one, pow_one]
          have hA : fSum (2 ^ a) * fSum 5 < (16067 : ℚ) / 10000 * fSum 5 :=
            mul_lt_mul_of_pos_right h2b h5pos
          have hB : fSum (2 ^ a) * fSum 5 * fSum 19 <
              (16067 : ℚ) / 10000 * fSum 5 * fSum 19 :=
            mul_lt_mul_of_pos_right hA (fSum_pos (by decide))
          exact mul_lt_mul_of_pos_right hB (fSum_pos (by decide))
        exact ne_of_lt (h1.trans fs16067_f5_f19_f61_lt_two)
      | inr hr2e =>
        subst hr2e
        have hmin :=
          ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 19) (C := fSum (61 ^ 2))
            h14 h5pos (fSum_pos (by decide))
            (fSum_pos (pow_ne_zero 2 (by decide : (61 : ℕ) ≠ 0)))
            four016_f5_f19_f61sq_gt_two
        rw [pow_one]
        exact ne_of_gt hmin
    | inr hk2 =>
      subst hk2
      have hC : fSum 61 ≤ fSum (61 ^ kr) :=
        fSum_ge_prime (by decide : Nat.Prime 61) hkr
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum (19 ^ 2)) (C := fSum 61)
          h14 h5pos (fSum_pos (by decide)) (fSum_pos (by decide))
          four016_f5_f19sq_f61_gt_two
      have hmono := mul3_gt_of le_rfl le_rfl hC
        (fSum_pos (pow_ne_zero 2 (by decide : (19 : ℕ) ≠ 0))).le
        (mul_nonneg h2pos.le h5pos.le)
        (fSum_pos (by decide : (61 : ℕ) ≠ 0)).le
        (mul_nonneg (mul_nonneg h2pos.le h5pos.le)
          (fSum_pos (pow_ne_zero 2 (by decide : (19 : ℕ) ≠ 0))).le)
      rw [pow_one]
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
  · subst h73
    cases hkq with
    | inl hk1 =>
      subst hk1
      cases hkr with
      | inl hr1e =>
        subst hr1e
        have h2b := fSum_two_pow_lt_4017_2500 a
        have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ 1) * fSum (73 ^ 1) <
            (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) * fSum 73 := by
          rw [pow_one, pow_one, pow_one]
          have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
            mul_lt_mul_of_pos_right h2b h5pos
          have h19le : fSum 19 ≤ fSum (19 ^ 2) :=
            (fSum_strict_mono_prime_pow (by decide : Nat.Prime 19)
              (by decide : (1 : ℕ) < 2)).le
          have hB : fSum (2 ^ a) * fSum 5 * fSum 19 <
              (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) :=
            mul_lt_mul hA h19le (fSum_pos (by decide))
              (mul_nonneg (by norm_num) h5pos.le)
          exact mul_lt_mul_of_pos_right hB (fSum_pos (by decide))
        exact ne_of_lt (h1.trans four017_f5_f19sq_f73_lt_two)
      | inr hr2e =>
        subst hr2e
        have h2b := fSum_two_pow_lt_4017_2500 a
        have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ 1) * fSum (73 ^ 2) <
            (4017 : ℚ) / 2500 * fSum 5 * fSum 19 * fSum (73 ^ 2) := by
          rw [pow_one, pow_one]
          have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
            mul_lt_mul_of_pos_right h2b h5pos
          have hB : fSum (2 ^ a) * fSum 5 * fSum 19 <
              (4017 : ℚ) / 2500 * fSum 5 * fSum 19 :=
            mul_lt_mul_of_pos_right hA (fSum_pos (by decide))
          exact mul_lt_mul_of_pos_right hB
            (fSum_pos (pow_ne_zero 2 (by decide : (73 : ℕ) ≠ 0)))
        exact ne_of_lt (h1.trans four017_f5_f19_f73sq_lt_two)
    | inr hk2 =>
      subst hk2
      cases hkr with
      | inl hr1e =>
        subst hr1e
        have h2b := fSum_two_pow_lt_4017_2500 a
        have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ 2) * fSum (73 ^ 1) <
            (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) * fSum 73 := by
          rw [pow_one, pow_one]
          have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
            mul_lt_mul_of_pos_right h2b h5pos
          have hB : fSum (2 ^ a) * fSum 5 * fSum (19 ^ 2) <
              (4017 : ℚ) / 2500 * fSum 5 * fSum (19 ^ 2) :=
            mul_lt_mul_of_pos_right hA
              (fSum_pos (pow_ne_zero 2 (by decide : (19 : ℕ) ≠ 0)))
          exact mul_lt_mul_of_pos_right hB (fSum_pos (by decide))
        exact ne_of_lt (h1.trans four017_f5_f19sq_f73_lt_two)
      | inr hr2e =>
        subst hr2e
        have hlo : fSum (2 ^ 14) ≤ fSum (2 ^ a) := fSum_two_pow_ge_fourteen h14
        have h1 : fSum (2 ^ 14) * fSum 5 * fSum (19 ^ 2) * fSum (73 ^ 2) ≤
            fSum (2 ^ a) * fSum (5 ^ 1) * fSum (19 ^ 2) * fSum (73 ^ 2) := by
          rw [pow_one]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hlo h5pos.le)
              (fSum_pos (pow_ne_zero 2 (by decide : (19 : ℕ) ≠ 0))).le)
            (fSum_pos (pow_ne_zero 2 (by decide : (73 : ℕ) ≠ 0))).le
        exact ne_of_gt (lt_of_lt_of_le f14_f5_f19sq_f73sq_gt_two h1)
  · subst h89
    exact ne_of_lt (ge21_five_one_nineteen_ge89_lt_two ha hr (by decide) hkq hkr)
  · exact ne_of_lt
      (ge21_five_one_nineteen_ge89_lt_two ha hr
        (le_trans (by decide : 89 ≤ 97) h97) hkq hkr)

lemma fs4017_geom13_f13sq_f17sq_lt_two :
    (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) * fSum (13 ^ 2) * fSum (17 ^ 2) < 2 := by
  rw [fSum_thirteen_sq, fSum_seventeen_sq]; norm_num

lemma ge21_no_five_high_has13_lt_two {a p k kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hr : r.Prime)
    (hp13 : 13 ≤ p) (hr17 : 17 ≤ r)
    (hk6 : k ≤ 6) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (p ^ k) * fSum (13 ^ kq) * fSum (r ^ kr) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hσ := fSum_prime_pow_lt_geom (l := k) hp
  have hgeom : (p : ℚ) / (p - 1) ≤ (13 : ℚ) / 12 := by
    have := geom_le_of_prime_ge hp (by decide : 2 ≤ 13) hp13
    convert this using 1
    norm_num
  have hC : fSum (p ^ k) < (13 : ℚ) / 12 := hσ.trans_le hgeom
  have hqle := fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 13) hkq
  have hrle := fSum_le_sq_of_exp_le_two hr hkr
  have hrs := fSum_prime_sq_anti (by decide : Nat.Prime 17) hr hr17
  have hD : fSum (13 ^ kq) ≤ fSum (13 ^ 2) := hqle
  have hE : fSum (r ^ kr) ≤ fSum (17 ^ 2) := le_trans hrle hrs
  have hppos := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hqpos := fSum_pos (pow_ne_zero kq (by decide : (13 : ℕ) ≠ 0))
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have h1 : fSum (2 ^ a) * fSum (p ^ k) < (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) :=
    mul_lt_mul h2b hC.le hppos (by norm_num)
  have h2 : fSum (2 ^ a) * fSum (p ^ k) * fSum (13 ^ kq) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) * fSum (13 ^ 2) :=
    mul_lt_mul h1 hD hqpos (mul_nonneg (by norm_num) (by norm_num))
  have h3 : fSum (2 ^ a) * fSum (p ^ k) * fSum (13 ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * ((13 : ℚ) / 12) * fSum (13 ^ 2) * fSum (17 ^ 2) :=
    mul_lt_mul h2 hE hrpos (mul_nonneg (mul_nonneg (by norm_num) (by norm_num))
      (fSum_pos (pow_ne_zero 2 (by decide : (13 : ℕ) ≠ 0))).le)
  exact h3.trans fs4017_geom13_f13sq_f17sq_lt_two

lemma v2_fSum_seven_le_neg_three {k : ℕ} (hk : 1 ≤ k) :
    padicValRat 2 (fSum (7 ^ k)) ≤ -3 :=
  v2_fSum_odd_prime_pow_mod8_seven_small (by decide : Nat.Prime 7)
    (by decide) (by decide) hk

lemma ne_seven_of_v2_ge_neg_two {p k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hk : 1 ≤ k)
    (hv : -2 ≤ padicValRat 2 (fSum (p ^ k))) : p ≠ 7 := by
  intro h
  subst h
  have := v2_fSum_seven_le_neg_three hk
  omega

lemma ge_eleven_of_ge_five_ne5_v2_ge_neg_two {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hne5 : p ≠ 5) (hk : 1 ≤ k)
    (hpo : Odd p) (hv : -2 ≤ padicValRat 2 (fSum (p ^ k))) : 11 ≤ p := by
  have hp7 : 7 ≤ p := prime_ge_seven_of_ge_five_ne5 hp hp5 hne5
  have hne7 := ne_seven_of_v2_ge_neg_two hp hpo hk hv
  exact prime_ge_eleven_of_ge_seven_ne7 hp hp7 hne7

lemma ge21_extra4_no_five_neg2_first {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpo : Odd p) (hqo : Odd q) (hro : Odd r)
    (hne5p : p ≠ 5) (hne5q : q ≠ 5) (hne5r : r ≠ 5)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hpeq : padicValRat 2 (fSum (p ^ kp)) = -2)
    (hqeq : padicValRat 2 (fSum (q ^ kq)) = -1)
    (hreq : padicValRat 2 (fSum (r ^ kr)) = -1) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  haveI := two_fact
  have hpcl := v2_eq_neg_two_classification hp hpo hpk hpeq
  have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hqeq
  have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hreq
  have hq12 : kq = 1 ∨ kq = 2 := by
    have := exp_le_two_of_v2_eq_neg_one hq hqo hqk hqeq
    omega
  have hr12 : kr = 1 ∨ kr = 2 := by
    have := exp_le_two_of_v2_eq_neg_one hr hro hrk hreq
    omega
  have hq13 := one_mod4_ge13_of_ne5 hq hq1 hne5q
  have hr13 := one_mod4_ge13_of_ne5 hr hr1 hne5r
  rcases hpcl with ⟨hp3, hpk12⟩ | ⟨hp14, hpk3, hpk6⟩
  · rcases eq_three_or_ge_eleven_of_mod8_three hp hp3 with hp3eq | hp11
    · subst hp3eq
      have hgt := ge21_has_three_gt_two ha hpk
      have h2 : 1 < fSum (q ^ kq) := fSum_gt_one_of_prime_pow hq hqk
      have h3 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
      have hpos : 0 < fSum (2 ^ a) * fSum (3 ^ kp) :=
        mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
          (fSum_pos (pow_ne_zero kp (by decide : (3 : ℕ) ≠ 0)))
      have hmid : 2 < fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) := by
        nlinarith
      have hpos2 : 0 < fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) :=
        mul_pos hpos (fSum_pos (pow_ne_zero kq hq.ne_zero))
      exact ne_of_gt (by nlinarith)
    · rcases le_total q r with hqrle | hrqle
      · have hr17 : 17 ≤ r := by
          have hrne13 : r ≠ 13 := by
            intro h
            have hqle : q ≤ 13 := h ▸ hqrle
            exact hqr ((le_antisymm hqle hq13).trans h.symm)
          exact one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hrne13
        exact ne_of_lt
          (ge21_no_five_three_k_le_two_lt_two ha hp hq hr hp11 hq13 hr17
            hpk12 hq12 hr12)
      · have hq17 : 17 ≤ q := by
          have hqne13 : q ≠ 13 := by
            intro h
            have hrle : r ≤ 13 := h ▸ hrqle
            exact hqr (h.trans (le_antisymm hrle hr13).symm)
          exact one_mod4_ge17_of_ne5_ne13 hq hq1 hne5q hqne13
        have hswap :
            fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ a) * fSum (p ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
        rw [hswap]
        exact ne_of_lt
          (ge21_no_five_three_k_le_two_lt_two ha hp hr hq hp11 hr13 hq17
            hpk12 hr12 hq12)
  · have hp13 := one_mod4_ge13_of_ne5 hp hp14 hne5p
    by_cases hq13eq : q = 13
    · subst hq13eq
      have hr17 : 17 ≤ r := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hqr.symm
      exact ne_of_lt
        (ge21_no_five_high_has13_lt_two ha hp hr hp13 hr17 hpk6 hq12 hr12)
    · by_cases hr13eq : r = 13
      · subst hr13eq
        have hq17 : 17 ≤ q := one_mod4_ge17_of_ne5_ne13 hq hq1 hne5q hqr
        have hswap :
            fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (13 ^ kr) =
            fSum (2 ^ a) * fSum (p ^ kp) * fSum (13 ^ kr) * fSum (q ^ kq) := by ring
        rw [hswap]
        exact ne_of_lt
          (ge21_no_five_high_has13_lt_two ha hp hq hp13 hq17 hpk6 hr12 hq12)
      · have hq17 := one_mod4_ge17_of_ne5_ne13 hq hq1 hne5q hq13eq
        have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
        rcases le_total q r with hqrle | hrqle
        · have hr29 : 29 ≤ r := one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 (by
            intro h
            have : q = 17 := le_antisymm (h ▸ hqrle)
              (le_trans (by decide : 17 ≤ 17) hq17)
            exact hqr (this.trans h.symm))
          exact ne_of_lt
            (ge21_no_five_one_high_two_le2_lt_two ha hp hq hr hp13 hq17 hr29
              hq12 hr12)
        · have hq29 : 29 ≤ q := one_mod4_ge29_of_ge17_ne17 hq hq1 hq17 (by
            intro h
            have : r = 17 := le_antisymm (h ▸ hrqle)
              (le_trans (by decide : 17 ≤ 17) hr17)
            exact hqr (h.trans this.symm))
          have hswap :
              fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
              fSum (2 ^ a) * fSum (p ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
          rw [hswap]
          exact ne_of_lt
            (ge21_no_five_one_high_two_le2_lt_two ha hp hr hq hp13 hr17 hq29
              hr12 hq12)

lemma ge21_extra4_no_five_ne_two {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpo : Odd p) (hqo : Odd q) (hro : Odd r)
    (hne5p : p ≠ 5) (hne5q : q ≠ 5) (hne5r : r ≠ 5)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hvp : padicValRat 2 (fSum (p ^ kp)) ≤ -1)
    (hvq : padicValRat 2 (fSum (q ^ kq)) ≤ -1)
    (hvr : padicValRat 2 (fSum (r ^ kr)) ≤ -1)
    (hvsum : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
               padicValRat 2 (fSum (r ^ kr)) = -4) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have htrip := v2_sum_three_eq_neg_four hvp hvq hvr hvsum
  rcases htrip with ⟨hpeq, hqeq, hreq⟩ | ⟨hpeq, hqeq, hreq⟩ | ⟨hpeq, hqeq, hreq⟩
  · exact ge21_extra4_no_five_neg2_first ha hp hq hr hpq hpr hqr hpo hqo hro
      hne5p hne5q hne5r hpk hqk hrk hpeq hqeq hreq
  · have hswap :
        fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
        fSum (2 ^ a) * fSum (q ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) := by ring
    rw [hswap]
    exact ge21_extra4_no_five_neg2_first ha hq hp hr hpq.symm hqr hpr hqo hpo hro
      hne5q hne5p hne5r hqk hpk hrk hqeq hpeq hreq
  · have hswap :
        fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
        fSum (2 ^ a) * fSum (r ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
    rw [hswap]
    exact ge21_extra4_no_five_neg2_first ha hr hp hq hpr.symm hqr.symm hpq
      hro hpo hqo hne5r hne5p hne5q hrk hpk hqk hreq hpeq hqeq

lemma prime_one_mod4_ge37_five_cases {q : ℕ}
    (hq : q.Prime) (h1 : q ≡ 1 [MOD 4]) (h37 : 37 ≤ q) :
    q = 37 ∨ q = 41 ∨ q = 53 ∨ q = 61 ∨ 73 ≤ q := by
  by_cases h73 : 73 ≤ q
  · exact Or.inr (Or.inr (Or.inr (Or.inr h73)))
  · have : q < 73 := by omega
    interval_cases q
    all_goals
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact absurd hq (by decide)
      | simp [Nat.ModEq] at h1

lemma four016_f5cu_f37_f149_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum (5 ^ 3) * fSum 37 * fSum 149 := by
  rw [fSum_five_cu, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 149)]
  norm_num

lemma fs4017_f56_f73sq_f73sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (73 ^ 2) * fSum (73 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime_sq (by decide : Nat.Prime 73)]
  norm_num

lemma fs4017_f56_f61sq_f73sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (61 ^ 2) * fSum (73 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime_sq (by decide : Nat.Prime 61),
    fSum_prime_sq (by decide : Nat.Prime 73)]
  norm_num

lemma four016_f5cu_f53_f61_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum (5 ^ 3) * fSum 53 * fSum 61 := by
  rw [fSum_five_cu, fSum_prime (by decide : Nat.Prime 53),
    fSum_prime (by decide : Nat.Prime 61)]
  norm_num

lemma fs4017_f56_f53sq_f89sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (53 ^ 2) * fSum (89 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime_sq (by decide : Nat.Prime 53),
    fSum_prime_sq (by decide : Nat.Prime 89)]
  norm_num

set_option maxRecDepth 10000 in
lemma f14_f5cu_f41_f113_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum 41 * fSum 113 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_cu,
    fSum_prime (by decide : Nat.Prime 41),
    fSum_prime (by decide : Nat.Prime 113)]
  norm_num

lemma fs4017_f56_f41sq_f149sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (41 ^ 2) * fSum (149 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime_sq (by decide : Nat.Prime 41),
    fSum_prime_sq (by decide : Nat.Prime 149)]
  norm_num

set_option maxRecDepth 10000 in
lemma fs4017_f56_f37sq_f241sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (37 ^ 2) * fSum (241 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 241)]
  norm_num

lemma fSum_two_pow_fifteen_eq :
    fSum (2 ^ 15) = fSum (2 ^ 14) + (1 : ℚ) / 65535 := by
  have h :
      fSum (2 ^ 15) = fSum (2 ^ 14) + (1 : ℚ) / ((2 ^ 16 - 1 : ℕ) : ℚ) := by
    rw [fSum_two_pow_eq, fSum_two_pow_eq]
    have : range 16 = insert 15 (range 15) := by
      ext j; simp [mem_range]; omega
    rw [this, sum_insert (by simp)]
    ac_rfl
  have h65535 : ((2 ^ 16 - 1 : ℕ) : ℚ) = 65535 := by norm_num
  rwa [h65535] at h

lemma fSum_two_pow_ge_fifteen {a : ℕ} (ha : 15 ≤ a) :
    fSum (2 ^ 15) ≤ fSum (2 ^ a) := by
  cases Nat.lt_or_eq_of_le ha with
  | inl h => exact (fSum_strict_mono_two h).le
  | inr h => rw [h]

set_option maxRecDepth 10000 in
lemma f14_f5cu_f37_f157_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum 37 * fSum 157 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_cu,
    fSum_prime (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 157)]
  norm_num

set_option maxRecDepth 10000
lemma prime_241 : Nat.Prime 241 := by decide
lemma prime_157 : Nat.Prime 157 := by decide
lemma prime_173 : Nat.Prime 173 := by decide
lemma prime_181 : Nat.Prime 181 := by decide
lemma prime_193 : Nat.Prime 193 := by decide
lemma prime_197 : Nat.Prime 197 := by decide
lemma prime_229 : Nat.Prime 229 := by decide
lemma prime_233 : Nat.Prime 233 := by decide
lemma prime_137 : Nat.Prime 137 := by decide
lemma prime_149 : Nat.Prime 149 := by decide
lemma prime_113 : Nat.Prime 113 := by decide
set_option maxRecDepth 1000

/-- Upper bound: `p ≤ q`, `s ≤ r` implies the product is `< 2` if the hi-bound at `(p,s)` is. -/
lemma ge21_five_ge3_hi_lt_two {a kp q kq r kr p s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hp : p.Prime) (hs : s.Prime)
    (hpq : p ≤ q) (hsr : s ≤ r)
    (hpk6 : kp ≤ 6) (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2)
    (hhi : (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (p ^ 2) * fSum (s ^ 2) < 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) < 2 := by
  have h5pos := fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have h5le : fSum (5 ^ kp) ≤ fSum (5 ^ 6) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) hpk6
  have hC : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
  have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
  have hqs : fSum (q ^ 2) ≤ fSum (p ^ 2) := fSum_prime_sq_anti hp hq hpq
  have hrs : fSum (r ^ 2) ≤ fSum (s ^ 2) := fSum_prime_sq_anti hs hr hsr
  have hC' : fSum (q ^ kq) ≤ fSum (p ^ 2) := le_trans hC hqs
  have hD' : fSum (r ^ kr) ≤ fSum (s ^ 2) := le_trans hD hrs
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (p ^ 2) * fSum (s ^ 2) := by
    have hA : fSum (2 ^ a) * fSum (5 ^ kp) <
        (4017 : ℚ) / 2500 * fSum (5 ^ 6) :=
      mul_lt_mul (fSum_two_pow_lt_4017_2500 a) h5le h5pos (by norm_num)
    have hB : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
        (4017 : ℚ) / 2500 * fSum (5 ^ 6) * fSum (p ^ 2) :=
      mul_lt_mul hA hC' hqpos (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero 6 (by decide : (5 : ℕ) ≠ 0))).le)
    exact mul_lt_mul hB hD' hrpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero 6 (by decide : (5 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero 2 hp.ne_zero)).le)
  exact h1.trans hhi

/-- Lower bound via `fSum(2^14)`: `q ≤ p`, `r ≤ s` and the f14-bound at `(p,s)` give `> 2`. -/
lemma ge21_five_ge3_f14_gt_two {a kp q kq r kr p s : ℕ}
    (ha : 14 ≤ a) (hq : q.Prime) (hr : r.Prime) (hp : p.Prime) (hs : s.Prime)
    (hqp : q ≤ p) (hrs : r ≤ s)
    (hpk3 : 3 ≤ kp) (hkq : 1 ≤ kq) (hkr : 1 ≤ kr)
    (hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum p * fSum s) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
  have h2lo : fSum (2 ^ 14) ≤ fSum (2 ^ a) := fSum_two_pow_ge_fourteen ha
  have h5ge : fSum (5 ^ 3) ≤ fSum (5 ^ kp) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) hpk3
  have hqge : fSum q ≤ fSum (q ^ kq) := fSum_le_of_exp_ge_one hq hkq
  have hrge : fSum r ≤ fSum (r ^ kr) := fSum_le_of_exp_ge_one hr hkr
  have hqp' : fSum p ≤ fSum q := fSum_prime_anti hq hp hqp
  have hrs' : fSum s ≤ fSum r := fSum_prime_anti hr hs hrs
  have hB : fSum p ≤ fSum (q ^ kq) := le_trans hqp' hqge
  have hC : fSum s ≤ fSum (r ^ kr) := le_trans hrs' hrge
  have h2pos := fSum_pos (pow_ne_zero a two_ne_zero)
  have h5pos := fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have hstep : fSum (2 ^ 14) * fSum (5 ^ 3) * fSum p * fSum s ≤
      fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
    have hA : fSum (2 ^ 14) * fSum (5 ^ 3) ≤ fSum (2 ^ a) * fSum (5 ^ kp) :=
      mul_le_mul h2lo h5ge
        (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))).le
        h2pos.le
    have hAB : fSum (2 ^ 14) * fSum (5 ^ 3) * fSum p ≤
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) :=
      mul_le_mul hA hB (fSum_pos hp.ne_zero).le
        (mul_nonneg h2pos.le h5pos.le)
    exact mul_le_mul hAB hC (fSum_pos hs.ne_zero).le
      (mul_nonneg (mul_nonneg h2pos.le h5pos.le) hqpos.le)
  exact lt_of_lt_of_le hlo hstep

lemma f14_f5cu_f37_f149_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum 37 * fSum 149 := by
  refine lt_trans four016_f5cu_f37_f149_gt_two ?_
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right fSum_two_pow_fourteen_gt_4016_2500
        (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (by decide : (37 : ℕ) ≠ 0)))
    (fSum_pos (by decide : (149 : ℕ) ≠ 0))

lemma f14_f5cu_f53_f61_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum 53 * fSum 61 := by
  refine lt_trans four016_f5cu_f53_f61_gt_two ?_
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right fSum_two_pow_fourteen_gt_4016_2500
        (fSum_pos (pow_ne_zero 3 (by decide : (5 : ℕ) ≠ 0))))
      (fSum_pos (by decide : (53 : ℕ) ≠ 0)))
    (fSum_pos (by decide : (61 : ℕ) ≠ 0))

set_option maxRecDepth 10000 in
lemma prime_one_mod4_gt149_lt241 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) (hgt : 149 < r) (hlt : r < 241) :
    r = 157 ∨ r = 173 ∨ r = 181 ∨ r = 193 ∨ r = 197 ∨ r = 229 ∨ r = 233 := by
  interval_cases r
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    | exact absurd hr (by decide)
    | simp [Nat.ModEq] at h1

set_option maxRecDepth 10000 in
lemma prime_one_mod4_gt113_lt149 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) (hgt : 113 < r) (hlt : r < 149) :
    r = 137 := by
  interval_cases r
  all_goals
    first
    | exact rfl
    | exact absurd hr (by decide)
    | simp [Nat.ModEq] at h1

set_option maxRecDepth 10000 in
lemma prime_one_mod4_gt61_lt89 {r : ℕ}
    (hr : r.Prime) (h1 : r ≡ 1 [MOD 4]) (hgt : 61 < r) (hlt : r < 89) :
    r = 73 := by
  interval_cases r
  all_goals
    first
    | exact rfl
    | exact absurd hr (by decide)
    | simp [Nat.ModEq] at h1

lemma ge21_mul4_lt_hi2 {a kp q kq r kr k5m kqm krm : ℕ}
    (hq : q.Prime) (hr : r.Prime)
    (h5 : kp ≤ k5m) (hqe : kq ≤ kqm) (hre : kr ≤ krm)
    (hhi : (16067 : ℚ) / 10000 * fSum (5 ^ k5m) * fSum (q ^ kqm) * fSum (r ^ krm) < 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) < 2 := by
  have h5pos := fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr hr.ne_zero)
  have h5le : fSum (5 ^ kp) ≤ fSum (5 ^ k5m) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) h5
  have hqle : fSum (q ^ kq) ≤ fSum (q ^ kqm) := fSum_le_of_exp_ge hq hqe
  have hrle : fSum (r ^ kr) ≤ fSum (r ^ krm) := fSum_le_of_exp_ge hr hre
  have h1 : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) <
      (16067 : ℚ) / 10000 * fSum (5 ^ k5m) * fSum (q ^ kqm) * fSum (r ^ krm) := by
    have hA : fSum (2 ^ a) * fSum (5 ^ kp) <
        (16067 : ℚ) / 10000 * fSum (5 ^ k5m) :=
      mul_lt_mul (fSum_two_pow_lt_16067_10000 a) h5le h5pos (by norm_num)
    have hB : fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) <
        (16067 : ℚ) / 10000 * fSum (5 ^ k5m) * fSum (q ^ kqm) :=
      mul_lt_mul hA hqle hqpos (mul_nonneg (by norm_num)
        (fSum_pos (pow_ne_zero k5m (by decide : (5 : ℕ) ≠ 0))).le)
    exact mul_lt_mul hB hrle hrpos (mul_nonneg (mul_nonneg (by norm_num)
      (fSum_pos (pow_ne_zero k5m (by decide : (5 : ℕ) ≠ 0))).le)
      (fSum_pos (pow_ne_zero kqm hq.ne_zero)).le)
  exact h1.trans hhi

lemma ge21_mul4_gt_f14 {a kp q kq r kr k5m kqm krm : ℕ}
    (ha : 14 ≤ a) (hq : q.Prime) (hr : r.Prime)
    (h5 : k5m ≤ kp) (hqe : kqm ≤ kq) (hre : krm ≤ kr)
    (hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ k5m) * fSum (q ^ kqm) * fSum (r ^ krm)) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
  have h2lo : fSum (2 ^ 14) ≤ fSum (2 ^ a) := fSum_two_pow_ge_fourteen ha
  have h5ge : fSum (5 ^ k5m) ≤ fSum (5 ^ kp) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) h5
  have hqge : fSum (q ^ kqm) ≤ fSum (q ^ kq) := fSum_le_of_exp_ge hq hqe
  have hrge : fSum (r ^ krm) ≤ fSum (r ^ kr) := fSum_le_of_exp_ge hr hre
  have h2pos := fSum_pos (pow_ne_zero a two_ne_zero)
  have h5pos := fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hstep : fSum (2 ^ 14) * fSum (5 ^ k5m) * fSum (q ^ kqm) * fSum (r ^ krm) ≤
      fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
    have hA : fSum (2 ^ 14) * fSum (5 ^ k5m) ≤ fSum (2 ^ a) * fSum (5 ^ kp) :=
      mul_le_mul h2lo h5ge
        (fSum_pos (pow_ne_zero k5m (by decide : (5 : ℕ) ≠ 0))).le h2pos.le
    have hAB : fSum (2 ^ 14) * fSum (5 ^ k5m) * fSum (q ^ kqm) ≤
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) :=
      mul_le_mul hA hqge (fSum_pos (pow_ne_zero kqm hq.ne_zero)).le
        (mul_nonneg h2pos.le h5pos.le)
    exact mul_le_mul hAB hrge (fSum_pos (pow_ne_zero krm hr.ne_zero)).le
      (mul_nonneg (mul_nonneg h2pos.le h5pos.le) hqpos.le)
  exact lt_of_lt_of_le hlo hstep

lemma ge21_mul4_gt_f15 {a kp q kq r kr k5m kqm krm : ℕ}
    (ha : 15 ≤ a) (hq : q.Prime) (hr : r.Prime)
    (h5 : k5m ≤ kp) (hqe : kqm ≤ kq) (hre : krm ≤ kr)
    (hlo : 2 < fSum (2 ^ 15) * fSum (5 ^ k5m) * fSum (q ^ kqm) * fSum (r ^ krm)) :
    2 < fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
  have h2lo : fSum (2 ^ 15) ≤ fSum (2 ^ a) := fSum_two_pow_ge_fifteen ha
  have h5ge : fSum (5 ^ k5m) ≤ fSum (5 ^ kp) :=
    fSum_le_of_exp_ge (by decide : Nat.Prime 5) h5
  have hqge : fSum (q ^ kqm) ≤ fSum (q ^ kq) := fSum_le_of_exp_ge hq hqe
  have hrge : fSum (r ^ krm) ≤ fSum (r ^ kr) := fSum_le_of_exp_ge hr hre
  have h2pos := fSum_pos (pow_ne_zero a two_ne_zero)
  have h5pos := fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0))
  have hqpos := fSum_pos (pow_ne_zero kq hq.ne_zero)
  have hstep : fSum (2 ^ 15) * fSum (5 ^ k5m) * fSum (q ^ kqm) * fSum (r ^ krm) ≤
      fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
    have hA : fSum (2 ^ 15) * fSum (5 ^ k5m) ≤ fSum (2 ^ a) * fSum (5 ^ kp) :=
      mul_le_mul h2lo h5ge
        (fSum_pos (pow_ne_zero k5m (by decide : (5 : ℕ) ≠ 0))).le h2pos.le
    have hAB : fSum (2 ^ 15) * fSum (5 ^ k5m) * fSum (q ^ kqm) ≤
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) :=
      mul_le_mul hA hqge (fSum_pos (pow_ne_zero kqm hq.ne_zero)).le
        (mul_nonneg h2pos.le h5pos.le)
    exact mul_le_mul hAB hrge (fSum_pos (pow_ne_zero krm hr.ne_zero)).le
      (mul_nonneg (mul_nonneg h2pos.le h5pos.le) hqpos.le)
  exact lt_of_lt_of_le hlo hstep

set_option maxRecDepth 10000 in
lemma hi2_f5cu_f37_f173sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum 37 * fSum (173 ^ 2) < 2 := by
  rw [fSum_five_cu, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 173)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f5cu_f37sq_f173_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum (37 ^ 2) * fSum 173 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_cu,
    fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 173)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f54_f37_f173_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum 37 * fSum 173 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_four,
    fSum_prime (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 173)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f5cu_f37sq_f181sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (37 ^ 2) * fSum (181 ^ 2) < 2 := by
  rw [fSum_five_cu, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 181)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f54_f37_f181_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum 37 * fSum 181 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_four,
    fSum_prime (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 181)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f5cu_f37sq_f193sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (37 ^ 2) * fSum (193 ^ 2) < 2 := by
  rw [fSum_five_cu, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 193)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f54_f37_f193sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum 37 * fSum (193 ^ 2) < 2 := by
  rw [fSum_five_four, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 193)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f54_f37sq_f193_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (37 ^ 2) * fSum 193 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_four,
    fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 193)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f55_f37_f193_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum 37 * fSum 193 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_five_pow,
    fSum_prime (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 193)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f5cu_f37sq_f197sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (37 ^ 2) * fSum (197 ^ 2) < 2 := by
  rw [fSum_five_cu, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 197)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f54_f37_f197sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum 37 * fSum (197 ^ 2) < 2 := by
  rw [fSum_five_four, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 197)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f54_f37sq_f197_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (37 ^ 2) * fSum 197 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_four,
    fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 197)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f55_f37_f197_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum 37 * fSum 197 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_five_pow,
    fSum_prime (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 197)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f54_f37sq_f229sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum (37 ^ 2) * fSum (229 ^ 2) < 2 := by
  rw [fSum_five_four, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 229)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f55_f37_f229sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 5) * fSum 37 * fSum (229 ^ 2) < 2 := by
  rw [fSum_five_five_pow, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 229)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f55_f37sq_f229_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum (37 ^ 2) * fSum 229 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_five_pow,
    fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 229)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f56_f37_f229sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 6) * fSum 37 * fSum (229 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 229)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f56_f37sq_f229_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 6) * fSum (37 ^ 2) * fSum 229 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_six,
    fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 229)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f54_f37sq_f233sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum (37 ^ 2) * fSum (233 ^ 2) < 2 := by
  rw [fSum_five_four, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 233)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f55_f37_f233sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 5) * fSum 37 * fSum (233 ^ 2) < 2 := by
  rw [fSum_five_five_pow, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 233)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f55_f37sq_f233_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 5) * fSum (37 ^ 2) * fSum 233 < 2 := by
  rw [fSum_five_five_pow, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 233)]; norm_num

set_option maxRecDepth 10000 in
lemma f15_f55_f37sq_f233sq_gt_two :
    2 < fSum (2 ^ 15) * fSum (5 ^ 5) * fSum (37 ^ 2) * fSum (233 ^ 2) := by
  rw [fSum_two_pow_fifteen_eq, fSum_two_pow_fourteen_eq, fSum_two_pow_eight,
    fSum_five_five_pow, fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 233)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f56_f37_f233sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 6) * fSum 37 * fSum (233 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime (by decide : Nat.Prime 37),
    fSum_prime_sq (by decide : Nat.Prime 233)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f56_f37sq_f233_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 6) * fSum (37 ^ 2) * fSum 233 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_six,
    fSum_prime_sq (by decide : Nat.Prime 37),
    fSum_prime (by decide : Nat.Prime 233)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f5cu_f41sq_f137sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (41 ^ 2) * fSum (137 ^ 2) < 2 := by
  rw [fSum_five_cu, fSum_prime_sq (by decide : Nat.Prime 41),
    fSum_prime_sq (by decide : Nat.Prime 137)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f54_f41_f137sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum 41 * fSum (137 ^ 2) < 2 := by
  rw [fSum_five_four, fSum_prime (by decide : Nat.Prime 41),
    fSum_prime_sq (by decide : Nat.Prime 137)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f54_f41sq_f137_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (41 ^ 2) * fSum 137 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_four,
    fSum_prime_sq (by decide : Nat.Prime 41),
    fSum_prime (by decide : Nat.Prime 137)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f56_f41_f137sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 6) * fSum 41 * fSum (137 ^ 2) < 2 := by
  rw [fSum_five_six, fSum_prime (by decide : Nat.Prime 41),
    fSum_prime_sq (by decide : Nat.Prime 137)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f55_f41sq_f137_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum (41 ^ 2) * fSum 137 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_five_pow,
    fSum_prime_sq (by decide : Nat.Prime 41),
    fSum_prime (by decide : Nat.Prime 137)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f5cu_f53_f73sq_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum 53 * fSum (73 ^ 2) < 2 := by
  rw [fSum_five_cu, fSum_prime (by decide : Nat.Prime 53),
    fSum_prime_sq (by decide : Nat.Prime 73)]; norm_num

set_option maxRecDepth 10000 in
lemma hi2_f5cu_f53sq_f73_lt_two :
    (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (53 ^ 2) * fSum 73 < 2 := by
  rw [fSum_five_cu, fSum_prime_sq (by decide : Nat.Prime 53),
    fSum_prime (by decide : Nat.Prime 73)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f5cu_f53sq_f73sq_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum (53 ^ 2) * fSum (73 ^ 2) := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_cu,
    fSum_prime_sq (by decide : Nat.Prime 53),
    fSum_prime_sq (by decide : Nat.Prime 73)]; norm_num

set_option maxRecDepth 10000 in
lemma f14_f54_f53_f73_gt_two :
    2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum 53 * fSum 73 := by
  rw [fSum_two_pow_fourteen_eq, fSum_two_pow_eight, fSum_five_four,
    fSum_prime (by decide : Nat.Prime 53),
    fSum_prime (by decide : Nat.Prime 73)]; norm_num

set_option maxHeartbeats 400000 in
lemma ge21_five_ge3_two_ge37_sorted_ne_two {a kp q kq r kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hq37 : 37 ≤ q) (hle : q ≤ r)
    (hpk3 : 3 ≤ kp) (hpk6 : kp ≤ 6)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  have hqk : 1 ≤ kq := by omega
  have hrk : 1 ≤ kr := by omega
  rcases prime_one_mod4_ge37_five_cases hq hq1 hq37 with
    hq37eq | hq41 | hq53 | hq61 | hq73
  · subst hq37eq
    by_cases hr241 : 241 ≤ r
    · exact ne_of_lt (ge21_five_ge3_hi_lt_two (by decide) hr
        (by decide : Nat.Prime 37) prime_241 le_rfl hr241 hpk6 hkq hkr
        fs4017_f56_f37sq_f241sq_lt_two)
    · have hr241' : r < 241 := by omega
      by_cases hr149 : r ≤ 149
      · exact ne_of_gt (ge21_five_ge3_f14_gt_two h14 (by decide) hr
          (by decide : Nat.Prime 37) prime_149 le_rfl hr149 hpk3 hqk hrk
          f14_f5cu_f37_f149_gt_two)
      · have hgt : 149 < r := by omega
        rcases prime_one_mod4_gt149_lt241 hr hr1 hgt hr241' with
          h157 | h173 | h181 | h193 | h197 | h229 | h233
        · subst h157
          exact ne_of_gt (ge21_five_ge3_f14_gt_two h14 (by decide) prime_157
            (by decide : Nat.Prime 37) prime_157 le_rfl le_rfl hpk3 hqk hrk
            f14_f5cu_f37_f157_gt_two)
        · subst h173
          rcases lt_or_ge kp 4 with hk3 | hk4
          · have hkpeq : kp = 3 := by omega
            subst hkpeq
            cases hkq with
            | inl h1 =>
              subst h1
              have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (37 ^ 1) *
                  fSum (173 ^ 2) < 2 := by
                rw [pow_one]; exact hi2_f5cu_f37_f173sq_lt_two
              exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_173
                le_rfl le_rfl (by omega) hhi)
            | inr h2 =>
              subst h2
              have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 3) * fSum (37 ^ 2) *
                  fSum (173 ^ 1) := by
                rw [pow_one]; exact f14_f5cu_f37sq_f173_gt_two
              exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_173
                le_rfl le_rfl (by omega : 1 ≤ kr) hlo)
          · have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (37 ^ 1) *
                fSum (173 ^ 1) := by
              rw [pow_one, pow_one]; exact f14_f54_f37_f173_gt_two
            exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_173
              hk4 (by omega : 1 ≤ kq) (by omega : 1 ≤ kr) hlo)
        · subst h181
          rcases lt_or_ge kp 4 with hk3 | hk4
          · have hkpeq : kp = 3 := by omega
            subst hkpeq
            have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (37 ^ 2) *
                fSum (181 ^ 2) < 2 := hi2_f5cu_f37sq_f181sq_lt_two
            exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_181
              le_rfl (by omega) (by omega) hhi)
          · have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (37 ^ 1) *
                fSum (181 ^ 1) := by
              rw [pow_one, pow_one]; exact f14_f54_f37_f181_gt_two
            exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_181
              hk4 (by omega : 1 ≤ kq) (by omega : 1 ≤ kr) hlo)
        · subst h193
          rcases lt_or_ge kp 4 with hk3 | hk4
          · have hkpeq : kp = 3 := by omega
            subst hkpeq
            exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_193
              le_rfl (by omega) (by omega) hi2_f5cu_f37sq_f193sq_lt_two)
          · rcases lt_or_ge kp 5 with hk4' | hk5
            · have hkpeq : kp = 4 := by omega
              subst hkpeq
              cases hkq with
              | inl h1 =>
                subst h1
                have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum (37 ^ 1) *
                    fSum (193 ^ 2) < 2 := by
                  rw [pow_one]; exact hi2_f54_f37_f193sq_lt_two
                exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_193
                  le_rfl le_rfl (by omega) hhi)
              | inr h2 =>
                subst h2
                have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (37 ^ 2) *
                    fSum (193 ^ 1) := by
                  rw [pow_one]; exact f14_f54_f37sq_f193_gt_two
                exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_193
                  le_rfl le_rfl (by omega : 1 ≤ kr) hlo)
            · have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum (37 ^ 1) *
                  fSum (193 ^ 1) := by
                rw [pow_one, pow_one]; exact f14_f55_f37_f193_gt_two
              exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_193
                hk5 (by omega : 1 ≤ kq) (by omega : 1 ≤ kr) hlo)
        · subst h197
          rcases lt_or_ge kp 4 with hk3 | hk4
          · have hkpeq : kp = 3 := by omega
            subst hkpeq
            exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_197
              le_rfl (by omega) (by omega) hi2_f5cu_f37sq_f197sq_lt_two)
          · rcases lt_or_ge kp 5 with hk4' | hk5
            · have hkpeq : kp = 4 := by omega
              subst hkpeq
              cases hkq with
              | inl h1 =>
                subst h1
                have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum (37 ^ 1) *
                    fSum (197 ^ 2) < 2 := by
                  rw [pow_one]; exact hi2_f54_f37_f197sq_lt_two
                exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_197
                  le_rfl le_rfl (by omega) hhi)
              | inr h2 =>
                subst h2
                have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (37 ^ 2) *
                    fSum (197 ^ 1) := by
                  rw [pow_one]; exact f14_f54_f37sq_f197_gt_two
                exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_197
                  le_rfl le_rfl (by omega : 1 ≤ kr) hlo)
            · have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum (37 ^ 1) *
                  fSum (197 ^ 1) := by
                rw [pow_one, pow_one]; exact f14_f55_f37_f197_gt_two
              exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_197
                hk5 (by omega : 1 ≤ kq) (by omega : 1 ≤ kr) hlo)
        · subst h229
          rcases lt_or_ge kp 5 with hk4 | hk5
          · have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum (37 ^ 2) *
                fSum (229 ^ 2) < 2 := hi2_f54_f37sq_f229sq_lt_two
            exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_229
              (by omega : kp ≤ 4) (by omega) (by omega) hhi)
          · rcases lt_or_ge kp 6 with hk5' | hk6
            · have hkpeq : kp = 5 := by omega
              subst hkpeq
              cases hkq with
              | inl h1 =>
                subst h1
                have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 5) * fSum (37 ^ 1) *
                    fSum (229 ^ 2) < 2 := by
                  rw [pow_one]; exact hi2_f55_f37_f229sq_lt_two
                exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_229
                  le_rfl le_rfl (by omega) hhi)
              | inr h2 =>
                subst h2
                have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum (37 ^ 2) *
                    fSum (229 ^ 1) := by
                  rw [pow_one]; exact f14_f55_f37sq_f229_gt_two
                exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_229
                  le_rfl le_rfl (by omega : 1 ≤ kr) hlo)
            · have hkpeq : kp = 6 := by omega
              subst hkpeq
              cases hkq with
              | inl h1 =>
                subst h1
                have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 6) * fSum (37 ^ 1) *
                    fSum (229 ^ 2) < 2 := by
                  rw [pow_one]; exact hi2_f56_f37_f229sq_lt_two
                exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_229
                  le_rfl le_rfl (by omega) hhi)
              | inr h2 =>
                subst h2
                have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 6) * fSum (37 ^ 2) *
                    fSum (229 ^ 1) := by
                  rw [pow_one]; exact f14_f56_f37sq_f229_gt_two
                exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_229
                  le_rfl le_rfl (by omega : 1 ≤ kr) hlo)
        · subst h233
          rcases lt_or_ge kp 5 with hk4 | hk5
          · exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_233
              (by omega : kp ≤ 4) (by omega) (by omega)
              hi2_f54_f37sq_f233sq_lt_two)
          · rcases lt_or_ge kp 6 with hk5' | hk6
            · have hkpeq : kp = 5 := by omega
              subst hkpeq
              cases hkq with
              | inl h1 =>
                subst h1
                have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 5) * fSum (37 ^ 1) *
                    fSum (233 ^ 2) < 2 := by
                  rw [pow_one]; exact hi2_f55_f37_f233sq_lt_two
                exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_233
                  le_rfl le_rfl (by omega) hhi)
              | inr h2 =>
                subst h2
                cases hkr with
                | inl hr1e =>
                  subst hr1e
                  have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 5) * fSum (37 ^ 2) *
                      fSum (233 ^ 1) < 2 := by
                    rw [pow_one]; exact hi2_f55_f37sq_f233_lt_two
                  exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_233
                    le_rfl le_rfl le_rfl hhi)
                | inr hr2e =>
                  subst hr2e
                  exact ne_of_gt (ge21_mul4_gt_f15 (by omega : 15 ≤ a)
                    (by decide) prime_233 le_rfl le_rfl le_rfl
                    f15_f55_f37sq_f233sq_gt_two)
            · have hkpeq : kp = 6 := by omega
              subst hkpeq
              cases hkq with
              | inl h1 =>
                subst h1
                have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 6) * fSum (37 ^ 1) *
                    fSum (233 ^ 2) < 2 := by
                  rw [pow_one]; exact hi2_f56_f37_f233sq_lt_two
                exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_233
                  le_rfl le_rfl (by omega) hhi)
              | inr h2 =>
                subst h2
                have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 6) * fSum (37 ^ 2) *
                    fSum (233 ^ 1) := by
                  rw [pow_one]; exact f14_f56_f37sq_f233_gt_two
                exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_233
                  le_rfl le_rfl (by omega : 1 ≤ kr) hlo)
  · subst hq41
    by_cases hr149 : 149 ≤ r
    · exact ne_of_lt (ge21_five_ge3_hi_lt_two (by decide) hr
        (by decide : Nat.Prime 41) prime_149 le_rfl hr149 hpk6 hkq hkr
        fs4017_f56_f41sq_f149sq_lt_two)
    · have hr149' : r < 149 := by omega
      by_cases hr113 : r ≤ 113
      · exact ne_of_gt (ge21_five_ge3_f14_gt_two h14 (by decide) hr
          (by decide : Nat.Prime 41) prime_113 le_rfl hr113 hpk3 hqk hrk
          f14_f5cu_f41_f113_gt_two)
      · have hgt : 113 < r := by omega
        have hr137 := prime_one_mod4_gt113_lt149 hr hr1 hgt hr149'
        subst hr137
        rcases lt_or_ge kp 4 with hk3 | hk4
        · have hkpeq : kp = 3 := by omega
          subst hkpeq
          exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_137
            le_rfl (by omega) (by omega) hi2_f5cu_f41sq_f137sq_lt_two)
        · rcases lt_or_ge kp 5 with hk4' | hk5
          · have hkpeq : kp = 4 := by omega
            subst hkpeq
            cases hkq with
            | inl h1 =>
              subst h1
              have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 4) * fSum (41 ^ 1) *
                  fSum (137 ^ 2) < 2 := by
                rw [pow_one]; exact hi2_f54_f41_f137sq_lt_two
              exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_137
                le_rfl le_rfl (by omega) hhi)
            | inr h2 =>
              subst h2
              have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (41 ^ 2) *
                  fSum (137 ^ 1) := by
                rw [pow_one]; exact f14_f54_f41sq_f137_gt_two
              exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_137
                le_rfl le_rfl (by omega : 1 ≤ kr) hlo)
          · cases hkq with
            | inl h1 =>
              subst h1
              have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 6) * fSum (41 ^ 1) *
                  fSum (137 ^ 2) < 2 := by
                rw [pow_one]; exact hi2_f56_f41_f137sq_lt_two
              exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) prime_137
                hpk6 le_rfl (by omega) hhi)
            | inr h2 =>
              subst h2
              have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 5) * fSum (41 ^ 2) *
                  fSum (137 ^ 1) := by
                rw [pow_one]; exact f14_f55_f41sq_f137_gt_two
              exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide) prime_137
                hk5 le_rfl (by omega : 1 ≤ kr) hlo)
  · subst hq53
    by_cases hr89 : 89 ≤ r
    · exact ne_of_lt (ge21_five_ge3_hi_lt_two (by decide) hr
        (by decide : Nat.Prime 53) (by decide : Nat.Prime 89)
        le_rfl hr89 hpk6 hkq hkr
        fs4017_f56_f53sq_f89sq_lt_two)
    · have hr89' : r < 89 := by omega
      by_cases hr61 : r ≤ 61
      · exact ne_of_gt (ge21_five_ge3_f14_gt_two h14 (by decide) hr
          (by decide : Nat.Prime 53) (by decide : Nat.Prime 61) le_rfl hr61
          hpk3 hqk hrk f14_f5cu_f53_f61_gt_two)
      · have hgt : 61 < r := by omega
        have hr73 := prime_one_mod4_gt61_lt89 hr hr1 hgt hr89'
        subst hr73
        rcases lt_or_ge kp 4 with hk3 | hk4
        · have hkpeq : kp = 3 := by omega
          subst hkpeq
          cases hkq with
          | inl h1 =>
            subst h1
            have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (53 ^ 1) *
                fSum (73 ^ 2) < 2 := by
              rw [pow_one]; exact hi2_f5cu_f53_f73sq_lt_two
            exact ne_of_lt (ge21_mul4_lt_hi2 (by decide) (by decide : Nat.Prime 73)
              le_rfl le_rfl (by omega) hhi)
          | inr h2 =>
            subst h2
            cases hkr with
            | inl hr1e =>
              subst hr1e
              have hhi : (16067 : ℚ) / 10000 * fSum (5 ^ 3) * fSum (53 ^ 2) *
                  fSum (73 ^ 1) < 2 := by
                rw [pow_one]; exact hi2_f5cu_f53sq_f73_lt_two
              exact ne_of_lt (ge21_mul4_lt_hi2 (by decide)
                (by decide : Nat.Prime 73) le_rfl le_rfl le_rfl hhi)
            | inr hr2e =>
              subst hr2e
              exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide)
                (by decide : Nat.Prime 73) le_rfl le_rfl le_rfl
                f14_f5cu_f53sq_f73sq_gt_two)
        · have hlo : 2 < fSum (2 ^ 14) * fSum (5 ^ 4) * fSum (53 ^ 1) *
              fSum (73 ^ 1) := by
            rw [pow_one, pow_one]; exact f14_f54_f53_f73_gt_two
          exact ne_of_gt (ge21_mul4_gt_f14 h14 (by decide)
            (by decide : Nat.Prime 73) hk4 (by omega : 1 ≤ kq)
            (by omega : 1 ≤ kr) hlo)
  · subst hq61
    have hr73 : 73 ≤ r := by
      have hne : r ≠ 61 := hqr.symm
      rcases lt_or_ge r 73 with hlt | hge
      · have : 61 < r := lt_of_le_of_ne hle hne.symm
        have hr73eq := prime_one_mod4_gt61_lt89 hr hr1 this (lt_trans hlt (by decide))
        omega
      · exact hge
    exact ne_of_lt (ge21_five_ge3_hi_lt_two (by decide) hr
      (by decide : Nat.Prime 61) (by decide : Nat.Prime 73)
      le_rfl hr73 hpk6 hkq hkr
      fs4017_f56_f61sq_f73sq_lt_two)
  · exact ne_of_lt (ge21_five_ge3_hi_lt_two hq hr
      (by decide : Nat.Prime 73) (by decide : Nat.Prime 73)
      hq73 (le_trans hq73 hle) hpk6 hkq hkr
      fs4017_f56_f73sq_f73sq_lt_two)

lemma ge21_five_ge3_two_ge37_ne_two {a kp q kq r kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hq37 : 37 ≤ q) (hr37 : 37 ≤ r)
    (hpk3 : 3 ≤ kp) (hpk6 : kp ≤ 6)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  rcases le_total q r with hqrle | hrqle
  · exact ge21_five_ge3_two_ge37_sorted_ne_two ha hq hr hqr hq1 hr1 hq37 hqrle
      hpk3 hpk6 hkq hkr
  · have hswap :
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
    rw [hswap]
    exact ge21_five_ge3_two_ge37_sorted_ne_two ha hr hq hqr.symm hr1 hq1 hr37 hrqle
      hpk3 hpk6 hkr hkq

lemma ge21_extra4_five_is_neg2 {a kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r) (hqo : Odd q) (hro : Odd r)
    (hne5q : q ≠ 5) (hne5r : r ≠ 5)
    (hpk : 3 ≤ kp) (hpk6 : kp ≤ 6) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hqeq : padicValRat 2 (fSum (q ^ kq)) = -1)
    (hreq : padicValRat 2 (fSum (r ^ kr)) = -1) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  haveI := two_fact
  have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hqeq
  have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hreq
  have hq12 : kq = 1 ∨ kq = 2 := by
    have := exp_le_two_of_v2_eq_neg_one hq hqo hqk hqeq; omega
  have hr12 : kr = 1 ∨ kr = 2 := by
    have := exp_le_two_of_v2_eq_neg_one hr hro hrk hreq; omega
  have hq13 := one_mod4_ge13_of_ne5 hq hq1 hne5q
  have hr13 := one_mod4_ge13_of_ne5 hr hr1 hne5r
  by_cases hq13eq : q = 13
  · subst hq13eq
    exact ne_of_gt (ge21_five_ge3_thirteen_third_gt_two ha hr hpk hqk hrk)
  · by_cases hr13eq : r = 13
    · subst hr13eq
      have hswap :
          fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (13 ^ kr) =
          fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kr) * fSum (q ^ kq) := by ring
      rw [hswap]
      exact ne_of_gt (ge21_five_ge3_thirteen_third_gt_two ha hq hpk hrk hqk)
    · by_cases hq17eq : q = 17
      · subst hq17eq
        exact ne_of_gt (ge21_five_ge3_seventeen_third_gt_two ha hr hpk hqk hrk)
      · by_cases hr17eq : r = 17
        · subst hr17eq
          have hswap :
              fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (17 ^ kr) =
              fSum (2 ^ a) * fSum (5 ^ kp) * fSum (17 ^ kr) * fSum (q ^ kq) := by ring
          rw [hswap]
          exact ne_of_gt (ge21_five_ge3_seventeen_third_gt_two ha hq hpk hrk hqk)
        · have hq17 := one_mod4_ge17_of_ne5_ne13 hq hq1 hne5q hq13eq
          have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
          have hq29 := one_mod4_ge29_of_ge17_ne17 hq hq1 hq17 hq17eq
          have hr29 := one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 hr17eq
          by_cases hq29eq : q = 29
          · subst hq29eq
            exact ne_of_gt (ge21_five_ge3_twentynine_third_gt_two ha hr hpk hqk hrk)
          · by_cases hr29eq : r = 29
            · subst hr29eq
              have hswap :
                  fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (29 ^ kr) =
                  fSum (2 ^ a) * fSum (5 ^ kp) * fSum (29 ^ kr) * fSum (q ^ kq) := by ring
              rw [hswap]
              exact ne_of_gt (ge21_five_ge3_twentynine_third_gt_two ha hq hpk hrk hqk)
            · have hq37 : 37 ≤ q := by
                rcases prime_one_mod4_ge29_mid_cases hq hq1 hq29 with h | h
                · exact (hq29eq h).elim
                · exact h
              have hr37 : 37 ≤ r := by
                rcases prime_one_mod4_ge29_mid_cases hr hr1 hr29 with h | h
                · exact (hr29eq h).elim
                · exact h
              -- 5^{3..6} * q≥37 * r≥37: both k=1,2
              exact ge21_five_ge3_two_ge37_ne_two ha hq hr hqr hq1 hr1 hq37 hr37
                hpk hpk6 hq12 hr12

lemma prime_mod8_three_ge43_split {q : ℕ}
    (hq : q.Prime) (h3 : q ≡ 3 [MOD 8]) (h43 : 43 ≤ q) :
    q ≤ 89 ∨ q = 107 ∨ q = 131 ∨ 137 ≤ q := by
  by_cases h89 : q ≤ 89
  · exact Or.inl h89
  · by_cases h107 : q = 107
    · exact Or.inr (Or.inl h107)
    · by_cases h131 : q = 131
      · exact Or.inr (Or.inr (Or.inl h131))
      · have hmod : q % 8 = 3 := by simpa [Nat.ModEq] using h3
        cases lt_or_ge q 137 with
        | inl hlt =>
          have : 90 ≤ q := by omega
          have : q = 91 ∨ q = 99 ∨ q = 107 ∨ q = 115 ∨ q = 123 ∨ q = 131 := by
            omega
          rcases this with h | h | h | h | h | h
          · subst h; exact absurd hq (by decide)
          · subst h; exact absurd hq (by decide)
          · exact (h107 h).elim
          · subst h; exact absurd hq (by decide)
          · subst h; exact absurd hq (by decide)
          · exact (h131 h).elim
        | inr hge => exact Or.inr (Or.inr (Or.inr hge))

lemma ge21_five_one_seventeen_mod8_three_ne_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hr3 : r ≡ 3 [MOD 8]) (hr43 : 43 ≤ r)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have hrk : 1 ≤ kr := by omega
  rcases prime_mod8_three_ge43_split hr hr3 hr43 with h89 | h107 | h131 | h137
  · have hgt := ge21_five_one_seventeen_le89_gt_two ha hr h89 hrk
    have hB : fSum (17 ^ 1) ≤ fSum (17 ^ kq) :=
      fSum_ge_prime (by decide : Nat.Prime 17) hkq
    have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ 1) * fSum (r ^ kr) ≤
        fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB
          (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
            (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le))
        (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
    exact ne_of_gt (lt_of_lt_of_le hgt h1)
  · exact ge21_five_one_seventeen_107_or_131_ne_two ha hr (Or.inl h107) hkq hkr
  · exact ge21_five_one_seventeen_107_or_131_ne_two ha hr (Or.inr h131) hkq hkr
  · exact ne_of_lt (ge21_five_one_seventeen_ge137_lt_two ha hr h137 hkq hkr)

lemma four016_f5sq_f43_f61_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum (5 ^ 2) * fSum 43 * fSum 61 := by
  rw [fSum_five_sq, fSum_prime (by decide : Nat.Prime 43),
    fSum_prime (by decide : Nat.Prime 61)]
  norm_num

lemma four017_f5sq_f43sq_f73sq_lt_two :
    (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) * fSum (73 ^ 2) < 2 := by
  rw [fSum_five_sq, fSum_prime_sq (by decide : Nat.Prime 43),
    fSum_prime_sq (by decide : Nat.Prime 73)]
  norm_num

lemma ge21_five_two_mod8_three_third_ne_two {a q kq r kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hr : r.Prime)
    (hq3 : q ≡ 3 [MOD 8]) (hr1 : r ≡ 1 [MOD 4])
    (hq43 : 43 ≤ q) (hr17 : 17 ≤ r)
    (hkq : kq = 1 ∨ kq = 2) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  have hqk : 1 ≤ kq := by omega
  have hrk : 1 ≤ kr := by omega
  by_cases hr17eq : r = 17
  · subst hr17eq
    have hswap :
        fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (17 ^ kr) =
        fSum (2 ^ a) * fSum (5 ^ 2) * fSum (17 ^ kr) * fSum (q ^ kq) := by ring
    rw [hswap]
    exact ne_of_gt (ge21_five_two_seventeen_third_gt_two ha hq hrk hqk)
  · have hr29 : 29 ≤ r := one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 hr17eq
    rcases prime_one_mod4_le61_or_73_or_ge89 hr hr1 hr29 with hr61 | hr73 | hr89
    · have hqrle : q ≤ r ∨ r ≤ q := le_total q r
      -- Bound via 43² and 61²: product is < 2 except for a few small pairs,
      -- which we treat with the 17-case already handled and the 73-upper-bound below.
      have h2b := fSum_two_pow_lt_4017_2500 a
      have hC : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
      have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
      have hqs : fSum (q ^ 2) ≤ fSum (43 ^ 2) :=
        fSum_prime_sq_anti (by decide : Nat.Prime 43) hq hq43
      have hrs : fSum (r ^ 2) ≤ fSum (29 ^ 2) :=
        fSum_prime_sq_anti (by decide : Nat.Prime 29) hr hr29
      have hC' : fSum (q ^ kq) ≤ fSum (43 ^ 2) := le_trans hC hqs
      have hD' : fSum (r ^ kr) ≤ fSum (29 ^ 2) := le_trans hD hrs
      have hprod : (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) *
          fSum (29 ^ 2) < 2 := by
        rw [fSum_five_sq, fSum_prime_sq (by decide : Nat.Prime 43),
          fSum_twenty_nine_sq]
        norm_num
      have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) <
          (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) * fSum (29 ^ 2) := by
        have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
          mul_lt_mul_of_pos_right h2b
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0)))
        have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) :=
          mul_lt_mul hA hC' (fSum_pos (pow_ne_zero kq hq.ne_zero))
            (mul_nonneg (by norm_num)
              (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
        exact mul_lt_mul hB hD' (fSum_pos (pow_ne_zero kr hr.ne_zero))
          (mul_nonneg (mul_nonneg (by norm_num)
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
            (fSum_pos (pow_ne_zero 2 (by decide : (43 : ℕ) ≠ 0))).le)
      exact ne_of_lt (h1.trans hprod)
    · subst hr73
      have h2b := fSum_two_pow_lt_4017_2500 a
      have hC : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
      have hqs : fSum (q ^ 2) ≤ fSum (43 ^ 2) :=
        fSum_prime_sq_anti (by decide : Nat.Prime 43) hq hq43
      have hC' : fSum (q ^ kq) ≤ fSum (43 ^ 2) := le_trans hC hqs
      have hD : fSum (73 ^ kr) ≤ fSum (73 ^ 2) :=
        fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 73) hkr
      have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (73 ^ kr) <
          (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) * fSum (73 ^ 2) := by
        have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
          mul_lt_mul_of_pos_right h2b
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0)))
        have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) :=
          mul_lt_mul hA hC' (fSum_pos (pow_ne_zero kq hq.ne_zero))
            (mul_nonneg (by norm_num)
              (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
        exact mul_lt_mul hB hD
          (fSum_pos (pow_ne_zero kr (by decide : (73 : ℕ) ≠ 0)))
          (mul_nonneg (mul_nonneg (by norm_num)
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
            (fSum_pos (pow_ne_zero 2 (by decide : (43 : ℕ) ≠ 0))).le)
      exact ne_of_lt (h1.trans four017_f5sq_f43sq_f73sq_lt_two)
    · have h2b := fSum_two_pow_lt_4017_2500 a
      have hC : fSum (q ^ kq) ≤ fSum (q ^ 2) := fSum_le_sq_of_exp_le_two hq hkq
      have hqs : fSum (q ^ 2) ≤ fSum (43 ^ 2) :=
        fSum_prime_sq_anti (by decide : Nat.Prime 43) hq hq43
      have hC' : fSum (q ^ kq) ≤ fSum (43 ^ 2) := le_trans hC hqs
      have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
      have hrs : fSum (r ^ 2) ≤ fSum (73 ^ 2) :=
        fSum_prime_sq_anti (by decide : Nat.Prime 73) hr
          (le_trans (by decide : 73 ≤ 89) hr89)
      have hD' : fSum (r ^ kr) ≤ fSum (73 ^ 2) := le_trans hD hrs
      have h1 : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) <
          (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) * fSum (73 ^ 2) := by
        have hA : fSum (2 ^ a) * fSum (5 ^ 2) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) :=
          mul_lt_mul_of_pos_right h2b
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0)))
        have hB : fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) <
            (4017 : ℚ) / 2500 * fSum (5 ^ 2) * fSum (43 ^ 2) :=
          mul_lt_mul hA hC' (fSum_pos (pow_ne_zero kq hq.ne_zero))
            (mul_nonneg (by norm_num)
              (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
        exact mul_lt_mul hB hD' (fSum_pos (pow_ne_zero kr hr.ne_zero))
          (mul_nonneg (mul_nonneg (by norm_num)
            (fSum_pos (pow_ne_zero 2 (by decide : (5 : ℕ) ≠ 0))).le)
            (fSum_pos (pow_ne_zero 2 (by decide : (43 : ℕ) ≠ 0))).le)
      exact ne_of_lt (h1.trans four017_f5sq_f43sq_f73sq_lt_two)

lemma fSum_seventeen_cu :
    fSum (17 ^ 3) = (565699 : ℚ) / 534180 := by
  rw [fSum_prime_pow (by decide : Nat.Prime 17)]
  simp [sum_range_succ, sigma_one, sigma_prime (show Nat.Prime 17 by decide),
    sigma_eq_geom (show Nat.Prime 17 by decide)]
  norm_num

lemma four016_f5_f17cu_f113_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum (17 ^ 3) * fSum 113 := by
  rw [fSum_five, fSum_seventeen_cu, fSum_prime (by decide : Nat.Prime 113)]
  norm_num

lemma four017_f5_f17cu_f137sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (17 ^ 3) * fSum (137 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen_cu, fSum_prime_sq (by decide : Nat.Prime 137)]
  norm_num

lemma fSum_seventeen_pow_le_cu_add {k : ℕ} (h3 : 3 ≤ k) (h6 : k ≤ 6) :
    fSum (17 ^ k) ≤ fSum (17 ^ 3) + (1 : ℚ) / 83521 + 1 / 1419857 + 1 / 24137569 := by
  have hle : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  have hp : Nat.Prime 17 := by decide
  have hmono : fSum (17 ^ k) ≤ fSum (17 ^ 6) := fSum_le_of_exp_ge hp h6
  have h6val : fSum (17 ^ 6) ≤
      fSum (17 ^ 3) + (1 : ℚ) / 83521 + 1 / 1419857 + 1 / 24137569 := by
    have hdecomp : fSum (17 ^ 6) = fSum (17 ^ 3) +
        (1 : ℚ) / (sigma 1 (17 ^ 4)) + 1 / (sigma 1 (17 ^ 5)) +
        1 / (sigma 1 (17 ^ 6)) := by
      rw [fSum_prime_pow hp, fSum_prime_pow hp]
      rw [show (6 : ℕ) + 1 = 7 by norm_num, show (3 : ℕ) + 1 = 4 by norm_num]
      rw [sum_range_succ (n := 6), sum_range_succ (n := 5), sum_range_succ (n := 4)]
    have h4 : (sigma 1 (17 ^ 4) : ℚ) ≥ 83521 := by
      rw [sigma_eq_geom hp]; norm_num
    have h5 : (sigma 1 (17 ^ 5) : ℚ) ≥ 1419857 := by
      rw [sigma_eq_geom hp]; norm_num
    have h6 : (sigma 1 (17 ^ 6) : ℚ) ≥ 24137569 := by
      rw [sigma_eq_geom hp]; norm_num
    have hpos4 : (0 : ℚ) < sigma 1 (17 ^ 4) := by exact_mod_cast (sigma_pos 1 (17 ^ 4) (by decide))
    have hpos5 : (0 : ℚ) < sigma 1 (17 ^ 5) := by exact_mod_cast (sigma_pos 1 (17 ^ 5) (by decide))
    have hpos6 : (0 : ℚ) < sigma 1 (17 ^ 6) := by exact_mod_cast (sigma_pos 1 (17 ^ 6) (by decide))
    have u4 : (1 : ℚ) / (sigma 1 (17 ^ 4)) ≤ 1 / 83521 :=
      one_div_le_one_div_of_le (by norm_num) h4
    have u5 : (1 : ℚ) / (sigma 1 (17 ^ 5)) ≤ 1 / 1419857 :=
      one_div_le_one_div_of_le (by norm_num) h5
    have u6 : (1 : ℚ) / (sigma 1 (17 ^ 6)) ≤ 1 / 24137569 :=
      one_div_le_one_div_of_le (by norm_num) h6
    linarith [hdecomp, u4, u5, u6]
  exact hmono.trans h6val

lemma ge21_five_one_seventeen_high_third_ne_two {a kq r kr : ℕ}
    (ha : 21 ≤ a) (hr : r.Prime)
    (hr1 : r ≡ 1 [MOD 4]) (hr17 : 17 ≤ r) (hne17 : r ≠ 17)
    (hkq3 : 3 ≤ kq) (hkq6 : kq ≤ 6) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  have hrk : 1 ≤ kr := by omega
  have hqk : 1 ≤ kq := by omega
  have hr29 : 29 ≤ r := one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 hne17
  by_cases h113 : r ≤ 113
  · have hC : fSum (17 ^ 3) ≤ fSum (17 ^ kq) :=
      fSum_le_of_exp_ge (by decide : Nat.Prime 17) hkq3
    have hD : fSum 113 ≤ fSum r :=
      fSum_prime_anti hr (by decide : Nat.Prime 113) h113
    have hD' : fSum 113 ≤ fSum (r ^ kr) :=
      le_trans hD (fSum_ge_prime hr hkr)
    have hmin :=
      ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum (17 ^ 3)) (C := fSum 113)
        h14 (fSum_pos (by decide))
        (fSum_pos (pow_ne_zero 3 (by decide : (17 : ℕ) ≠ 0)))
        (fSum_pos (by decide)) four016_f5_f17cu_f113_gt_two
    have hmono := mul3_gt_of le_rfl hC hD'
      (fSum_pos (pow_ne_zero 3 (by decide : (17 : ℕ) ≠ 0))).le
      (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      (fSum_pos (by decide : (113 : ℕ) ≠ 0)).le
      (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))).le)
    rw [pow_one]
    exact ne_of_gt (lt_of_lt_of_le hmin hmono)
  · have hr137 : 137 ≤ r := by
      have : 97 ≤ r := by omega
      rcases prime_one_mod4_ge97_small_cases hr hr1 this with
        h97 | h101 | h109 | h113' | h137
      · omega
      · omega
      · omega
      · omega
      · exact h137
    have h2b := fSum_two_pow_lt_4017_2500 a
    have hC : fSum (17 ^ kq) ≤ fSum (17 ^ 3) +
        (1 : ℚ) / 83521 + 1 / 1419857 + 1 / 24137569 :=
      fSum_seventeen_pow_le_cu_add hkq3 hkq6
    have hD : fSum (r ^ kr) ≤ fSum (r ^ 2) := fSum_le_sq_of_exp_le_two hr hkr
    have hrs : fSum (r ^ 2) ≤ fSum (137 ^ 2) :=
      fSum_prime_sq_anti (by decide : Nat.Prime 137) hr hr137
    have hD' : fSum (r ^ kr) ≤ fSum (137 ^ 2) := le_trans hD hrs
    have hbound : (4017 : ℚ) / 2500 * fSum 5 *
        (fSum (17 ^ 3) + (1 : ℚ) / 83521 + 1 / 1419857 + 1 / 24137569) *
        fSum (137 ^ 2) < 2 := by
      rw [fSum_five, fSum_seventeen_cu, fSum_prime_sq (by decide : Nat.Prime 137)]
      norm_num
    have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kq) * fSum (r ^ kr) ≤
        (4017 : ℚ) / 2500 * fSum 5 *
          (fSum (17 ^ 3) + (1 : ℚ) / 83521 + 1 / 1419857 + 1 / 24137569) *
          fSum (137 ^ 2) := by
      rw [pow_one]
      have hA : fSum (2 ^ a) * fSum 5 ≤ (4017 : ℚ) / 2500 * fSum 5 :=
        (mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))).le
      have hB : fSum (2 ^ a) * fSum 5 * fSum (17 ^ kq) ≤
          (4017 : ℚ) / 2500 * fSum 5 *
            (fSum (17 ^ 3) + (1 : ℚ) / 83521 + 1 / 1419857 + 1 / 24137569) :=
        mul_le_mul hA hC (fSum_pos (pow_ne_zero kq (by decide : (17 : ℕ) ≠ 0))).le
          (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      exact mul_le_mul hB hD' (fSum_pos (pow_ne_zero kr hr.ne_zero)).le
        (mul_nonneg (mul_nonneg (by norm_num)
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          (add_nonneg (add_nonneg (add_nonneg
            (fSum_pos (pow_ne_zero 3 (by decide : (17 : ℕ) ≠ 0))).le (by norm_num))
            (by norm_num)) (by norm_num)))
    exact ne_of_lt (h1.trans_lt hbound)

lemma four016_f5_f89_f17_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 89 * fSum 17 := by
  rw [fSum_five, fSum_prime (by decide : Nat.Prime 89), fSum_seventeen]
  norm_num

lemma four017_f5_geom137_f17sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * ((137 : ℚ) / 136) * fSum (17 ^ 2) < 2 := by
  rw [fSum_five, fSum_seventeen_sq]; norm_num

lemma four017_f5_f97sq_f17_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (97 ^ 2) * fSum 17 < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 97), fSum_seventeen]
  norm_num

lemma four016_f5_f97_f17sq_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 97 * fSum (17 ^ 2) := by
  rw [fSum_five, fSum_prime (by decide : Nat.Prime 97), fSum_seventeen_sq]
  norm_num

lemma four017_f5_f101sq_f17_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (101 ^ 2) * fSum 17 < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 101), fSum_seventeen]
  norm_num

lemma four016_f5_f101_f17sq_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 101 * fSum (17 ^ 2) := by
  rw [fSum_five, fSum_prime (by decide : Nat.Prime 101), fSum_seventeen_sq]
  norm_num

lemma four017_f5_f109sq_f17_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (109 ^ 2) * fSum 17 < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 109), fSum_seventeen]
  norm_num

lemma four016_f5_f109_f17sq_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 109 * fSum (17 ^ 2) := by
  rw [fSum_five, fSum_prime (by decide : Nat.Prime 109), fSum_seventeen_sq]
  norm_num

lemma four017_f5_f113sq_f17_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * fSum (113 ^ 2) * fSum 17 < 2 := by
  rw [fSum_five, fSum_prime_sq (by decide : Nat.Prime 113), fSum_seventeen]
  norm_num

lemma four016_f5_f113_f17sq_gt_two :
    2 < (4016 : ℚ) / 2500 * fSum 5 * fSum 113 * fSum (17 ^ 2) := by
  rw [fSum_five, fSum_prime (by decide : Nat.Prime 113), fSum_seventeen_sq]
  norm_num

lemma ge21_five_one_high_seventeen_mid_ne_two {a q kq kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime)
    (hmid : q = 97 ∨ q = 101 ∨ q = 109 ∨ q = 113)
    (hkq3 : 3 ≤ kq) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (17 ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  have hσ := fSum_prime_pow_lt_geom (l := kq) hq
  have hqk : 1 ≤ kq := by omega
  cases hkr with
  | inl h1 =>
    subst h1
    have h2b := fSum_two_pow_lt_4017_2500 a
    have hgeom : (q : ℚ) / (q - 1) ≤ (97 : ℚ) / 96 := by
      have hq97 : 97 ≤ q := by
        rcases hmid with h | h | h | h <;> subst h <;> omega
      have := geom_le_of_prime_ge hq (by decide : 2 ≤ 97) hq97
      convert this using 1
      norm_num
    have hC : fSum (q ^ kq) < (97 : ℚ) / 96 := hσ.trans_le hgeom
    have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (17 ^ 1) <
        (4017 : ℚ) / 2500 * fSum 5 * ((97 : ℚ) / 96) * fSum 17 := by
      rw [pow_one, pow_one]
      have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
        mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
      have hB : fSum (2 ^ a) * fSum 5 * fSum (q ^ kq) <
          (4017 : ℚ) / 2500 * fSum 5 * ((97 : ℚ) / 96) :=
        mul_lt_mul hA hC.le (fSum_pos (pow_ne_zero kq hq.ne_zero))
          (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      exact mul_lt_mul_of_pos_right hB (fSum_pos (by decide))
    have hprod : (4017 : ℚ) / 2500 * fSum 5 * ((97 : ℚ) / 96) * fSum 17 < 2 := by
      rw [fSum_five, fSum_seventeen]; norm_num
    exact ne_of_lt (h1.trans hprod)
  | inr h2 =>
    subst h2
    have hC : fSum q ≤ fSum (q ^ kq) := fSum_le_of_exp_ge_one hq hqk
    rcases hmid with h | h | h | h
    · subst h
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 97) (C := fSum (17 ^ 2))
          h14 (fSum_pos (by decide)) (fSum_pos (by decide))
          (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0)))
          four016_f5_f97_f17sq_gt_two
      have hmono := mul3_gt_of le_rfl hC le_rfl
        (fSum_pos (by decide : (97 : ℕ) ≠ 0)).le
        (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le
        (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          (fSum_pos (pow_ne_zero kq (by decide : (97 : ℕ) ≠ 0))).le)
      rw [pow_one]
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
    · subst h
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 101) (C := fSum (17 ^ 2))
          h14 (fSum_pos (by decide)) (fSum_pos (by decide))
          (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0)))
          four016_f5_f101_f17sq_gt_two
      have hmono := mul3_gt_of le_rfl hC le_rfl
        (fSum_pos (by decide : (101 : ℕ) ≠ 0)).le
        (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le
        (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          (fSum_pos (pow_ne_zero kq (by decide : (101 : ℕ) ≠ 0))).le)
      rw [pow_one]
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
    · subst h
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 109) (C := fSum (17 ^ 2))
          h14 (fSum_pos (by decide)) (fSum_pos (by decide))
          (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0)))
          four016_f5_f109_f17sq_gt_two
      have hmono := mul3_gt_of le_rfl hC le_rfl
        (fSum_pos (by decide : (109 : ℕ) ≠ 0)).le
        (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le
        (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          (fSum_pos (pow_ne_zero kq (by decide : (109 : ℕ) ≠ 0))).le)
      rw [pow_one]
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)
    · subst h
      have hmin :=
        ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 113) (C := fSum (17 ^ 2))
          h14 (fSum_pos (by decide)) (fSum_pos (by decide))
          (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0)))
          four016_f5_f113_f17sq_gt_two
      have hmono := mul3_gt_of le_rfl hC le_rfl
        (fSum_pos (by decide : (113 : ℕ) ≠ 0)).le
        (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (pow_ne_zero 2 (by decide : (17 : ℕ) ≠ 0))).le
        (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
          (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
          (fSum_pos (pow_ne_zero kq (by decide : (113 : ℕ) ≠ 0))).le)
      rw [pow_one]
      exact ne_of_gt (lt_of_lt_of_le hmin hmono)

lemma ge21_five_one_high_seventeen_ne_two {a q kq kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime)
    (hq1 : q ≡ 1 [MOD 4]) (hq29 : 29 ≤ q)
    (hkq3 : 3 ≤ kq) (hkq6 : kq ≤ 6) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (17 ^ kr) ≠ 2 := by
  have h14 : 14 ≤ a := by omega
  have hqk : 1 ≤ kq := by omega
  by_cases h89 : q ≤ 89
  · have hC : fSum 89 ≤ fSum q :=
      fSum_prime_anti hq (by decide : Nat.Prime 89) h89
    have hC' : fSum 89 ≤ fSum (q ^ kq) :=
      le_trans hC (fSum_le_of_exp_ge_one hq hqk)
    have hD : fSum 17 ≤ fSum (17 ^ kr) :=
      fSum_ge_prime (by decide : Nat.Prime 17) hkr
    have hmin :=
      ge14_mul3_gt_two (n := a) (A := fSum 5) (B := fSum 89) (C := fSum 17)
        h14 (fSum_pos (by decide)) (fSum_pos (by decide)) (fSum_pos (by decide))
        four016_f5_f89_f17_gt_two
    have hmono := mul3_gt_of le_rfl hC' hD
      (fSum_pos (by decide : (89 : ℕ) ≠ 0)).le
      (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
      (fSum_pos (by decide : (17 : ℕ) ≠ 0)).le
      (mul_nonneg (mul_nonneg (fSum_pos (pow_ne_zero a two_ne_zero)).le
        (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        (fSum_pos (pow_ne_zero kq hq.ne_zero)).le)
    rw [pow_one]
    exact ne_of_gt (lt_of_lt_of_le hmin hmono)
  · by_cases h137 : 137 ≤ q
    · have h2b := fSum_two_pow_lt_4017_2500 a
      have hσ := fSum_prime_pow_lt_geom (l := kq) hq
      have hgeom : (q : ℚ) / (q - 1) ≤ (137 : ℚ) / 136 := by
        have := geom_le_of_prime_ge hq (by decide : 2 ≤ 137) h137
        convert this using 1
        norm_num
      have hC : fSum (q ^ kq) < (137 : ℚ) / 136 := hσ.trans_le hgeom
      have hD : fSum (17 ^ kr) ≤ fSum (17 ^ 2) :=
        fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 17) hkr
      have h1 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (17 ^ kr) <
          (4017 : ℚ) / 2500 * fSum 5 * ((137 : ℚ) / 136) * fSum (17 ^ 2) := by
        rw [pow_one]
        have hA : fSum (2 ^ a) * fSum 5 < (4017 : ℚ) / 2500 * fSum 5 :=
          mul_lt_mul_of_pos_right h2b (fSum_pos (by decide))
        have hB : fSum (2 ^ a) * fSum 5 * fSum (q ^ kq) <
            (4017 : ℚ) / 2500 * fSum 5 * ((137 : ℚ) / 136) :=
          mul_lt_mul hA hC.le (fSum_pos (pow_ne_zero kq hq.ne_zero))
            (mul_nonneg (by norm_num) (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le)
        exact mul_lt_mul hB hD
          (fSum_pos (pow_ne_zero kr (by decide : (17 : ℕ) ≠ 0)))
          (mul_nonneg (mul_nonneg (by norm_num)
            (fSum_pos (by decide : (5 : ℕ) ≠ 0)).le) (by norm_num))
      exact ne_of_lt (h1.trans four017_f5_geom137_f17sq_lt_two)
    · have : 97 ≤ q := by
        cases lt_or_ge q 97 with
        | inl hlt =>
          have : 90 ≤ q := by omega
          interval_cases q
          all_goals
            first
            | exact absurd hq (by decide)
            | simp [Nat.ModEq] at hq1
        | inr hge => exact hge
      rcases prime_one_mod4_ge97_small_cases hq hq1 this with
        h97 | h101 | h109 | h113 | h137'
      · exact ge21_five_one_high_seventeen_mid_ne_two ha hq (Or.inl h97) hkq3 hkr
      · exact ge21_five_one_high_seventeen_mid_ne_two ha hq
          (Or.inr (Or.inl h101)) hkq3 hkr
      · exact ge21_five_one_high_seventeen_mid_ne_two ha hq
          (Or.inr (Or.inr (Or.inl h109))) hkq3 hkr
      · exact ge21_five_one_high_seventeen_mid_ne_two ha hq
          (Or.inr (Or.inr (Or.inr h113))) hkq3 hkr
      · exact (h137 h137').elim

lemma ge21_five_two_high_third_ne_two {a q kq r kr : ℕ}
    (ha : 21 ≤ a) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hq1 : q ≡ 1 [MOD 4]) (hr1 : r ≡ 1 [MOD 4])
    (hq29 : 29 ≤ q) (hr17 : 17 ≤ r)
    (hkq3 : 3 ≤ kq) (hkq6 : kq ≤ 6) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  have hqk : 1 ≤ kq := by omega
  have hrk : 1 ≤ kr := by omega
  by_cases hr17eq : r = 17
  · subst hr17eq
    have hswap :
        fSum (2 ^ a) * fSum (5 ^ 2) * fSum (q ^ kq) * fSum (17 ^ kr) =
        fSum (2 ^ a) * fSum (5 ^ 2) * fSum (17 ^ kr) * fSum (q ^ kq) := by ring
    rw [hswap]
    exact ne_of_gt (ge21_five_two_seventeen_third_gt_two ha hq hrk hqk)
  · have hr29 : 29 ≤ r := one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 hr17eq
    -- Remaining: both primes ≥ 29. Close numerical range; finished below after
    -- the main extra4 argument is rewired.
    sorry

lemma fs4017_f5_geom37_f29sq_lt_two :
    (4017 : ℚ) / 2500 * fSum 5 * ((37 : ℚ) / 36) * fSum (29 ^ 2) < 2 := by
  rw [fSum_five, fSum_twenty_nine_sq]; norm_num

lemma ge21_five_one_high_ge37_twentynine_lt_two {a p k kr : ℕ}
    (ha : 21 ≤ a) (hp : p.Prime)
    (hp37 : 37 ≤ p) (hkr : kr = 1 ∨ kr = 2) :
    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (p ^ k) * fSum (29 ^ kr) < 2 := by
  have h2b := fSum_two_pow_lt_4017_2500 a
  have hσ := fSum_prime_pow_lt_geom (l := k) hp
  have hgeom : (p : ℚ) / (p - 1) ≤ (37 : ℚ) / 36 := by
    have := geom_le_of_prime_ge hp (by decide : 2 ≤ 37) hp37
    convert this using 1
    norm_num
  have hC : fSum (p ^ k) < (37 : ℚ) / 36 := hσ.trans_le hgeom
  have hD : fSum (29 ^ kr) ≤ fSum (29 ^ 2) :=
    fSum_le_sq_of_exp_le_two (by decide : Nat.Prime 29) hkr
  have h5pos := fSum_pos (by decide : (5 : ℕ) ≠ 0)
  have hppos := fSum_pos (pow_ne_zero k hp.ne_zero)
  have hrpos := fSum_pos (pow_ne_zero kr (by decide : (29 : ℕ) ≠ 0))
  have h1 : fSum (2 ^ a) * fSum (5 ^ 1) < (4017 : ℚ) / 2500 * fSum 5 := by
    rw [pow_one]
    exact mul_lt_mul_of_pos_right h2b h5pos
  have h2 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (p ^ k) <
      (4017 : ℚ) / 2500 * fSum 5 * ((37 : ℚ) / 36) :=
    mul_lt_mul h1 hC.le hppos (mul_nonneg (by norm_num) h5pos.le)
  have h3 : fSum (2 ^ a) * fSum (5 ^ 1) * fSum (p ^ k) * fSum (29 ^ kr) <
      (4017 : ℚ) / 2500 * fSum 5 * ((37 : ℚ) / 36) * fSum (29 ^ 2) :=
    mul_lt_mul h2 hD hrpos (mul_nonneg (mul_nonneg (by norm_num) h5pos.le) (by norm_num))
  exact h3.trans fs4017_f5_geom37_f29sq_lt_two

lemma ge21_extra4_five_is_neg1 {a kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r) (hqo : Odd q) (hro : Odd r)
    (hne5q : q ≠ 5) (hne5r : r ≠ 5)
    (hpk : kp = 1 ∨ kp = 2) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hqeq : padicValRat 2 (fSum (q ^ kq)) = -2)
    (hreq : padicValRat 2 (fSum (r ^ kr)) = -1) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  haveI := two_fact
  have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hreq
  have hr12 : kr = 1 ∨ kr = 2 := by
    have := exp_le_two_of_v2_eq_neg_one hr hro hrk hreq; omega
  have hqcl := v2_eq_neg_two_classification hq hqo hqk hqeq
  have hpk1 : 1 ≤ kp := by omega
  by_cases hr13eq : r = 13
  · subst hr13eq
    have hswap :
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (13 ^ kr) =
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (13 ^ kr) * fSum (q ^ kq) := by ring
    rw [hswap]
    exact ne_of_gt (ge21_has_five_thirteen_any_gt_two ha hq hpk1 hrk hqk)
  · rcases hqcl with ⟨hq3, hkq12⟩ | ⟨hq14, hkq3, hkq6⟩
    · rcases eq_three_or_ge_eleven_of_mod8_three hq hq3 with hq3eq | hq11
      · subst hq3eq
        have hgt := ge21_has_three_gt_two ha hqk
        have h2 : 1 < fSum (5 ^ kp) := fSum_gt_one_of_prime_pow (by decide) hpk1
        have h3 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
        have hpos : 0 < fSum (2 ^ a) * fSum (3 ^ kq) :=
          mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
            (fSum_pos (pow_ne_zero kq (by decide : (3 : ℕ) ≠ 0)))
        have hmid : 2 < fSum (2 ^ a) * fSum (3 ^ kq) * fSum (5 ^ kp) := by
          nlinarith
        have hpos2 : 0 < fSum (2 ^ a) * fSum (3 ^ kq) * fSum (5 ^ kp) :=
          mul_pos hpos (fSum_pos (pow_ne_zero kp (by decide : (5 : ℕ) ≠ 0)))
        have hswap :
            fSum (2 ^ a) * fSum (5 ^ kp) * fSum (3 ^ kq) * fSum (r ^ kr) =
            fSum (2 ^ a) * fSum (3 ^ kq) * fSum (5 ^ kp) * fSum (r ^ kr) := by ring
        rw [hswap]
        exact ne_of_gt (by nlinarith)
      · by_cases hq11eq : q = 11
        · subst hq11eq
          exact ne_of_gt (ge21_has_five_eleven_any_gt_two ha hr hpk1 hqk hrk)
        · by_cases hq19eq : q = 19
          · subst hq19eq
            cases hpk with
            | inl h1 =>
              subst h1
              have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
              by_cases hr17eq : r = 17
              · subst hr17eq
                exact ne_of_gt (ge21_five_one_nineteen_le53_gt_two ha hr
                  (by decide) (by omega : 1 ≤ kq) hrk)
              · have hr29 : 29 ≤ r :=
                  one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 hr17eq
                exact ge21_five_one_nineteen_third_ne_two ha hr hr1 hr29 hkq12 hr12
            | inr h2 =>
              subst h2
              exact ne_of_gt (ge21_five_two_nineteen_third_gt_two ha hr hqk hrk)
          · have hq13 : 13 ≤ q := prime_ge_thirteen_of_ge_eleven_ne hq hq11 hq11eq
            have hqne13 : q ≠ 13 := fun h => not_three_mod8_of_eq_thirteen (h ▸ hq3)
            have hq17 : 17 ≤ q := prime_ge_seventeen_of_ge_thirteen_ne hq hq13 hqne13
            have hq19le : 19 ≤ q := by
              have : q ≠ 17 := fun h => not_three_mod8_of_eq_seventeen (h ▸ hq3)
              have : q ≠ 18 := fun h => not_prime_eighteen (h ▸ hq)
              omega
            have hq43 : 43 ≤ q := by
              cases prime_eq_nineteen_or_ge_fortythree_of_mod8_three hq hq3 hq19le with
              | inl h => exact (hq19eq h).elim
              | inr h => exact h
            cases hpk with
            | inl h1 =>
              subst h1
              have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
              by_cases hr17eq : r = 17
              · subst hr17eq
                have hswap :
                    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (17 ^ kr) =
                    fSum (2 ^ a) * fSum (5 ^ 1) * fSum (17 ^ kr) * fSum (q ^ kq) :=
                  by ring
                rw [hswap]
                exact ge21_five_one_seventeen_mod8_three_ne_two ha hq hq3 hq43
                  hr12 hkq12
              · have hr29 := one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 hr17eq
                by_cases hr29eq : r = 29
                · subst hr29eq
                  have hswap :
                      fSum (2 ^ a) * fSum (5 ^ 1) * fSum (q ^ kq) * fSum (29 ^ kr) =
                      fSum (2 ^ a) * fSum (5 ^ 1) * fSum (29 ^ kr) * fSum (q ^ kq) :=
                    by ring
                  rw [hswap]
                  exact ne_of_lt (ge21_five_one_ge29_third_lt_two ha
                    (by decide : Nat.Prime 29) hq (by decide : (29 : ℕ) ≤ 29)
                    (le_trans (by decide : (37 : ℕ) ≤ 43) hq43) hr12 hkq12)
                · have hr37 : 37 ≤ r := by
                    rcases prime_one_mod4_ge29_mid_cases hr hr1 hr29 with h | h
                    · exact (hr29eq h).elim
                    · exact h
                  exact ne_of_lt (ge21_five_one_high_ge29_third_lt_two ha hq hr
                    (le_trans (by decide : (29 : ℕ) ≤ 43) hq43) hr37 hr12)
            | inr h2 =>
              subst h2
              have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
              exact ge21_five_two_mod8_three_third_ne_two ha hq hr hq3 hr1
                hq43 hr17 hkq12 hr12
    · by_cases hq13eq : q = 13
      · subst hq13eq
        exact ne_of_gt (ge21_has_five_thirteen_any_gt_two ha hr hpk1 hqk hrk)
      · by_cases hq17eq : q = 17
        · subst hq17eq
          cases hpk with
          | inl h1 =>
            subst h1
            have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
            exact ge21_five_one_seventeen_high_third_ne_two ha hr hr1 hr17
              (hqr.symm) hkq3 hkq6 hr12
          | inr h2 =>
            subst h2
            exact ne_of_gt (ge21_five_two_seventeen_third_gt_two ha hr hqk hrk)
        · have hq29 : 29 ≤ q := one_mod4_ge29_of_ge17_ne17 hq hq14
            (one_mod4_ge17_of_ne5_ne13 hq hq14 hne5q hq13eq) hq17eq
          cases hpk with
          | inl h1 =>
            subst h1
            have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
            by_cases hr17eq : r = 17
            · subst hr17eq
              exact ge21_five_one_high_seventeen_ne_two ha hq hq14 hq29
                hkq3 hkq6 hr12
            · have hr29 := one_mod4_ge29_of_ge17_ne17 hr hr1 hr17 hr17eq
              by_cases hr29eq : r = 29
              · subst hr29eq
                have hq37 : 37 ≤ q := by
                  rcases prime_one_mod4_ge29_mid_cases hq hq14 hq29 with hq29eq | hq37
                  · exact (hqr hq29eq).elim
                  · exact hq37
                exact ne_of_lt
                  (ge21_five_one_high_ge37_twentynine_lt_two ha hq hq37 hr12)
              · have hr37 : 37 ≤ r := by
                  rcases prime_one_mod4_ge29_mid_cases hr hr1 hr29 with h29 | h37
                  · exact (hr29eq h29).elim
                  · exact h37
                exact ne_of_lt (ge21_five_one_high_ge29_third_lt_two ha hq hr
                  hq29 hr37 hr12)
          | inr h2 =>
            subst h2
            have hr17 := one_mod4_ge17_of_ne5_ne13 hr hr1 hne5r hr13eq
            exact ge21_five_two_high_third_ne_two ha hq hr hqr hq14 hr1
              hq29 hr17 hkq3 hkq6 hr12

lemma ge21_three_v2_neg_four_has5 {a kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r) (hqo : Odd q) (hro : Odd r)
    (hne5q : q ≠ 5) (hne5r : r ≠ 5)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hvp : padicValRat 2 (fSum (5 ^ kp)) ≤ -1)
    (hvq : padicValRat 2 (fSum (q ^ kq)) ≤ -1)
    (hvr : padicValRat 2 (fSum (r ^ kr)) ≤ -1)
    (hvsum : padicValRat 2 (fSum (5 ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
               padicValRat 2 (fSum (r ^ kr)) = -4) :
    fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  haveI := two_fact
  have htrip := v2_sum_three_eq_neg_four hvp hvq hvr hvsum
  rcases htrip with ⟨hpeq, hqeq, hreq⟩ | ⟨hpeq, hqeq, hreq⟩ | ⟨hpeq, hqeq, hreq⟩
  · have hlog : Nat.log 2 (kp + 1) = 2 := by
      rw [log_of_v2_mod4_one (by decide) (by decide) (by decide) hpk] at hpeq
      omega
    obtain ⟨hkp3, hkp6⟩ := exp_mid_of_log_eq_two hpk hlog
    exact ge21_extra4_five_is_neg2 ha hq hr hqr hqo hro hne5q hne5r
      hkp3 hkp6 hqk hrk hqeq hreq
  · have hlog : Nat.log 2 (kp + 1) = 1 := by
      rw [log_of_v2_mod4_one (by decide) (by decide) (by decide) hpk] at hpeq
      omega
    have hkp12 : kp = 1 ∨ kp = 2 := by
      have := exp_le_two_of_log_eq_one hpk hlog; omega
    exact ge21_extra4_five_is_neg1 ha hq hr hqr hqo hro hne5q hne5r
      hkp12 hqk hrk hqeq hreq
  · have hlog : Nat.log 2 (kp + 1) = 1 := by
      rw [log_of_v2_mod4_one (by decide) (by decide) (by decide) hpk] at hpeq
      omega
    have hkp12 : kp = 1 ∨ kp = 2 := by
      have := exp_le_two_of_log_eq_one hpk hlog; omega
    have hswap :
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) =
        fSum (2 ^ a) * fSum (5 ^ kp) * fSum (r ^ kr) * fSum (q ^ kq) := by ring
    rw [hswap]
    exact ge21_extra4_five_is_neg1 ha hr hq hqr.symm hro hqo hne5r hne5q
      hkp12 hrk hqk hreq hqeq

lemma ge21_three_v2_neg_four_ne_two {a p kp q kq r kr : ℕ}
    (ha : 21 ≤ a)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpo : Odd p) (hqo : Odd q) (hro : Odd r)
    (hpk : 1 ≤ kp) (hqk : 1 ≤ kq) (hrk : 1 ≤ kr)
    (hvsum : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
               padicValRat 2 (fSum (r ^ kr)) = -4) :
    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) ≠ 2 := by
  haveI := two_fact
  have hvp : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
  have hvq : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
  have hvr : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
    Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
  by_cases hp5 : p = 5
  · subst hp5
    exact ge21_three_v2_neg_four_has5 ha hq hr hqr hqo hro
      (fun h => hpq h.symm) (fun h => hpr h.symm) hpk hqk hrk hvp hvq hvr hvsum
  · by_cases hq5 : q = 5
    · subst hq5
      have hswap :
          fSum (2 ^ a) * fSum (p ^ kp) * fSum (5 ^ kq) * fSum (r ^ kr) =
          fSum (2 ^ a) * fSum (5 ^ kq) * fSum (p ^ kp) * fSum (r ^ kr) := by ring
      rw [hswap]
      have hvsum' : padicValRat 2 (fSum (5 ^ kq)) + padicValRat 2 (fSum (p ^ kp)) +
          padicValRat 2 (fSum (r ^ kr)) = -4 := by linarith
      exact ge21_three_v2_neg_four_has5 ha hp hr hpr hpo hro
        (fun h => hpq h) (fun h => hqr h.symm) hqk hpk hrk hvq hvp hvr hvsum'
    · by_cases hr5 : r = 5
      · subst hr5
        have hswap :
            fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) * fSum (5 ^ kr) =
            fSum (2 ^ a) * fSum (5 ^ kr) * fSum (p ^ kp) * fSum (q ^ kq) := by ring
        rw [hswap]
        have hvsum' : padicValRat 2 (fSum (5 ^ kr)) + padicValRat 2 (fSum (p ^ kp)) +
            padicValRat 2 (fSum (q ^ kq)) = -4 := by linarith
        exact ge21_three_v2_neg_four_has5 ha hp hq hpq hpo hqo
          (fun h => hpr h) (fun h => hqr h) hrk hpk hqk hvr hvp hvq hvsum'
      · exact ge21_extra4_no_five_ne_two ha hp hq hr hpq hpr hqr hpo hqo hro
          hp5 hq5 hr5 hpk hqk hrk hvp hvq hvr hvsum

set_option maxHeartbeats 400000 in
/-- `a ≡ 21 [MOD 32]`, at least three odd prime factors. -/
lemma fSum_mod32_twentyone_omega_ge_three_not_int
    {a m : ℕ} (ha : 1 ≤ a) (ha21 : a ≡ 21 [MOD 32])
    (hodd : Odd m) (hm : 1 < m) (hω : 3 ≤ m.primeFactors.card) :
    (fSum (2 ^ a) * fSum m).den ≠ 1 := by
  haveI := two_fact
  have hm0 : m ≠ 0 := by omega
  have ha21n : 21 ≤ a := by
    have : a % 32 = 21 := by simpa [Nat.ModEq] using ha21
    omega
  have hv2m : padicValRat 2 (fSum m) ≤ - (m.primeFactors.card : ℤ) :=
    v2_fSum_odd_le_neg_omega hodd hm
  have hgt : 1 < fSum (2 ^ a) * fSum m := by
    have h1 := fSum_two_pow_gt_one ha
    have h2 : 1 < fSum m := fSum_gt_one hm
    nlinarith [fSum_pos (pow_ne_zero a two_ne_zero), fSum_pos hm0]
  have hv2prod_eq : padicValRat 2 (fSum (2 ^ a) * fSum m) =
      padicValRat 2 (fSum (2 ^ a)) + padicValRat 2 (fSum m) :=
    padicValRat.mul (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
      (fSum_ne_zero hm0)
  have h2n : 2 ∉ m.primeFactors := by
    intro h
    exact Nat.not_even_iff_odd.mpr hodd
      (even_iff_two_dvd.mpr (dvd_of_mem_primeFactors h))
  cases mod32_twentyone_of_mod64 ha21 with
  | inl ha21_64 =>
    have hv2a : padicValRat 2 (fSum (2 ^ a)) = 5 :=
      v2_fSum_two_pow_mod64_twentyone ha21_64
    by_cases hneg : padicValRat 2 (fSum (2 ^ a) * fSum m) < 0
    · exact den_ne_one_of_neg_padic hneg
    · have hωle : m.primeFactors.card ≤ 5 := by
        have : (m.primeFactors.card : ℤ) ≤ 5 := by
          have := hv2m
          have : 0 ≤ padicValRat 2 (fSum (2 ^ a) * fSum m) := le_of_not_gt hneg
          rw [hv2prod_eq, hv2a] at this
          linarith
        exact_mod_cast this
      have hω345 : m.primeFactors.card = 3 ∨ m.primeFactors.card = 4 ∨
          m.primeFactors.card = 5 := by omega
      rcases hω345 with hω3 | hω4 | hω5
      · obtain ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hs, hm_eq⟩ :=
          eq_three_prime_pows_of_card_eq_three hm0 hω3
        set kp := m.factorization p
        set kq := m.factorization q
        set kr := m.factorization r
        have hpk : 1 ≤ kp := by
          have : p ∈ m.primeFactors := by simp [hs]
          exact factorization_pos_of_mem_primeFactors this
        have hqk : 1 ≤ kq := by
          have : q ∈ m.primeFactors := by simp [hs]
          exact factorization_pos_of_mem_primeFactors this
        have hrk : 1 ≤ kr := by
          have : r ∈ m.primeFactors := by simp [hs]
          exact factorization_pos_of_mem_primeFactors this
        have hpo : Odd p :=
          hp.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
        have hqo : Odd q :=
          hq.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
        have hro : Odd r :=
          hr.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
        have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
          Nat.coprime_pow_primes kp kq hp hq hpq
        have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
          refine Nat.Coprime.mul_left ?_ ?_
          · exact Nat.coprime_pow_primes kp kr hp hr hpr
          · exact Nat.coprime_pow_primes kq kr hq hr hqr
        have hfm : fSum m =
            fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
          rw [hm_eq, fSum_mul hcop2, fSum_mul hcop1]
        have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
        have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
        have hv2r : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
        have hv2msum : padicValRat 2 (fSum m) =
            padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) := by
          rw [hfm, padicValRat.mul
              (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
              (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)),
            padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
              (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
        have hp3or := odd_prime_eq_three_or_ge_five hp hpo
        have hq3or := odd_prime_eq_three_or_ge_five hq hqo
        have hr3or := odd_prime_eq_three_or_ge_five hr hro
        by_cases hhas3 : p = 3 ∨ q = 3 ∨ r = 3
        · have hgt2 : 2 < fSum (2 ^ a) * fSum m := by
            rcases hhas3 with hp3 | hq3 | hr3
            · subst hp3
              have h1 := ge21_has_three_gt_two ha21n hpk
              have h2 : 1 < fSum (q ^ kq) := fSum_gt_one_of_prime_pow hq hqk
              have h3 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
              have hpos : 0 < fSum (2 ^ a) * fSum (3 ^ kp) :=
                mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
                  (fSum_pos (pow_ne_zero kp (by decide : (3 : ℕ) ≠ 0)))
              have hmid : 2 < fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) := by
                nlinarith [h1, h2, hpos]
              have hpos2 : 0 < fSum (2 ^ a) * fSum (3 ^ kp) * fSum (q ^ kq) :=
                mul_pos hpos (fSum_pos (pow_ne_zero kq hq.ne_zero))
              rw [hfm]
              nlinarith [hmid, h3, hpos2]
            · subst hq3
              have h1 := ge21_has_three_gt_two ha21n hqk
              have h2 : 1 < fSum (p ^ kp) := fSum_gt_one_of_prime_pow hp hpk
              have h3 : 1 < fSum (r ^ kr) := fSum_gt_one_of_prime_pow hr hrk
              have hpos : 0 < fSum (2 ^ a) * fSum (3 ^ kq) :=
                mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
                  (fSum_pos (pow_ne_zero kq (by decide : (3 : ℕ) ≠ 0)))
              have hmid : 2 < fSum (2 ^ a) * fSum (3 ^ kq) * fSum (p ^ kp) := by
                nlinarith [h1, h2, hpos]
              have hpos2 : 0 < fSum (2 ^ a) * fSum (3 ^ kq) * fSum (p ^ kp) :=
                mul_pos hpos (fSum_pos (pow_ne_zero kp hp.ne_zero))
              rw [hfm]
              nlinarith [hmid, h3, hpos2]
            · subst hr3
              have h1 := ge21_has_three_gt_two ha21n hrk
              have h2 : 1 < fSum (p ^ kp) := fSum_gt_one_of_prime_pow hp hpk
              have h3 : 1 < fSum (q ^ kq) := fSum_gt_one_of_prime_pow hq hqk
              have hpos : 0 < fSum (2 ^ a) * fSum (3 ^ kr) :=
                mul_pos (fSum_pos (pow_ne_zero a two_ne_zero))
                  (fSum_pos (pow_ne_zero kr (by decide : (3 : ℕ) ≠ 0)))
              have hmid : 2 < fSum (2 ^ a) * fSum (3 ^ kr) * fSum (p ^ kp) := by
                nlinarith [h1, h2, hpos]
              have hpos2 : 0 < fSum (2 ^ a) * fSum (3 ^ kr) * fSum (p ^ kp) :=
                mul_pos hpos (fSum_pos (pow_ne_zero kp hp.ne_zero))
              rw [hfm]
              nlinarith [hmid, h3, hpos2]
          have hlt4 : fSum (2 ^ a) * fSum m < 4 := by
            rw [hfm]
            rcases hhas3 with hp3 | hq3 | hr3
            · subst hp3
              have hq5 : 5 ≤ q := by
                rcases hq3or with hq3' | hq5
                · exact (hpq hq3'.symm).elim
                · exact hq5
              have hr5 : 5 ≤ r := by
                rcases hr3or with hr3' | hr5
                · exact (hpr hr3'.symm).elim
                · exact hr5
              have hbound :=
                fSum_two_three_two_ge5_lt_four (a := a) (k := kp)
                  (p := q) (l := kq) (q := r) (s := kr) hq hr hq5 hr5
              convert hbound using 1; ring
            · subst hq3
              have hp5 : 5 ≤ p := by
                rcases hp3or with hp3' | hp5
                · exact (hpq hp3').elim
                · exact hp5
              have hr5 : 5 ≤ r := by
                rcases hr3or with hr3' | hr5
                · exact (hqr hr3'.symm).elim
                · exact hr5
              have hbound :=
                fSum_two_three_two_ge5_lt_four (a := a) (k := kq)
                  (p := p) (l := kp) (q := r) (s := kr) hp hr hp5 hr5
              convert hbound using 1; ring
            · subst hr3
              have hp5 : 5 ≤ p := by
                rcases hp3or with hp3' | hp5
                · exact (hpr hp3').elim
                · exact hp5
              have hq5 : 5 ≤ q := by
                rcases hq3or with hq3' | hq5
                · exact (hqr hq3').elim
                · exact hq5
              have hbound :=
                fSum_two_three_two_ge5_lt_four (a := a) (k := kr)
                  (p := p) (l := kp) (q := q) (s := kq) hp hq hp5 hq5
              convert hbound using 1; ring
          have hne2 : fSum (2 ^ a) * fSum m ≠ 2 := ne_of_gt hgt2
          by_cases hv0 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 0
          · have hv5 : padicValRat 2 (fSum m) = -5 := by
              have : padicValRat 2 (fSum (2 ^ a) * fSum m) =
                  5 + padicValRat 2 (fSum m) := by rw [hv2prod_eq, hv2a]
              omega
            have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
              have hassoc :
                  fSum (2 ^ a) * fSum m =
                    fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) *
                      fSum (r ^ kr) := by rw [hfm]; ring
              rw [hassoc]
              refine ge21_has_three_v2m_neg_five_lt_three ha21n hp hq hr
                hpq hpr hqr hpo hqo hro hpk hqk hrk hhas3 ?_
              rw [← hv2msum, hv5]
            have hne3 : fSum (2 ^ a) * fSum m ≠ 3 := ne_of_lt hlt3
            exact den_ne_one_of_lt_four_ne_two_ne_three hgt hlt4 hne2 hne3
          · have hne3 : fSum (2 ^ a) * fSum m ≠ 3 := by
              intro h
              have : padicValRat 2 (fSum (2 ^ a) * fSum m) = 0 := by
                haveI := two_fact
                rw [h, show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num,
                  padicValRat.of_nat]
                exact_mod_cast padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)
              exact hv0 this
            exact den_ne_one_of_lt_four_ne_two_ne_three hgt hlt4 hne2 hne3
        · have hp5 : 5 ≤ p := by
            rcases hp3or with hp3 | hp5
            · exact (hhas3 (Or.inl hp3)).elim
            · exact hp5
          have hq5 : 5 ≤ q := by
            rcases hq3or with hq3 | hq5
            · exact (hhas3 (Or.inr (Or.inl hq3))).elim
            · exact hq5
          have hr5 : 5 ≤ r := by
            rcases hr3or with hr3 | hr5
            · exact (hhas3 (Or.inr (Or.inr hr3))).elim
            · exact hr5
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
            rw [hfm]
            have hbound :=
              fSum_three_prime_pows_lt_three (a := a) (k := kp) (l := kq) (s := kr)
                hp hq hr hp5 hq5 hr5
            convert hbound using 1; ring
          by_cases hextra : padicValRat 2 (fSum m) ≤ -4
          · have hv2prod : padicValRat 2 (fSum (2 ^ a) * fSum m) =
                5 + padicValRat 2 (fSum m) := by
              rw [hv2prod_eq, hv2a]
            by_cases hle5 : padicValRat 2 (fSum m) ≤ -5
            · have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by
                linarith
              exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv
            · have hv4 : padicValRat 2 (fSum m) = -4 := by omega
              have hv1 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 1 := by
                rw [hv2prod, hv4]; norm_num
              have hne2 : fSum (2 ^ a) * fSum m ≠ 2 := by
                rw [hfm]
                have hvsum : padicValRat 2 (fSum (p ^ kp)) +
                    padicValRat 2 (fSum (q ^ kq)) +
                    padicValRat 2 (fSum (r ^ kr)) = -4 := by
                  rw [← hv2msum, hv4]
                have h := ge21_three_v2_neg_four_ne_two ha21n hp hq hr
                  hpq hpr hqr hpo hqo hro hpk hqk hrk hvsum
                convert h using 1; ring
              exact den_ne_one_of_mem_Ioo_ne_two hgt hlt3 hne2
          · have hv3 : padicValRat 2 (fSum m) = -3 := by
              have : -3 ≤ padicValRat 2 (fSum m) := by linarith [hv2m, hω3]
              omega
            have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by
              rw [hv2prod_eq, hv2a, hv3]; norm_num
            exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv
      · obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hp, hq, hr, hss, hset, hm_eq⟩ :=
          eq_four_prime_pows_of_card_eq_four hm0 hω4
        set kp := m.factorization p
        set kq := m.factorization q
        set kr := m.factorization r
        set ks := m.factorization s
        have hpk : 1 ≤ kp := by
          have : p ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hqk : 1 ≤ kq := by
          have : q ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hrk : 1 ≤ kr := by
          have : r ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hsk : 1 ≤ ks := by
          have : s ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hpo : Odd p :=
          hp.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hqo : Odd q :=
          hq.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hro : Odd r :=
          hr.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hso : Odd s :=
          hss.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
          Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
        have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
          Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
        have hv2r : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
          Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
        have hv2s : padicValRat 2 (fSum (s ^ ks)) ≤ -1 :=
          Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hss hso hsk)
        have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
          Nat.coprime_pow_primes kp kq hp hq hpq
        have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
          refine Nat.Coprime.mul_left ?_ ?_
          · exact Nat.coprime_pow_primes kp kr hp hr hpr
          · exact Nat.coprime_pow_primes kq kr hq hr hqr
        have hcop3 : Nat.Coprime (p ^ kp * q ^ kq * r ^ kr) (s ^ ks) := by
          refine Nat.Coprime.mul_left ?_ ?_
          · refine Nat.Coprime.mul_left ?_ ?_
            · exact Nat.coprime_pow_primes kp ks hp hss hps
            · exact Nat.coprime_pow_primes kq ks hq hss hqs
          · exact Nat.coprime_pow_primes kr ks hr hss hrs
        have hfm : fSum m =
            fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) * fSum (s ^ ks) := by
          rw [hm_eq, fSum_mul hcop3, fSum_mul hcop2, fSum_mul hcop1]
        have hv2msum : padicValRat 2 (fSum m) =
            padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) := by
          rw [hfm]
          rw [padicValRat.mul
              (mul_ne_zero
                (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                  (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
                (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)))
              (fSum_ne_zero (pow_ne_zero _ hss.ne_zero))]
          rw [padicValRat.mul
              (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
              (fSum_ne_zero (pow_ne_zero _ hr.ne_zero))]
          rw [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
              (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
        have hvle : padicValRat 2 (fSum m) ≤ -4 := by rw [hv2msum]; linarith
        have hv2prod : padicValRat 2 (fSum (2 ^ a) * fSum m) =
            5 + padicValRat 2 (fSum m) := by rw [hv2prod_eq, hv2a]
        by_cases hle5 : padicValRat 2 (fSum m) ≤ -5
        · have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by linarith
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
            have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three
              (fun h => h2n (by simp [hset, h])) (fun h => by
                have : padicValRat 2 (fSum (3 ^ kp)) ≤ -2 :=
                  v2_fSum_odd_prime_pow_mod4_three (h ▸ hp) (h ▸ hpo) (by decide) hpk
                have : padicValRat 2 (fSum m) ≤ -5 := by rw [hv2msum]; linarith
                exact this)
            sorry
          exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv
        · have hv4 : padicValRat 2 (fSum m) = -4 := by omega
          have hv2peq : padicValRat 2 (fSum (p ^ kp)) = -1 := by
            have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
                padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) = -4 :=
              by rw [← hv2msum, hv4]
            omega
          have hv2qeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by
            have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
                padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) = -4 :=
              by rw [← hv2msum, hv4]
            omega
          have hv2req : padicValRat 2 (fSum (r ^ kr)) = -1 := by
            have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
                padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) = -4 :=
              by rw [← hv2msum, hv4]
            omega
          have hv2seq : padicValRat 2 (fSum (s ^ ks)) = -1 := by
            have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
                padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) = -4 :=
              by rw [← hv2msum, hv4]
            omega
          have hp1 := mod4_one_of_v2_eq_neg_one hp hpo hpk hv2peq
          have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hv2qeq
          have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hv2req
          have hs1 := mod4_one_of_v2_eq_neg_one hss hso hsk hv2seq
          have hkp12 : kp = 1 ∨ kp = 2 := by
            have := exp_le_two_of_v2_eq_neg_one hp hpo hpk hv2peq; omega
          have hkq12 : kq = 1 ∨ kq = 2 := by
            have := exp_le_two_of_v2_eq_neg_one hq hqo hqk hv2qeq; omega
          have hkr12 : kr = 1 ∨ kr = 2 := by
            have := exp_le_two_of_v2_eq_neg_one hr hro hrk hv2req; omega
          have hks12 : ks = 1 ∨ ks = 2 := by
            have := exp_le_two_of_v2_eq_neg_one hss hso hsk hv2seq; omega
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
            rw [hfm]
            have hbound := fSum_four_one_mod4_any_lt_three (a := a)
              hp hq hr hss hpq hpr hps hqr hqs hrs
              hp1 hq1 hr1 hs1 hkp12 hkq12 hkr12 hks12
            convert hbound using 1; ring
          have hne2 : fSum (2 ^ a) * fSum m ≠ 2 := by
            rw [hfm]
            by_cases hhas5 : p = 5 ∨ q = 5 ∨ r = 5 ∨ s = 5
            · by_cases hhas13 : p = 13 ∨ q = 13 ∨ r = 13 ∨ s = 13
              · -- 5 and 13: product > 2
                sorry
              · -- 5, no 13: remaining ≥ 17
                sorry
            · -- no 5: all ≥ 13, product < 2 after sorting
              sorry
          exact den_ne_one_of_mem_Ioo_ne_two hgt hlt3 hne2
      · exact fSum_mod64_twentyone_omega_five_not_int ha21_64 hodd hm hω5 hneg
  | inr ha53 =>
    have hv2a6 : 6 ≤ padicValRat 2 (fSum (2 ^ a)) :=
      v2_fSum_two_pow_mod64_fiftythree ha53
    have hv2prod : padicValRat 2 (fSum (2 ^ a) * fSum m) =
        padicValRat 2 (fSum (2 ^ a)) + padicValRat 2 (fSum m) := hv2prod_eq
    have hge : 0 ≤ padicValRat 2 (fSum (2 ^ a) * fSum m) := le_of_not_gt hneg
    have hv2m_ge : -6 ≤ padicValRat 2 (fSum m) := by linarith
    have hωle : m.primeFactors.card ≤ 6 := by
      have : (m.primeFactors.card : ℤ) ≤ 6 := by linarith [hv2m]
      exact_mod_cast this
    cases mod64_fiftythree_of_mod128 ha53 with
    | inl ha53_128 =>
      have hv2a : padicValRat 2 (fSum (2 ^ a)) = 6 :=
        v2_fSum_two_pow_mod128_fiftythree ha53_128
      by_cases hle5 : padicValRat 2 (fSum m) ≤ -5
      · by_cases hle6 : padicValRat 2 (fSum m) ≤ -6
        · have hv6 : padicValRat 2 (fSum m) = -6 := by omega
          have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by
            rw [hv2prod, hv2a, hv6]; norm_num
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
            have h2 := fSum_two_pow_lt_13_8 a
            have hm' : fSum m < (3 : ℚ) / 2 := by
              -- crude: ω≥3 odd, each fSum < 5/4? not always (f3=5/4)
              have : fSum m < 2 := by
                have hgt1 : 1 < fSum m := fSum_gt_one hm
                have := fSum_three_prime_pows_lt_three (a := 0) (k := 1) (l := 1)
                  (s := 1) (hp := by
                    have hne : m.primeFactors.Nonempty := by
                      rw [Nat.nonempty_primeFactors]; omega
                    exact minFac_prime (by omega)) 
                sorry
              nlinarith [fSum_pos (pow_ne_zero a two_ne_zero)]
            nlinarith [fSum_pos (pow_ne_zero a two_ne_zero), fSum_pos hm0]
          exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv
        · have hv5 : padicValRat 2 (fSum m) = -5 := by omega
          have hv1 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 1 := by
            rw [hv2prod, hv2a, hv5]; norm_num
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
            sorry
          have hne2 : fSum (2 ^ a) * fSum m ≠ 2 := by
            sorry
          exact den_ne_one_of_mem_Ioo_ne_two hgt hlt3 hne2
      · have : padicValRat 2 (fSum m) ≥ -4 := by linarith
        have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by
          rw [hv2prod, hv2a]; linarith
        have hlt3 : fSum (2 ^ a) * fSum m < 3 := by sorry
        exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv
    | inr ha117 =>
      have hv2a : 7 ≤ padicValRat 2 (fSum (2 ^ a)) :=
        v2_fSum_two_pow_mod128_onehundredseventeen ha117
      by_cases hle6 : padicValRat 2 (fSum m) ≤ -6
      · have hv6 : padicValRat 2 (fSum m) = -6 := by omega
        by_cases hv7 : padicValRat 2 (fSum (2 ^ a)) = 7
        · have hv1 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 1 := by
            rw [hv2prod, hv7, hv6]; norm_num
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by sorry
          have hne2 : fSum (2 ^ a) * fSum m ≠ 2 := by sorry
          exact den_ne_one_of_mem_Ioo_ne_two hgt hlt3 hne2
        · have : 8 ≤ padicValRat 2 (fSum (2 ^ a)) := by omega
          have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by
            rw [hv2prod, hv6]; linarith
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by sorry
          exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv
      · have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by
          rw [hv2prod]; linarith
        have hlt3 : fSum (2 ^ a) * fSum m < 3 := by sorry
        exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv

/-- `a ≡ 5 [MOD 16]`, at least three odd prime factors. -/
lemma fSum_mod16_five_omega_ge_three_not_int
    {a m : ℕ} (ha : 1 ≤ a) (ha5 : a ≡ 5 [MOD 16])
    (hodd : Odd m) (hm : 1 < m) (hω : 3 ≤ m.primeFactors.card) :
    (fSum (2 ^ a) * fSum m).den ≠ 1 := by
  haveI := two_fact
  have hm0 : m ≠ 0 := by omega
  have hv2m : padicValRat 2 (fSum m) ≤ - (m.primeFactors.card : ℤ) :=
    v2_fSum_odd_le_neg_omega hodd hm
  have hgt : 1 < fSum (2 ^ a) * fSum m := by
    have h1 := fSum_two_pow_gt_one ha
    have h2 : 1 < fSum m := fSum_gt_one hm
    nlinarith [fSum_pos (pow_ne_zero a two_ne_zero), fSum_pos hm0]
  have hv2prod_eq : padicValRat 2 (fSum (2 ^ a) * fSum m) =
      padicValRat 2 (fSum (2 ^ a)) + padicValRat 2 (fSum m) :=
    padicValRat.mul (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
      (fSum_ne_zero hm0)
  have hage : 5 ≤ a := by
    have : a % 16 = 5 := by simpa [Nat.ModEq] using ha5
    omega
  have h2n : 2 ∉ m.primeFactors := by
    intro h
    exact Nat.not_even_iff_odd.mpr hodd
      (even_iff_two_dvd.mpr (dvd_of_mem_primeFactors h))
  cases mod16_five_of_mod32 ha5 with
  | inl ha5_32 =>
    have hv2a : padicValRat 2 (fSum (2 ^ a)) = 4 :=
      v2_fSum_two_pow_mod32_five ha5_32
    have hv2le : padicValRat 2 (fSum (2 ^ a) * fSum m) ≤
        4 - (m.primeFactors.card : ℤ) := by
      rw [hv2prod_eq, hv2a]; linarith
    by_cases hneg : padicValRat 2 (fSum (2 ^ a) * fSum m) < 0
    · exact den_ne_one_of_neg_padic hneg
    · have hωle : m.primeFactors.card ≤ 4 := by
        have : (m.primeFactors.card : ℤ) ≤ 4 := by
          have := hv2le; linarith
        exact_mod_cast this
      have hω34 : m.primeFactors.card = 3 ∨ m.primeFactors.card = 4 := by omega
      cases hω34 with
      | inl hω3 =>
        obtain ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hs, hm_eq⟩ :=
          eq_three_prime_pows_of_card_eq_three hm0 hω3
        set kp := m.factorization p
        set kq := m.factorization q
        set kr := m.factorization r
        have hpk : 1 ≤ kp := by
          have : p ∈ m.primeFactors := by simp [hs]
          exact factorization_pos_of_mem_primeFactors this
        have hqk : 1 ≤ kq := by
          have : q ∈ m.primeFactors := by simp [hs]
          exact factorization_pos_of_mem_primeFactors this
        have hrk : 1 ≤ kr := by
          have : r ∈ m.primeFactors := by simp [hs]
          exact factorization_pos_of_mem_primeFactors this
        have hpo : Odd p :=
          hp.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
        have hqo : Odd q :=
          hq.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
        have hro : Odd r :=
          hr.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
        have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
          Nat.coprime_pow_primes kp kq hp hq hpq
        have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
          refine Nat.Coprime.mul_left ?_ ?_
          · exact Nat.coprime_pow_primes kp kr hp hr hpr
          · exact Nat.coprime_pow_primes kq kr hq hr hqr
        have hfm : fSum m =
            fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
          rw [hm_eq, fSum_mul hcop2, fSum_mul hcop1]
        have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
        have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
        have hv2r : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
        have hv2msum : padicValRat 2 (fSum m) =
            padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) := by
          rw [hfm, padicValRat.mul
              (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
              (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)),
            padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
              (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
        by_cases hextra : padicValRat 2 (fSum m) ≤ -4
        · have hnv : padicValRat 2 (fSum (2 ^ a) * fSum m) ≠ 1 := by
            rw [hv2prod_eq, hv2a]; linarith
          have hp3or := odd_prime_eq_three_or_ge_five hp hpo
          have hq3or := odd_prime_eq_three_or_ge_five hq hqo
          have hr3or := odd_prime_eq_three_or_ge_five hr hro
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
            rw [hfm]
            rcases hp3or with hp3 | hp5'
            · subst hp3
              rcases hq3or with hq3 | hq5'
              · exact (hpq hq3.symm).elim
              · rcases hr3or with hr3 | hr5'
                · exact (hpr hr3.symm).elim
                · have hv3le : padicValRat 2 (fSum (3 ^ kp)) ≤ -2 :=
                    v2_fSum_odd_prime_pow_mod4_three Nat.prime_three
                      (by decide) (by decide) hpk
                  have hvsum4 : padicValRat 2 (fSum (3 ^ kp)) +
                      padicValRat 2 (fSum (q ^ kq)) +
                      padicValRat 2 (fSum (r ^ kr)) = -4 := by
                    have hle : padicValRat 2 (fSum m) ≤ -4 := hextra
                    have hge : -4 ≤ padicValRat 2 (fSum m) := by
                      have : 0 ≤ padicValRat 2 (fSum (2 ^ a) * fSum m) :=
                        le_of_not_gt hneg
                      rw [hv2prod_eq, hv2a] at this; linarith
                    have : padicValRat 2 (fSum m) = -4 := by linarith
                    rw [← hv2msum]; exact this
                  have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by omega
                  have hvreq : padicValRat 2 (fSum (r ^ kr)) = -1 := by omega
                  have hkq12 := exp_le_two_of_v2_eq_neg_one hq hqo hqk hvqeq
                  have hkr12 := exp_le_two_of_v2_eq_neg_one hr hro hrk hvreq
                  have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hvqeq
                  have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hvreq
                  have hkp2 : kp ≤ 2 := by
                    have hform := v2_fSum_eq_one_sub Nat.prime_three
                      (by decide : Odd 3) hpk
                    have : padicValNat 2 (3 + 1) = 2 := padicValNat_two_four
                    have hlog : Nat.log 2 (kp + 1) = 1 := by
                      rw [hform] at hv3le
                      have : 1 ≤ Nat.log 2 (kp + 1) :=
                        Nat.log_pos (by decide) (by omega)
                      omega
                    exact exp_le_two_of_log_eq_one hpk hlog
                  have hswap : q ≤ r ∨ r ≤ q := le_total q r
                  cases hswap with
                  | inl hle =>
                    have hr13 : 13 ≤ r := by
                      have : r ≠ 5 := by
                        intro h
                        have : q = 5 := by
                          have hqle5 : q ≤ 5 := h ▸ hle
                          have : 5 ≤ q := five_le_of_mod4_one hq hq1
                          omega
                        exact hqr (this.trans h.symm)
                      rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
                      · exact (this h5).elim
                      · exact h13.symm ▸ le_rfl
                      · omega
                      · omega
                    have hbound := fSum_two_three_two_one_mod4_lt_three
                      (a := a) (k := kp) (p := q) (l := kq) (q := r) (s := kr)
                      hq hr hq5' hr13 hkp2 hkq12 hkr12
                    convert hbound using 1; ring
                  | inr hle =>
                    have hq13 : 13 ≤ q := by
                      have : q ≠ 5 := by
                        intro h
                        have : r = 5 := by
                          have hrle5 : r ≤ 5 := h ▸ hle
                          have : 5 ≤ r := five_le_of_mod4_one hr hr1
                          omega
                        exact hqr (h.trans this.symm)
                      rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
                      · exact (this h5).elim
                      · exact h13.symm ▸ le_rfl
                      · omega
                      · omega
                    have hbound := fSum_two_three_two_one_mod4_lt_three
                      (a := a) (k := kp) (p := r) (l := kr) (q := q) (s := kq)
                      hr hq hr5' hq13 hkp2 hkr12 hkq12
                    convert hbound using 1; ring
            · rcases hq3or with hq3 | hq5'
              · subst hq3
                rcases hr3or with hr3 | hr5'
                · exact (hqr hr3.symm).elim
                · have hv3le : padicValRat 2 (fSum (3 ^ kq)) ≤ -2 :=
                    v2_fSum_odd_prime_pow_mod4_three Nat.prime_three
                      (by decide) (by decide) hqk
                  have hvsum4 : padicValRat 2 (fSum (p ^ kp)) +
                      padicValRat 2 (fSum (3 ^ kq)) +
                      padicValRat 2 (fSum (r ^ kr)) = -4 := by
                    have hge : -4 ≤ padicValRat 2 (fSum m) := by
                      have : 0 ≤ padicValRat 2 (fSum (2 ^ a) * fSum m) :=
                        le_of_not_gt hneg
                      rw [hv2prod_eq, hv2a] at this; linarith
                    have : padicValRat 2 (fSum m) = -4 := by linarith [hextra]
                    rw [← hv2msum]; exact this
                  have hvpeq : padicValRat 2 (fSum (p ^ kp)) = -1 := by omega
                  have hvreq : padicValRat 2 (fSum (r ^ kr)) = -1 := by omega
                  have hkp12 := exp_le_two_of_v2_eq_neg_one hp hpo hpk hvpeq
                  have hkr12 := exp_le_two_of_v2_eq_neg_one hr hro hrk hvreq
                  have hp1 := mod4_one_of_v2_eq_neg_one hp hpo hpk hvpeq
                  have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hvreq
                  have hkq2 : kq ≤ 2 := by
                    have hform := v2_fSum_eq_one_sub Nat.prime_three
                      (by decide : Odd 3) hqk
                    have : padicValNat 2 (3 + 1) = 2 := padicValNat_two_four
                    have hlog : Nat.log 2 (kq + 1) = 1 := by
                      rw [hform] at hv3le
                      have : 1 ≤ Nat.log 2 (kq + 1) :=
                        Nat.log_pos (by decide) (by omega)
                      omega
                    exact exp_le_two_of_log_eq_one hqk hlog
                  have hswap : p ≤ r ∨ r ≤ p := le_total p r
                  cases hswap with
                  | inl hle =>
                    have hr13 : 13 ≤ r := by
                      have : r ≠ 5 := by
                        intro h
                        have : p = 5 := by
                          have : p ≤ 5 := h ▸ hle
                          have : 5 ≤ p := five_le_of_mod4_one hp hp1
                          omega
                        exact hpr (this.trans h.symm)
                      rcases prime_one_mod_four_cases hr hr1 with h5 | h13 | h17 | hge
                      · exact (this h5).elim
                      · exact h13.symm ▸ le_rfl
                      · omega
                      · omega
                    have hbound := fSum_two_three_two_one_mod4_lt_three
                      (a := a) (k := kq) (p := p) (l := kp) (q := r) (s := kr)
                      hp hr hp5' hr13 hkq2 hkp12 hkr12
                    convert hbound using 1; ring
                  | inr hle =>
                    have hp13 : 13 ≤ p := by
                      have : p ≠ 5 := by
                        intro h
                        have : r = 5 := by
                          have : r ≤ 5 := h ▸ hle
                          have : 5 ≤ r := five_le_of_mod4_one hr hr1
                          omega
                        exact hpr (h.trans this.symm)
                      rcases prime_one_mod_four_cases hp hp1 with h5 | h13 | h17 | hge
                      · exact (this h5).elim
                      · exact h13.symm ▸ le_rfl
                      · omega
                      · omega
                    have hbound := fSum_two_three_two_one_mod4_lt_three
                      (a := a) (k := kq) (p := r) (l := kr) (q := p) (s := kp)
                      hr hp hr5' hp13 hkq2 hkr12 hkp12
                    convert hbound using 1; ring
              · rcases hr3or with hr3 | hr5'
                · subst hr3
                  have hv3le : padicValRat 2 (fSum (3 ^ kr)) ≤ -2 :=
                    v2_fSum_odd_prime_pow_mod4_three Nat.prime_three
                      (by decide) (by decide) hrk
                  have hvsum4 : padicValRat 2 (fSum (p ^ kp)) +
                      padicValRat 2 (fSum (q ^ kq)) +
                      padicValRat 2 (fSum (3 ^ kr)) = -4 := by
                    have hge : -4 ≤ padicValRat 2 (fSum m) := by
                      have : 0 ≤ padicValRat 2 (fSum (2 ^ a) * fSum m) :=
                        le_of_not_gt hneg
                      rw [hv2prod_eq, hv2a] at this; linarith
                    have : padicValRat 2 (fSum m) = -4 := by linarith [hextra]
                    rw [← hv2msum]; exact this
                  have hvpeq : padicValRat 2 (fSum (p ^ kp)) = -1 := by omega
                  have hvqeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by omega
                  have hkp12 := exp_le_two_of_v2_eq_neg_one hp hpo hpk hvpeq
                  have hkq12 := exp_le_two_of_v2_eq_neg_one hq hqo hqk hvqeq
                  have hp1 := mod4_one_of_v2_eq_neg_one hp hpo hpk hvpeq
                  have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hvqeq
                  have hkr2 : kr ≤ 2 := by
                    have hform := v2_fSum_eq_one_sub Nat.prime_three
                      (by decide : Odd 3) hrk
                    have : padicValNat 2 (3 + 1) = 2 := padicValNat_two_four
                    have hlog : Nat.log 2 (kr + 1) = 1 := by
                      rw [hform] at hv3le
                      have : 1 ≤ Nat.log 2 (kr + 1) :=
                        Nat.log_pos (by decide) (by omega)
                      omega
                    exact exp_le_two_of_log_eq_one hrk hlog
                  have hswap : p ≤ q ∨ q ≤ p := le_total p q
                  cases hswap with
                  | inl hle =>
                    have hq13 : 13 ≤ q := by
                      have : q ≠ 5 := by
                        intro h
                        have : p = 5 := by
                          have : p ≤ 5 := h ▸ hle
                          have : 5 ≤ p := five_le_of_mod4_one hp hp1
                          omega
                        exact hpq (this.trans h.symm)
                      rcases prime_one_mod_four_cases hq hq1 with h5 | h13 | h17 | hge
                      · exact (this h5).elim
                      · exact h13.symm ▸ le_rfl
                      · omega
                      · omega
                    have hbound := fSum_two_three_two_one_mod4_lt_three
                      (a := a) (k := kr) (p := p) (l := kp) (q := q) (s := kq)
                      hp hq hp5' hq13 hkr2 hkp12 hkq12
                    convert hbound using 1; ring
                  | inr hle =>
                    have hp13 : 13 ≤ p := by
                      have : p ≠ 5 := by
                        intro h
                        have : q = 5 := by
                          have : q ≤ 5 := h ▸ hle
                          have : 5 ≤ q := five_le_of_mod4_one hq hq1
                          omega
                        exact hpq (h.trans this.symm)
                      rcases prime_one_mod_four_cases hp hp1 with h5 | h13 | h17 | hge
                      · exact (this h5).elim
                      · exact h13.symm ▸ le_rfl
                      · omega
                      · omega
                    have hbound := fSum_two_three_two_one_mod4_lt_three
                      (a := a) (k := kr) (p := q) (l := kq) (q := p) (s := kp)
                      hq hp hq5' hp13 hkr2 hkq12 hkp12
                    convert hbound using 1; ring
                · have hbound :=
                    fSum_three_prime_pows_lt_three (a := a) (k := kp) (l := kq)
                      (s := kr) hp hq hr hp5' hq5' hr5'
                  convert hbound using 1; ring
          exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 hnv
        · have hv3 : padicValRat 2 (fSum m) = -3 := by
            have : -3 ≤ padicValRat 2 (fSum m) := by linarith [hv2m, hω3]
            have : ¬ padicValRat 2 (fSum m) ≤ -4 := hextra
            omega
          have hv2peq : padicValRat 2 (fSum (p ^ kp)) = -1 := by
            have : padicValRat 2 (fSum (p ^ kp)) +
                padicValRat 2 (fSum (q ^ kq)) +
                padicValRat 2 (fSum (r ^ kr)) = -3 := by
              rw [← hv2msum, hv3]
            omega
          have hv2qeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by
            have : padicValRat 2 (fSum (p ^ kp)) +
                padicValRat 2 (fSum (q ^ kq)) +
                padicValRat 2 (fSum (r ^ kr)) = -3 := by
              rw [← hv2msum, hv3]
            omega
          have hv2req : padicValRat 2 (fSum (r ^ kr)) = -1 := by
            have : padicValRat 2 (fSum (p ^ kp)) +
                padicValRat 2 (fSum (q ^ kq)) +
                padicValRat 2 (fSum (r ^ kr)) = -3 := by
              rw [← hv2msum, hv3]
            omega
          have hkp12 := exp_le_two_of_v2_eq_neg_one hp hpo hpk hv2peq
          have hkq12 := exp_le_two_of_v2_eq_neg_one hq hqo hqk hv2qeq
          have hkr12 := exp_le_two_of_v2_eq_neg_one hr hro hrk hv2req
          have hp1 := mod4_one_of_v2_eq_neg_one hp hpo hpk hv2peq
          have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hv2qeq
          have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hv2req
          have hp5 : 5 ≤ p := five_le_of_mod4_one hp hp1
          have hq5 : 5 ≤ q := five_le_of_mod4_one hq hq1
          have hr5 : 5 ≤ r := five_le_of_mod4_one hr hr1
          have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
            rw [hfm]
            have hbound :=
              fSum_three_prime_pows_lt_three (a := a) (k := kp) (l := kq) (s := kr)
                hp hq hr hp5 hq5 hr5
            convert hbound using 1; ring
          have hv2prod1 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 1 := by
            rw [hv2prod_eq, hv2a, hv3]; norm_num
          -- remaining: show ≠ 2
          have hne2 : fSum (2 ^ a) * fSum m ≠ 2 := by
            rw [hfm]
            have hkp12' : kp = 1 ∨ kp = 2 := by omega
            have hkq12' : kq = 1 ∨ kq = 2 := by omega
            have hkr12' : kr = 1 ∨ kr = 2 := by omega
            have ha_cases : a = 5 ∨ 21 ≤ a := by
              have : a % 32 = 5 := by simpa [Nat.ModEq] using ha5_32
              omega
            cases ha_cases with
            | inl haeq =>
              subst haeq
              have h := five_three_one_mod4_ne_two hp hq hr hpq hpr hqr
                hp1 hq1 hr1 hkp12' hkq12' hkr12'
              convert h using 1; ring
            | inr ha21' =>
              have h := ge21_three_one_mod4_ne_two ha21' hp hq hr hpq hpr hqr
                hp1 hq1 hr1 hkp12' hkq12' hkr12'
              convert h using 1; ring
          exact den_ne_one_of_mem_Ioo_ne_two hgt hlt3 hne2
      | inr hω4 =>
        obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hp, hq, hr, hss, hset, hm_eq⟩ :=
          eq_four_prime_pows_of_card_eq_four hm0 hω4
        set kp := m.factorization p
        set kq := m.factorization q
        set kr := m.factorization r
        set ks := m.factorization s
        have hpk : 1 ≤ kp := by
          have : p ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hqk : 1 ≤ kq := by
          have : q ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hrk : 1 ≤ kr := by
          have : r ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hsk : 1 ≤ ks := by
          have : s ∈ m.primeFactors := by simp [hset]
          exact factorization_pos_of_mem_primeFactors this
        have hpo : Odd p :=
          hp.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hqo : Odd q :=
          hq.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hro : Odd r :=
          hr.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hso : Odd s :=
          hss.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hset]) h2n)
        have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
        have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
        have hv2r : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
        have hv2s : padicValRat 2 (fSum (s ^ ks)) ≤ -1 :=
          Int.le_sub_one_of_lt
            (padicValRat_two_fSum_odd_prime_pow_neg hss hso hsk)
        have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
          Nat.coprime_pow_primes kp kq hp hq hpq
        have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
          refine Nat.Coprime.mul_left ?_ ?_
          · exact Nat.coprime_pow_primes kp kr hp hr hpr
          · exact Nat.coprime_pow_primes kq kr hq hr hqr
        have hcop3 : Nat.Coprime
            (p ^ kp * q ^ kq * r ^ kr) (s ^ ks) := by
          refine Nat.Coprime.mul_left ?_ ?_
          · refine Nat.Coprime.mul_left ?_ ?_
            · exact Nat.coprime_pow_primes kp ks hp hss hps
            · exact Nat.coprime_pow_primes kq ks hq hss hqs
          · exact Nat.coprime_pow_primes kr ks hr hss hrs
        have hfm : fSum m =
            fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) * fSum (s ^ ks) := by
          rw [hm_eq, fSum_mul hcop3, fSum_mul hcop2, fSum_mul hcop1]
        have hv2msum : padicValRat 2 (fSum m) =
            padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) := by
          rw [hfm]
          rw [padicValRat.mul
              (mul_ne_zero
                (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                  (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
                (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)))
              (fSum_ne_zero (pow_ne_zero _ hss.ne_zero))]
          rw [padicValRat.mul
              (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
              (fSum_ne_zero (pow_ne_zero _ hr.ne_zero))]
          rw [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
              (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
        have hv4 : padicValRat 2 (fSum m) = -4 := by
          have hle : padicValRat 2 (fSum m) ≤ -4 := by
            rw [hv2msum]; linarith
          have hge : -4 ≤ padicValRat 2 (fSum m) := by
            have : padicValRat 2 (fSum (2 ^ a) * fSum m) ≥ 0 := by
              push_neg at hneg; exact hneg
            rw [hv2prod_eq, hv2a] at this
            linarith
          linarith
        have hv2peq : padicValRat 2 (fSum (p ^ kp)) = -1 := by
          have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) =
              -4 := by rw [← hv2msum, hv4]
          omega
        have hv2qeq : padicValRat 2 (fSum (q ^ kq)) = -1 := by
          have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) =
              -4 := by rw [← hv2msum, hv4]
          omega
        have hv2req : padicValRat 2 (fSum (r ^ kr)) = -1 := by
          have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) =
              -4 := by rw [← hv2msum, hv4]
          omega
        have hv2seq : padicValRat 2 (fSum (s ^ ks)) = -1 := by
          have : padicValRat 2 (fSum (p ^ kp)) + padicValRat 2 (fSum (q ^ kq)) +
              padicValRat 2 (fSum (r ^ kr)) + padicValRat 2 (fSum (s ^ ks)) =
              -4 := by rw [← hv2msum, hv4]
          omega
        have hkp12 := exp_le_two_of_v2_eq_neg_one hp hpo hpk hv2peq
        have hkq12 := exp_le_two_of_v2_eq_neg_one hq hqo hqk hv2qeq
        have hkr12 := exp_le_two_of_v2_eq_neg_one hr hro hrk hv2req
        have hks12 := exp_le_two_of_v2_eq_neg_one hss hso hsk hv2seq
        have hp1 := mod4_one_of_v2_eq_neg_one hp hpo hpk hv2peq
        have hq1 := mod4_one_of_v2_eq_neg_one hq hqo hqk hv2qeq
        have hr1 := mod4_one_of_v2_eq_neg_one hr hro hrk hv2req
        have hs1 := mod4_one_of_v2_eq_neg_one hss hso hsk hv2seq
        have hp5 : 5 ≤ p := five_le_of_mod4_one hp hp1
        have hq5 : 5 ≤ q := five_le_of_mod4_one hq hq1
        have hr5 : 5 ≤ r := five_le_of_mod4_one hr hr1
        have hs5 : 5 ≤ s := five_le_of_mod4_one hss hs1
        have hkp12' : kp = 1 ∨ kp = 2 := by omega
        have hkq12' : kq = 1 ∨ kq = 2 := by omega
        have hkr12' : kr = 1 ∨ kr = 2 := by omega
        have hks12' : ks = 1 ∨ ks = 2 := by omega
        have hlt3 : fSum (2 ^ a) * fSum m < 3 := by
          rw [hfm]
          have hbound :=
            fSum_four_one_mod4_any_lt_three (a := a)
              hp hq hr hss hpq hpr hps hqr hqs hrs
              hp1 hq1 hr1 hs1 hkp12' hkq12' hkr12' hks12'
          convert hbound using 1
          ring
        have hv0 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 0 := by
          rw [hv2prod_eq, hv2a, hv4]; norm_num
        exact den_ne_one_of_lt_three_v2_ne_one hgt hlt3 (by rw [hv0]; decide)
  | inr ha21 =>
    exact fSum_mod32_twentyone_omega_ge_three_not_int ha ha21 hodd hm hω


/-- `a ≡ 5 [MOD 8]`, at least three odd prime factors. -/
lemma fSum_mod8_five_omega_ge_three_not_int
    {a m : ℕ} (ha : 1 ≤ a) (ha5 : a ≡ 5 [MOD 8])
    (hodd : Odd m) (hm : 1 < m) (hω : 3 ≤ m.primeFactors.card) :
    (fSum (2 ^ a) * fSum m).den ≠ 1 := by
  haveI := two_fact
  have hm0 : m ≠ 0 := by omega
  have hv2m : padicValRat 2 (fSum m) ≤ - (m.primeFactors.card : ℤ) :=
    v2_fSum_odd_le_neg_omega hodd hm
  have hv2m3 : padicValRat 2 (fSum m) ≤ -3 := by
    have : (3 : ℤ) ≤ m.primeFactors.card := by exact_mod_cast hω
    linarith
  have hgt : 1 < fSum (2 ^ a) * fSum m := by
    have h1 := fSum_two_pow_gt_one ha
    have h2 : 1 < fSum m := fSum_gt_one hm
    nlinarith [fSum_pos (pow_ne_zero a two_ne_zero), fSum_pos hm0]
  cases mod8_five_of_mod16 ha5 with
  | inl ha5_16 =>
    -- a ≡ 5 [MOD 16]: handled by a further 32-adic split
    exact fSum_mod16_five_omega_ge_three_not_int ha ha5_16 hodd hm hω
  | inr ha13 =>
    have hv2a : padicValRat 2 (fSum (2 ^ a)) = 3 :=
      v2_fSum_two_pow_mod16_thirteen ha13
    have hv2prod : padicValRat 2 (fSum (2 ^ a) * fSum m) =
        3 + padicValRat 2 (fSum m) := by
      rw [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
        (fSum_ne_zero hm0), hv2a]
    have hv2le : padicValRat 2 (fSum (2 ^ a) * fSum m) ≤ 0 := by
      linarith
    by_cases hneg : padicValRat 2 (fSum (2 ^ a) * fSum m) < 0
    · exact den_ne_one_of_neg_padic hneg
    · have hv0 : padicValRat 2 (fSum (2 ^ a) * fSum m) = 0 := by linarith
      have hv2m_eq : padicValRat 2 (fSum m) = -3 := by
        have : 3 + padicValRat 2 (fSum m) = 0 := by
          rw [← hv2prod, hv0]
        linarith
      have hωeq : m.primeFactors.card = 3 := by
        have hle : (m.primeFactors.card : ℤ) ≤ 3 := by
          have := hv2m
          linarith
        omega
      obtain ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hs, hm_eq⟩ :=
        eq_three_prime_pows_of_card_eq_three hm0 hωeq
      set kp := m.factorization p
      set kq := m.factorization q
      set kr := m.factorization r
      have hpk : 1 ≤ kp := by
        have : p ∈ m.primeFactors := by simp [hs]
        exact factorization_pos_of_mem_primeFactors this
      have hqk : 1 ≤ kq := by
        have : q ∈ m.primeFactors := by simp [hs]
        exact factorization_pos_of_mem_primeFactors this
      have hrk : 1 ≤ kr := by
        have : r ∈ m.primeFactors := by simp [hs]
        exact factorization_pos_of_mem_primeFactors this
      have h2n : 2 ∉ m.primeFactors := by
        intro h
        exact Nat.not_even_iff_odd.mpr hodd
          (even_iff_two_dvd.mpr (dvd_of_mem_primeFactors h))
      have hpo : Odd p := hp.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
      have hqo : Odd q := hq.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
      have hro : Odd r := hr.odd_of_ne_two (ne_of_mem_of_not_mem (by simp [hs]) h2n)
      have hp5 : 5 ≤ p := by
        rcases odd_prime_eq_three_or_ge_five hp hpo with hp3 | hp5
        · -- if p = 3 then v2(fSum(3^kp)) ≤ -2, so v2(m) ≤ -4, contradiction
          have hv3 : padicValRat 2 (fSum (3 ^ kp)) ≤ -2 := by
            subst hp3
            exact v2_fSum_odd_prime_pow_mod4_three Nat.prime_three
              (by decide) (by decide) hpk
          have hvq : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
            Int.le_sub_one_of_lt
              (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
          have hvr : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
            Int.le_sub_one_of_lt
              (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
          have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
            Nat.coprime_pow_primes kp kq hp hq hpq
          have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
            refine Nat.Coprime.mul_left ?_ ?_
            · exact Nat.coprime_pow_primes kp kr hp hr hpr
            · exact Nat.coprime_pow_primes kq kr hq hr hqr
          have hfm : fSum m =
              fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
            rw [hm_eq, fSum_mul hcop2, fSum_mul hcop1]
          have : padicValRat 2 (fSum m) ≤ -4 := by
            rw [hfm, padicValRat.mul
                (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                  (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
                (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)),
              padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
            subst hp3
            linarith
          linarith
        · exact hp5
      have hq5 : 5 ≤ q := by
        rcases odd_prime_eq_three_or_ge_five hq hqo with hq3 | hq5
        · have hv3 : padicValRat 2 (fSum (3 ^ kq)) ≤ -2 := by
            subst hq3
            exact v2_fSum_odd_prime_pow_mod4_three Nat.prime_three
              (by decide) (by decide) hqk
          have hvp : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
            Int.le_sub_one_of_lt
              (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
          have hvr : padicValRat 2 (fSum (r ^ kr)) ≤ -1 :=
            Int.le_sub_one_of_lt
              (padicValRat_two_fSum_odd_prime_pow_neg hr hro hrk)
          have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
            Nat.coprime_pow_primes kp kq hp hq hpq
          have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
            refine Nat.Coprime.mul_left ?_ ?_
            · exact Nat.coprime_pow_primes kp kr hp hr hpr
            · exact Nat.coprime_pow_primes kq kr hq hr hqr
          have hfm : fSum m =
              fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
            rw [hm_eq, fSum_mul hcop2, fSum_mul hcop1]
          have : padicValRat 2 (fSum m) ≤ -4 := by
            rw [hfm, padicValRat.mul
                (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                  (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
                (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)),
              padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
            subst hq3
            linarith
          linarith
        · exact hq5
      have hr5 : 5 ≤ r := by
        rcases odd_prime_eq_three_or_ge_five hr hro with hr3 | hr5
        · have hv3 : padicValRat 2 (fSum (3 ^ kr)) ≤ -2 := by
            subst hr3
            exact v2_fSum_odd_prime_pow_mod4_three Nat.prime_three
              (by decide) (by decide) hrk
          have hvp : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
            Int.le_sub_one_of_lt
              (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpk)
          have hvq : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
            Int.le_sub_one_of_lt
              (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqk)
          have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
            Nat.coprime_pow_primes kp kq hp hq hpq
          have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
            refine Nat.Coprime.mul_left ?_ ?_
            · exact Nat.coprime_pow_primes kp kr hp hr hpr
            · exact Nat.coprime_pow_primes kq kr hq hr hqr
          have hfm : fSum m =
              fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
            rw [hm_eq, fSum_mul hcop2, fSum_mul hcop1]
          have : padicValRat 2 (fSum m) ≤ -4 := by
            rw [hfm, padicValRat.mul
                (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                  (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))
                (fSum_ne_zero (pow_ne_zero _ hr.ne_zero)),
              padicValRat.mul (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
            subst hr3
            linarith
          linarith
        · exact hr5
      have hcop1 : Nat.Coprime (p ^ kp) (q ^ kq) :=
        Nat.coprime_pow_primes kp kq hp hq hpq
      have hcop2 : Nat.Coprime (p ^ kp * q ^ kq) (r ^ kr) := by
        refine Nat.Coprime.mul_left ?_ ?_
        · exact Nat.coprime_pow_primes kp kr hp hr hpr
        · exact Nat.coprime_pow_primes kq kr hq hr hqr
      have hfm : fSum m =
          fSum (p ^ kp) * fSum (q ^ kq) * fSum (r ^ kr) := by
        rw [hm_eq, fSum_mul hcop2, fSum_mul hcop1]
      have hlt : fSum (2 ^ a) * fSum m < 3 := by
        rw [hfm]
        have hbound :=
          fSum_three_prime_pows_lt_three (a := a) (k := kp) (l := kq) (s := kr)
            hp hq hr hp5 hq5 hr5
        convert hbound using 1
        ring
      exact den_ne_one_of_lt_three_v2_ne_one hgt hlt (by
        rw [hv0]; decide)

/-- `a ≡ 5 [MOD 8]`, two odd prime factors, “big” exponents or a 3 (mod 4) prime. -/
lemma fSum_mod8_five_omega_two_big_not_int
    {a p kp q kq : ℕ} (ha : 1 ≤ a) (ha5 : a ≡ 5 [MOD 8])
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpo : Odd p) (hqo : Odd q) (hpkp : 1 ≤ kp) (hqkp : 1 ≤ kq)
    (hbig : 3 ≤ kp ∨ 3 ≤ kq ∨ p ≡ 3 [MOD 4] ∨ q ≡ 3 [MOD 4]) :
    (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))).den ≠ 1 := by
  haveI := two_fact
  have hv2m : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) ≤ -3 := by
    rw [padicValRat.mul
      (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
      (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
    have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
      Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpkp)
    have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
      Int.le_sub_one_of_lt (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqkp)
    rcases hbig with hkp3 | hkq3 | hp3 | hq3
    · have : padicValRat 2 (fSum (p ^ kp)) ≤ -2 :=
        v2_fSum_odd_prime_pow_exp_ge_three hp hpo hkp3
      linarith
    · have : padicValRat 2 (fSum (q ^ kq)) ≤ -2 :=
        v2_fSum_odd_prime_pow_exp_ge_three hq hqo hkq3
      linarith
    · have : padicValRat 2 (fSum (p ^ kp)) ≤ -2 :=
        v2_fSum_odd_prime_pow_mod4_three hp hpo hp3 hpkp
      linarith
    · have : padicValRat 2 (fSum (q ^ kq)) ≤ -2 :=
        v2_fSum_odd_prime_pow_mod4_three hq hqo hq3 hqkp
      linarith
  have hgt : 1 < fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) := by
    have := fSum_two_mul_two_prime_pows_gt_one ha hp hq hpkp hqkp
    linarith
  have hlt : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) < 3 :=
    fSum_two_mul_two_prime_pows_lt_three' hp hq hpq hpo hqo
  have hlt' : fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq)) < 3 := by
    convert hlt using 1; ring
  cases mod8_five_of_mod16 ha5 with
  | inl ha5_16 =>
    exact fSum_mod16_five_omega_two_big_not_int
      ha ha5_16 hp hq hpq hpo hqo hpkp hqkp hbig
  | inr ha13 =>
    have hv2a : padicValRat 2 (fSum (2 ^ a)) = 3 :=
      v2_fSum_two_pow_mod16_thirteen ha13
    have hv2prod : padicValRat 2
        (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) =
        3 + padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) := by
      rw [padicValRat.mul (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
        (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
          (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))), hv2a]
    have : padicValRat 2
        (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) ≠ 1 := by
      linarith
    exact den_ne_one_of_lt_three_v2_ne_one hgt hlt' this

theorem oeis_265709_conjecture_0.disproof :
    ¬ (∃ (n : ℕ), 1 < n ∧
      ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1) := by
  rintro ⟨n, hn, hden⟩
  have hn0 : n ≠ 0 := by omega
  rw [← fSum_apply n] at hden
  haveI := two_fact
  by_cases hodd : Odd n
  · exact den_ne_one_of_neg_padic (padicValRat_two_fSum_odd hodd hn) hden
  · have he : Even n := Nat.not_odd_iff_even.mp hodd
    have ha_pos : 1 ≤ n.factorization 2 := factorization_two_pos_of_even he hn0
    set a := n.factorization 2
    set m := ordCompl[2] n
    have hdecomp : fSum n = fSum (2 ^ a) * fSum m := fSum_eq_mul_odd_part hn0
    have hm_odd : Odd m := odd_ordCompl n hn0
    rw [hdecomp] at hden
    by_cases hm1 : m = 1
    · rw [hm1, fSum_one, mul_one] at hden
      exact fSum_two_pow_not_int ha_pos hden
    · have hmgt : 1 < m := by
        have : 0 < m := Nat.ordCompl_pos 2 hn0
        omega
      by_cases ha_even : Even a
      · have hv2 : padicValRat 2 (fSum (2 ^ a) * fSum m) < 0 := by
          rw [padicValRat.mul
            (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
            (fSum_ne_zero (by omega))]
          have h1 := v2_fSum_two_pow_of_even ha_even
          have h2 := padicValRat_two_fSum_odd hm_odd hmgt
          linarith
        exact den_ne_one_of_neg_padic hv2 hden
      · have ha_odd : Odd a := Nat.not_even_iff_odd.mp ha_even
        have hm0 : m ≠ 0 := by omega
        have h2nm : 2 ∉ m.primeFactors := by
          intro h
          exact Nat.not_even_iff_odd.mpr hm_odd
            (even_iff_two_dvd.mpr (dvd_of_mem_primeFactors h))
        by_cases hmod : a ≡ 3 [MOD 4]
        · have hv2a : padicValRat 2 (fSum (2 ^ a)) = 1 :=
            v2_fSum_two_pow_mod4_three hmod
          by_cases hω : 2 ≤ m.primeFactors.card
          · have hv2m : padicValRat 2 (fSum m) ≤ -2 := by
              have := v2_fSum_odd_le_neg_omega hm_odd hmgt
              have : (2 : ℤ) ≤ m.primeFactors.card := by exact_mod_cast hω
              linarith
            have hv2 : padicValRat 2 (fSum (2 ^ a) * fSum m) < 0 := by
              rw [padicValRat.mul
                (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
                (fSum_ne_zero hm0)]
              linarith
            exact den_ne_one_of_neg_padic hv2 hden
          · have hω1 : m.primeFactors.card = 1 := by
              have hne : m.primeFactors.Nonempty := by
                rw [Nat.nonempty_primeFactors]
                omega
              have : 1 ≤ m.primeFactors.card := Finset.card_pos.mpr hne
              omega
            have hm_pow := eq_minFac_pow_of_card_primeFactors_eq_one hmgt hω1
            set p := m.minFac
            set k := m.factorization p
            have hp : p.Prime := minFac_prime (by omega)
            have hk : 1 ≤ k := by
              have : p ∈ m.primeFactors := by
                have : p ∣ m := minFac_dvd m
                exact mem_primeFactors.mpr ⟨hp, this, hm0⟩
              exact factorization_pos_of_mem_primeFactors this
            have hpo : Odd p := hp.odd_of_ne_two (by
              intro h2
              apply h2nm
              have : p ∈ m.primeFactors :=
                mem_primeFactors.mpr ⟨hp, minFac_dvd m, hm0⟩
              rwa [h2] at this)
            rw [hm_pow] at hden
            by_cases hp3 : p ≡ 3 [MOD 4]
            · have hv2m : padicValRat 2 (fSum (p ^ k)) ≤ -2 :=
                v2_fSum_odd_prime_pow_mod4_three hp hpo hp3 hk
              have hv2 : padicValRat 2 (fSum (2 ^ a) * fSum (p ^ k)) < 0 := by
                rw [padicValRat.mul
                  (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
                  (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))]
                linarith
              exact den_ne_one_of_neg_padic hv2 hden
            · have hp5 : 5 ≤ p := by
                have hp2 : p ≠ 2 := by
                  intro h2; apply h2nm
                  have : p ∈ m.primeFactors :=
                    mem_primeFactors.mpr ⟨hp, minFac_dvd m, hm0⟩
                  rwa [h2] at this
                have hp3' : p ≠ 3 := by
                  intro h3
                  have : p % 4 = 3 := by simp [h3]
                  have : p ≡ 3 [MOD 4] := by simpa [Nat.ModEq] using this
                  exact hp3 this
                exact hp.five_le_of_ne_two_of_ne_three hp2 hp3'
              have hlt : fSum (2 ^ a) * fSum (p ^ k) < 2 :=
                fSum_two_pow_mul_prime_lt_two hp hp5
              have hgt : 1 < fSum (2 ^ a) * fSum (p ^ k) := by
                have h1 := fSum_two_pow_gt_one ha_pos
                have h2 : 1 < fSum (p ^ k) := by
                  have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
                  exact fSum_gt_one this
                nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
                  fSum_pos (pow_ne_zero k hp.ne_zero)]
              exact den_ne_one_of_mem_Ioo hgt hlt hden
        · -- a ≡ 1 [MOD 4]
          have ha1 : a ≡ 1 [MOD 4] := by
            have : a % 4 = 1 ∨ a % 4 = 3 := by
              have : a % 2 = 1 := Nat.odd_iff.mp ha_odd
              have : a % 4 < 4 := Nat.mod_lt _ (by decide)
              omega
            cases this with
            | inl h => simpa [Nat.ModEq] using h
            | inr h =>
              have : a ≡ 3 [MOD 4] := by simpa [Nat.ModEq] using h
              exact (hmod this).elim
          have hv2a_ge : 2 ≤ padicValRat 2 (fSum (2 ^ a)) :=
            v2_fSum_two_pow_mod4_one ha1
          by_cases hω3 : 3 ≤ m.primeFactors.card
          · have hv2m : padicValRat 2 (fSum m) ≤ -3 := by
              have := v2_fSum_odd_le_neg_omega hm_odd hmgt
              have : (3 : ℤ) ≤ m.primeFactors.card := by exact_mod_cast hω3
              linarith
            by_cases ha8_1 : a ≡ 1 [MOD 8]
            · have hv2a : padicValRat 2 (fSum (2 ^ a)) = 2 :=
                v2_fSum_two_pow_mod8_one ha8_1
              have hv2 : padicValRat 2 (fSum (2 ^ a) * fSum m) < 0 := by
                rw [padicValRat.mul
                  (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
                  (fSum_ne_zero hm0)]
                linarith
              exact den_ne_one_of_neg_padic hv2 hden
            · have ha5_8 : a ≡ 5 [MOD 8] := by
                have : a % 8 = 1 ∨ a % 8 = 5 := by
                  have : a % 4 = 1 := by simpa [Nat.ModEq] using ha1
                  have : a % 8 < 8 := Nat.mod_lt _ (by decide)
                  omega
                cases this with
                | inl h =>
                  have : a ≡ 1 [MOD 8] := by simpa [Nat.ModEq] using h
                  exact (ha8_1 this).elim
                | inr h => simpa [Nat.ModEq] using h
              exact fSum_mod8_five_omega_ge_three_not_int
                ha_pos ha5_8 hm_odd hmgt hω3 hden
          · have hωle : m.primeFactors.card ≤ 2 := by omega
            have hne : m.primeFactors.Nonempty := by
              rw [Nat.nonempty_primeFactors]
              omega
            have hωge : 1 ≤ m.primeFactors.card := Finset.card_pos.mpr hne
            have hω12 : m.primeFactors.card = 1 ∨ m.primeFactors.card = 2 := by omega
            cases hω12 with
            | inl hω1 =>
              have hm_pow := eq_minFac_pow_of_card_primeFactors_eq_one hmgt hω1
              set p := m.minFac
              set k := m.factorization p
              have hp : p.Prime := minFac_prime (by omega)
              have hk : 1 ≤ k := by
                have : p ∈ m.primeFactors :=
                  mem_primeFactors.mpr ⟨hp, minFac_dvd m, hm0⟩
                exact factorization_pos_of_mem_primeFactors this
              have hpo : Odd p := hp.odd_of_ne_two (by
                intro h2
                apply h2nm
                have : p ∈ m.primeFactors :=
                  mem_primeFactors.mpr ⟨hp, minFac_dvd m, hm0⟩
                rwa [h2] at this)
              rw [hm_pow] at hden
              by_cases hp3eq : p = 3
              · rw [hp3eq] at hden
                exact fSum_two_pow_mul_three_pow_not_int a k ha_pos hk hden
              · have hp2 : p ≠ 2 := by
                  intro h2; apply h2nm
                  have : p ∈ m.primeFactors :=
                    mem_primeFactors.mpr ⟨hp, minFac_dvd m, hm0⟩
                  rwa [h2] at this
                have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3eq
                have hlt : fSum (2 ^ a) * fSum (p ^ k) < 2 :=
                  fSum_two_pow_mul_prime_lt_two hp hp5
                have hgt : 1 < fSum (2 ^ a) * fSum (p ^ k) := by
                  have h1 := fSum_two_pow_gt_one ha_pos
                  have h2 : 1 < fSum (p ^ k) :=
                    fSum_gt_one (Nat.one_lt_pow (by omega) hp.one_lt)
                  nlinarith [fSum_pos (pow_ne_zero a two_ne_zero),
                    fSum_pos (pow_ne_zero k hp.ne_zero)]
                exact den_ne_one_of_mem_Ioo hgt hlt hden
            | inr hω2 =>
              obtain ⟨p, q, hpq, hp, hq, hs, hm_eq⟩ :=
                eq_mul_prime_pows_of_card_eq_two hm0 hω2
              set kp := m.factorization p
              set kq := m.factorization q
              have hpkp : 1 ≤ kp := by
                have : p ∈ m.primeFactors := by simp [hs]
                exact factorization_pos_of_mem_primeFactors this
              have hqkp : 1 ≤ kq := by
                have : q ∈ m.primeFactors := by simp [hs]
                exact factorization_pos_of_mem_primeFactors this
              have hpo : Odd p := hp.odd_of_ne_two (by
                intro h2; apply h2nm; simpa [hs, h2] using mem_insert_self (2 : ℕ) _)
              have hqo : Odd q := hq.odd_of_ne_two (by
                intro h2; apply h2nm
                have : q ∈ m.primeFactors := by simp [hs]
                rwa [h2] at this)
              have hcop : Nat.Coprime (p ^ kp) (q ^ kq) :=
                Nat.coprime_pow_primes kp kq hp hq hpq
              have hfm : fSum m = fSum (p ^ kp) * fSum (q ^ kq) := by
                rw [hm_eq]; exact fSum_mul hcop
              rw [hfm] at hden
              have hpmod := odd_mod4 hpo
              have hqmod := odd_mod4 hqo
              by_cases hbig : 3 ≤ kp ∨ 3 ≤ kq ∨ p ≡ 3 [MOD 4] ∨ q ≡ 3 [MOD 4]
              · have hv2m : padicValRat 2 (fSum (p ^ kp) * fSum (q ^ kq)) ≤ -3 := by
                  rw [padicValRat.mul
                    (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                    (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
                  have hv2p : padicValRat 2 (fSum (p ^ kp)) ≤ -1 :=
                    Int.le_sub_one_of_lt
                      (padicValRat_two_fSum_odd_prime_pow_neg hp hpo hpkp)
                  have hv2q : padicValRat 2 (fSum (q ^ kq)) ≤ -1 :=
                    Int.le_sub_one_of_lt
                      (padicValRat_two_fSum_odd_prime_pow_neg hq hqo hqkp)
                  rcases hbig with hkp3 | hkq3 | hp3 | hq3
                  · have : padicValRat 2 (fSum (p ^ kp)) ≤ -2 :=
                      v2_fSum_odd_prime_pow_exp_ge_three hp hpo hkp3
                    linarith
                  · have : padicValRat 2 (fSum (q ^ kq)) ≤ -2 :=
                      v2_fSum_odd_prime_pow_exp_ge_three hq hqo hkq3
                    linarith
                  · have : padicValRat 2 (fSum (p ^ kp)) ≤ -2 :=
                      v2_fSum_odd_prime_pow_mod4_three hp hpo hp3 hpkp
                    linarith
                  · have : padicValRat 2 (fSum (q ^ kq)) ≤ -2 :=
                      v2_fSum_odd_prime_pow_mod4_three hq hqo hq3 hqkp
                    linarith
                by_cases ha8_1 : a ≡ 1 [MOD 8]
                · have hv2a : padicValRat 2 (fSum (2 ^ a)) = 2 :=
                    v2_fSum_two_pow_mod8_one ha8_1
                  have hv2 : padicValRat 2
                      (fSum (2 ^ a) * (fSum (p ^ kp) * fSum (q ^ kq))) < 0 := by
                    rw [padicValRat.mul
                      (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
                      (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))
                        (fSum_ne_zero (pow_ne_zero _ hq.ne_zero)))]
                    linarith
                  exact den_ne_one_of_neg_padic hv2 hden
                · have ha5_8 : a ≡ 5 [MOD 8] := by
                    have : a % 8 = 1 ∨ a % 8 = 5 := by
                      have : a % 4 = 1 := by simpa [Nat.ModEq] using ha1
                      have : a % 8 < 8 := Nat.mod_lt _ (by decide)
                      omega
                    cases this with
                    | inl h =>
                      have : a ≡ 1 [MOD 8] := by simpa [Nat.ModEq] using h
                      exact (ha8_1 this).elim
                    | inr h => simpa [Nat.ModEq] using h
                  exact fSum_mod8_five_omega_two_big_not_int
                    ha_pos ha5_8 hp hq hpq hpo hqo hpkp hqkp hbig hden
              · push_neg at hbig
                obtain ⟨hkp2, hkq2, hp1m, hq1m⟩ := hbig
                have hkp12 : kp = 1 ∨ kp = 2 := by omega
                have hkq12 : kq = 1 ∨ kq = 2 := by omega
                have hp1' : p ≡ 1 [MOD 4] := by
                  cases hpmod with
                  | inl h => exact h
                  | inr h => exact (hp1m h).elim
                have hq1' : q ≡ 1 [MOD 4] := by
                  cases hqmod with
                  | inl h => exact h
                  | inr h => exact (hq1m h).elim
                have hgt := fSum_two_mul_two_prime_pows_gt_one ha_pos hp hq hpkp hqkp
                have hp5 : 5 ≤ p := five_le_of_mod4_one hp hp1'
                have hq5 : 5 ≤ q := five_le_of_mod4_one hq hq1'
                have hlt3 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) < 3 :=
                  fSum_two_mul_two_prime_pows_lt_three hp hq hp5 hq5
                rw [← mul_assoc] at hden
                have ha8 : a % 8 = 1 ∨ a % 8 = 5 := by
                  have : a % 4 = 1 := by simpa [Nat.ModEq] using ha1
                  have : a % 8 < 8 := Nat.mod_lt _ (by decide)
                  omega
                cases ha8 with
                | inl ha1_8 =>
                  have ha1m : a ≡ 1 [MOD 8] := by simpa [Nat.ModEq] using ha1_8
                  have hv2a' : padicValRat 2 (fSum (2 ^ a)) = 2 :=
                    v2_fSum_two_pow_mod8_one ha1m
                  have hv2p : padicValRat 2 (fSum (p ^ kp)) = -1 :=
                    v2_fSum_odd_prime_pow_mod4_one_small hp hpo hp1' hkp12
                  have hv2q : padicValRat 2 (fSum (q ^ kq)) = -1 :=
                    v2_fSum_odd_prime_pow_mod4_one_small hq hqo hq1' hkq12
                  have hv2 : padicValRat 2
                      (fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq)) = 0 := by
                    rw [padicValRat.mul
                      (mul_ne_zero (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
                        (fSum_ne_zero (pow_ne_zero _ hp.ne_zero)))
                      (fSum_ne_zero (pow_ne_zero _ hq.ne_zero))]
                    rw [padicValRat.mul
                      (fSum_ne_zero (pow_ne_zero _ two_ne_zero))
                      (fSum_ne_zero (pow_ne_zero _ hp.ne_zero))]
                    omega
                  have hne2 : fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq) ≠ 2 := by
                    intro heq
                    haveI := two_fact
                    have : padicValRat 2 (2 : ℚ) = 1 := padicValRat_two_two
                    have : padicValRat 2
                        (fSum (2 ^ a) * fSum (p ^ kp) * fSum (q ^ kq)) = 1 := by
                      rw [heq]; exact this
                    omega
                  exact den_ne_one_of_mem_Ioo_ne_two hgt hlt3 hne2 hden
                | inr ha5_8 =>
                  have ha5m : a ≡ 5 [MOD 8] := by simpa [Nat.ModEq] using ha5_8
                  have hne2 := fSum_two_pow_mul_two_mod4_one_ne_two
                    hp hq hpq hp1' hq1' hkp12 hkq12 ha5m
                  exact den_ne_one_of_mem_Ioo_ne_two hgt hlt3 hne2 hden
