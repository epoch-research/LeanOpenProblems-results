import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

/-! ### Auxiliary lemmas -/

private instance fact_prime_two : Fact (2 : ℕ).Prime := ⟨prime_two⟩

private lemma two_pow_dvd_totient_iff {n m : ℕ} (hm : m ≠ 0) :
    2 ^ n ∣ m.totient ↔ n ≤ padicValNat 2 m.totient :=
  padicValNat_dvd_iff_le (totient_pos.mpr (pos_of_ne_zero hm)).ne'

private lemma two_pow_dvd_totient_two_pow (n : ℕ) :
    2 ^ n ∣ totient (2 ^ (n + 1)) := by
  rw [totient_prime_pow prime_two (succ_pos n)]
  simp

private lemma two_pow_dvd_totient_fermat {k : ℕ} (h : (fermatNumber k).Prime) :
    2 ^ (2 ^ k) ∣ totient (fermatNumber k) := by
  rw [totient_prime h, fermatNumber, add_tsub_cancel_right]

private lemma fermatNumber_lt_two_pow_succ (k : ℕ) :
    fermatNumber k < 2 ^ (2 ^ k + 1) := by
  simp only [fermatNumber]
  have hlt : 1 < 2 ^ (2 ^ k) := Nat.one_lt_two_pow (pow_ne_zero k two_ne_zero)
  calc
    2 ^ (2 ^ k) + 1 < 2 ^ (2 ^ k) + 2 ^ (2 ^ k) := Nat.add_lt_add_left hlt _
    _ = 2 * 2 ^ (2 ^ k) := by ring
    _ = 2 ^ (2 ^ k + 1) := by rw [pow_succ, mul_comm]

private lemma padicValNat_two_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat 2 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat 2 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : ∏ j ∈ s, f j ≠ 0 := by
      intro h0
      rcases Finset.prod_eq_zero_iff.mp h0 with ⟨j, hj, hj0⟩
      exact hfs j hj hj0
    rw [Finset.prod_insert hi, Finset.sum_insert hi, padicValNat.mul hfi hprod, ih hfs]

private lemma one_le_padicValNat_two_pred {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    1 ≤ padicValNat 2 (p - 1) := by
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  exact one_le_padicValNat_of_dvd hp1 (even_iff_two_dvd.mp (hp.even_sub_one h2))

private lemma padicValNat_two_of_odd_mul (k q : ℕ) (hq : Odd q) :
    padicValNat 2 (2 ^ k * q) = k := by
  have hq0 : q ≠ 0 := (Odd.pos hq).ne'
  have h2q : ¬ 2 ∣ q := hq.not_two_dvd_nat
  rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hq0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd h2q, add_zero]

private lemma padicValNat_two_totient {m : ℕ} (hm : m ≠ 0) :
    padicValNat 2 m.totient =
      m.factorization 2 - 1 + ∑ p ∈ m.primeFactors, padicValNat 2 (p - 1) := by
  have hterm_ne : ∀ p ∈ m.primeFactors, p ^ (m.factorization p - 1) * (p - 1) ≠ 0 := by
    intro p hp
    have hpp : p.Prime := (mem_primeFactors.mp hp).1
    exact mul_ne_zero (pow_ne_zero _ hpp.ne_zero) (Nat.sub_ne_zero_of_lt hpp.one_lt)
  rw [totient_eq_prod_factorization hm, Finsupp.prod, support_factorization,
    padicValNat_two_prod _ _ hterm_ne]
  have hsplit :
      (∑ p ∈ m.primeFactors, padicValNat 2 (p ^ (m.factorization p - 1) * (p - 1))) =
        ∑ p ∈ m.primeFactors,
          ((m.factorization p - 1) * padicValNat 2 p + padicValNat 2 (p - 1)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp : p.Prime := (mem_primeFactors.mp hp).1
    have hpow : p ^ (m.factorization p - 1) ≠ 0 := pow_ne_zero _ hpp.ne_zero
    have hpred : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hpp.one_lt
    rw [padicValNat.mul hpow hpred, padicValNat.pow _ hpp.ne_zero]
  rw [hsplit, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (s := m.primeFactors) (p := fun p => p = 2)]
  have h2filter :
      ∑ p ∈ m.primeFactors.filter (fun p => p = 2),
          (m.factorization p - 1) * padicValNat 2 p =
        m.factorization 2 - 1 := by
    by_cases h2 : 2 ∈ m.primeFactors
    · rw [Finset.filter_eq' (s := m.primeFactors) 2, if_pos h2, Finset.sum_singleton,
        factorization_def m prime_two, padicValNat_self, mul_one]
    · rw [Finset.filter_eq' (s := m.primeFactors) 2, if_neg h2, Finset.sum_empty]
      have : m.factorization 2 = 0 := by
        rw [factorization_def m prime_two]
        exact padicValNat.eq_zero_of_not_dvd fun hdvd =>
          h2 (mem_primeFactors.mpr ⟨prime_two, hdvd, hm⟩)
      simp [this]
  have hodd :
      ∑ p ∈ m.primeFactors.filter (fun p => ¬p = 2),
          (m.factorization p - 1) * padicValNat 2 p = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp2 : p ≠ 2 := (Finset.mem_filter.mp hp).2
    have hpp : p.Prime := (mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
    have : padicValNat 2 p = 0 :=
      padicValNat.eq_zero_of_not_dvd fun hdvd =>
        hp2 ((prime_dvd_prime_iff_eq prime_two hpp).mp hdvd).symm
    simp [this]
  rw [h2filter, hodd, add_zero]

private lemma odd_prime_ge_two_pow_val_add_one {p : ℕ} (hp : p.Prime) (_h2 : p ≠ 2) :
    2 ^ padicValNat 2 (p - 1) + 1 ≤ p := by
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  obtain ⟨k, q, hq, hqeq⟩ := exists_eq_two_pow_mul_odd hp1
  have hk : padicValNat 2 (p - 1) = k := by
    rw [hqeq]; exact padicValNat_two_of_odd_mul k q hq
  have hq1 : 1 ≤ q := Nat.succ_le_of_lt (Odd.pos hq)
  have hp_eq : p = 2 ^ k * q + 1 := by
    have : 1 ≤ p := hp.one_lt.le
    omega
  rw [hk, hp_eq]
  have : 2 ^ k * 1 ≤ 2 ^ k * q := Nat.mul_le_mul_left _ hq1
  omega

private lemma odd_prime_not_fermat_ge {p : ℕ} (hp : p.Prime) (_h2 : p ≠ 2)
    (hne : p ≠ 2 ^ padicValNat 2 (p - 1) + 1) :
    3 * 2 ^ padicValNat 2 (p - 1) + 1 ≤ p := by
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  obtain ⟨k, q, hq, hqeq⟩ := exists_eq_two_pow_mul_odd hp1
  have hk : padicValNat 2 (p - 1) = k := by
    rw [hqeq]; exact padicValNat_two_of_odd_mul k q hq
  have hp_eq : p = 2 ^ k * q + 1 := by
    have : 1 ≤ p := hp.one_lt.le
    omega
  have hq3 : 3 ≤ q := by
    have hq1 : 1 ≤ q := Nat.succ_le_of_lt (Odd.pos hq)
    have hne' : q ≠ 1 := by
      intro hq1'
      apply hne
      rw [hk, hp_eq, hq1', mul_one]
    have hodd : q % 2 = 1 := (odd_iff.mp hq)
    omega
  rw [hk, hp_eq]
  have : 2 ^ k * 3 ≤ 2 ^ k * q := Nat.mul_le_mul_left _ hq3
  omega

private lemma eq_fermatNumber_of_two_pow_add_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (heq : p = 2 ^ padicValNat 2 (p - 1) + 1) :
    ∃ k, p = fermatNumber k ∧ padicValNat 2 (p - 1) = 2 ^ k := by
  have hc0 : padicValNat 2 (p - 1) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (one_le_padicValNat_two_pred hp h2)
  obtain ⟨k, hk⟩ := pow_of_pow_add_prime (a := 2) one_lt_two hc0 (by rwa [← heq])
  refine ⟨k, ?_, hk⟩
  rw [heq, hk, fermatNumber]

private lemma prod_two_pow_add_one_ge (s : Finset ℕ) (f : ℕ → ℕ) (hs : s.Nonempty) :
    2 ^ (∑ i ∈ s, f i) + 1 ≤ ∏ i ∈ s, (2 ^ f i + 1) := by
  classical
  revert hs
  induction s using Finset.induction with
  | empty =>
    intro hs
    exact (Finset.not_nonempty_empty hs).elim
  | insert a s ha ih =>
    intro hs
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp
    · have ih' := ih hs'
      have hmul :
          (2 ^ f a + 1) * (2 ^ ∑ i ∈ s, f i + 1) ≤
            (2 ^ f a + 1) * ∏ i ∈ s, (2 ^ f i + 1) :=
        Nat.mul_le_mul_left _ ih'
      refine le_trans ?_ hmul
      rw [pow_add]
      have h1 : 0 < 2 ^ f a := pow_pos two_pos _
      have h2 : 0 < 2 ^ ∑ i ∈ s, f i := pow_pos two_pos _
      calc
        2 ^ f a * 2 ^ ∑ i ∈ s, f i + 1
            ≤ 2 ^ f a * 2 ^ ∑ i ∈ s, f i + 2 ^ f a + 2 ^ ∑ i ∈ s, f i + 1 := by omega
        _ = (2 ^ f a + 1) * (2 ^ ∑ i ∈ s, f i + 1) := by ring

private lemma prod_three_mul_two_pow_add_one_ge (s : Finset ℕ) (f : ℕ → ℕ) (hs : s.Nonempty) :
    3 * 2 ^ (∑ i ∈ s, f i) + 1 ≤ ∏ i ∈ s, (3 * 2 ^ f i + 1) := by
  classical
  revert hs
  induction s using Finset.induction with
  | empty =>
    intro hs
    exact (Finset.not_nonempty_empty hs).elim
  | insert a s ha ih =>
    intro hs
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp
    · have ih' := ih hs'
      have hmul :
          (3 * 2 ^ f a + 1) * (3 * 2 ^ ∑ i ∈ s, f i + 1) ≤
            (3 * 2 ^ f a + 1) * ∏ i ∈ s, (3 * 2 ^ f i + 1) :=
        Nat.mul_le_mul_left _ ih'
      refine le_trans ?_ hmul
      rw [pow_add]
      have ha0 : 0 < 2 ^ f a := pow_pos two_pos _
      have hs0 : 0 < 2 ^ ∑ i ∈ s, f i := pow_pos two_pos _
      calc
        3 * (2 ^ f a * 2 ^ ∑ i ∈ s, f i) + 1
            ≤ (3 * 2 ^ f a + 1) * (3 * 2 ^ ∑ i ∈ s, f i + 1) := by
              nlinarith
        _ = (3 * 2 ^ f a + 1) * (3 * 2 ^ ∑ i ∈ s, f i + 1) := rfl

private lemma mixed_prod_ge (sF sN : Finset ℕ) (f : ℕ → ℕ) (hN : sN.Nonempty) :
    3 * 2 ^ (∑ i ∈ sF, f i + ∑ i ∈ sN, f i) + 1 ≤
      (∏ i ∈ sF, (2 ^ f i + 1)) * (∏ i ∈ sN, (3 * 2 ^ f i + 1)) := by
  have hNge := prod_three_mul_two_pow_add_one_ge sN f hN
  rcases sF.eq_empty_or_nonempty with hF | hF
  · subst hF
    simpa using hNge
  · have hFge := prod_two_pow_add_one_ge sF f hF
    have hmul :
        (2 ^ ∑ i ∈ sF, f i + 1) * (3 * 2 ^ ∑ i ∈ sN, f i + 1) ≤
          (∏ i ∈ sF, (2 ^ f i + 1)) * (∏ i ∈ sN, (3 * 2 ^ f i + 1)) :=
      Nat.mul_le_mul hFge hNge
    refine le_trans ?_ hmul
    rw [pow_add]
    have h1 : 0 < 2 ^ ∑ i ∈ sF, f i := pow_pos two_pos _
    have h2 : 0 < 2 ^ ∑ i ∈ sN, f i := pow_pos two_pos _
    nlinarith

private lemma two_pow_mul_odd_primes_le {m : ℕ} (hm : m ≠ 0) :
    2 ^ m.factorization 2 * ∏ p ∈ m.primeFactors.erase 2, p ≤ m := by
  have hright : (∏ p ∈ m.primeFactors, p ^ m.factorization p) = m :=
    factorization_prod_pow_eq_self hm
  refine le_trans ?_ hright.le
  by_cases h2 : 2 ∈ m.primeFactors
  · have hsplit := Finset.mul_prod_erase (s := m.primeFactors)
      (f := fun p => p ^ m.factorization p) h2
    rw [← hsplit]
    refine Nat.mul_le_mul_left _ ?_
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
    have hp' : p ∈ m.primeFactors := Finset.mem_of_mem_erase hp
    have hpp : p.Prime := (mem_primeFactors.mp hp').1
    have hpos : 1 ≤ m.factorization p :=
      Prime.factorization_pos_of_dvd hpp hm (mem_primeFactors.mp hp').2.1
    exact Nat.le_self_pow (Nat.one_le_iff_ne_zero.mp hpos) p
  · rw [Finset.erase_eq_of_notMem h2]
    have hα : m.factorization 2 = 0 := by
      rw [factorization_def m prime_two]
      exact padicValNat.eq_zero_of_not_dvd fun hdvd =>
        h2 (mem_primeFactors.mpr ⟨prime_two, hdvd, hm⟩)
    rw [hα, pow_zero, one_mul]
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
    have hpp : p.Prime := (mem_primeFactors.mp hp).1
    have hpos : 1 ≤ m.factorization p :=
      Prime.factorization_pos_of_dvd hpp hm (mem_primeFactors.mp hp).2.1
    exact Nat.le_self_pow (Nat.one_le_iff_ne_zero.mp hpos) p

private lemma sum_range_two_pow (t : ℕ) :
    ∑ k ∈ Finset.range t, 2 ^ k = 2 ^ t - 1 := by
  rw [geomSum_eq (by decide : 2 ≤ 2) t]
  simp

private lemma two_pow_succ_lt_three_mul (k : ℕ) :
    2 ^ (k + 1) < 3 * 2 ^ k + 1 := by
  rw [pow_succ]
  have : 0 < 2 ^ k := pow_pos two_pos _
  omega

private lemma two_pow_lt_three_mul_add_pos (k a : ℕ) (ha : 0 < a) :
    2 ^ k < 3 * 2 ^ k + a := by
  have : 0 < 2 ^ k := pow_pos two_pos _
  omega

private lemma two_pow_succ_lt_two_mul_succ (k : ℕ) :
    2 ^ (k + 1) < 2 * (2 ^ k + 1) := by
  rw [pow_succ]
  have : 0 < 2 ^ k := pow_pos two_pos _
  omega

private lemma two_pow_succ_lt_two_pow_succ {t : ℕ} (ht : t ≠ 0) :
    2 ^ t + 1 < 2 ^ (t + 1) := by
  have hlt : 1 < 2 ^ t := Nat.one_lt_two_pow ht
  rw [pow_succ]
  omega

private lemma fermatNumber_succ_gt_bound {t : ℕ} (ht : t ≠ 0) :
    2 ^ (2 ^ t + 1) < fermatNumber (t + 1) := by
  simp only [fermatNumber]
  have hexp : 2 ^ t + 1 < 2 ^ (t + 1) := two_pow_succ_lt_two_pow_succ ht
  have : 2 ^ (2 ^ t + 1) < 2 ^ (2 ^ (t + 1)) :=
    Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hexp
  omega

private lemma three_mul_two_pow_mono {n s : ℕ} (h : n ≤ s) :
    3 * 2 ^ n + 1 ≤ 3 * 2 ^ s + 1 := by
  have : 2 ^ n ≤ 2 ^ s := Nat.pow_le_pow_right (by decide : 0 < 2) h
  omega

private lemma three_mul_two_pow_mono_add {n s a : ℕ} (h : n ≤ s) :
    3 * 2 ^ n + a ≤ 3 * 2 ^ s + a := by
  have : 2 ^ n ≤ 2 ^ s := Nat.pow_le_pow_right (by decide : 0 < 2) h
  omega

/-- The only `m < 2^{2^t+1}` with `2^{2^t} | φ(m)` is the Fermat prime `F_t` (if prime). -/
private lemma unique_small_of_two_pow_dvd_totient {t : ℕ} (ht : t ≠ 0) {m : ℕ} (hm : 0 < m)
    (hdvd : 2 ^ (2 ^ t) ∣ m.totient)
    (hlt : m < 2 ^ (2 ^ t + 1)) :
    m = fermatNumber t ∧ (fermatNumber t).Prime := by
  set n := 2 ^ t
  set α := m.factorization 2
  set P := m.primeFactors.erase 2
  set c : ℕ → ℕ := fun p => padicValNat 2 (p - 1)
  set s := ∑ p ∈ P, c p
  have hm0 : m ≠ 0 := hm.ne'
  have hval0 : n ≤ α - 1 + ∑ p ∈ m.primeFactors, c p := by
    have := (two_pow_dvd_totient_iff hm0).mp hdvd
    rwa [padicValNat_two_totient hm0] at this
  have hsum2 : ∑ p ∈ m.primeFactors, c p = s := by
    have hc2 : c 2 = 0 := by simp [c]
    exact (Finset.sum_erase (s := m.primeFactors) hc2).symm
  have hval : n ≤ α - 1 + s := by rwa [hsum2] at hval0
  have hmge : 2 ^ α * ∏ p ∈ P, p ≤ m := two_pow_mul_odd_primes_le hm0
  set PF := P.filter (fun p => p = 2 ^ c p + 1)
  set PN := P.filter (fun p => p ≠ 2 ^ c p + 1)
  have hprodP : ∏ p ∈ P, p = (∏ p ∈ PF, p) * ∏ p ∈ PN, p := by
    simp only [PF, PN, Finset.prod_filter_mul_prod_filter_not]
  have hsumP : s = ∑ p ∈ PF, c p + ∑ p ∈ PN, c p := by
    simp only [s, PF, PN, Finset.sum_filter_add_sum_filter_not]
  have hPF_ge : ∏ p ∈ PF, (2 ^ c p + 1) ≤ ∏ p ∈ PF, p := by
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
    exact ((Finset.mem_filter.mp hp).2).symm.le
  have hPN_ge : ∏ p ∈ PN, (3 * 2 ^ c p + 1) ≤ ∏ p ∈ PN, p := by
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hne : p ≠ 2 ^ c p + 1 := (Finset.mem_filter.mp hp).2
    have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hpP
    have hpp : p.Prime := (mem_primeFactors.mp (Finset.mem_of_mem_erase hpP)).1
    exact odd_prime_not_fermat_ge hpp hp2 hne
  -- Case 1: a non-Fermat odd prime factor exists
  by_cases hN : PN.Nonempty
  · have hmix := mixed_prod_ge PF PN c hN
    have hoddprod : 3 * 2 ^ s + 1 ≤ ∏ p ∈ P, p := by
      rw [hsumP, hprodP]
      exact le_trans hmix (Nat.mul_le_mul hPF_ge hPN_ge)
    have hmgt : 3 * 2 ^ (α + s) + 2 ^ α ≤ m := by
      have : 3 * 2 ^ (α + s) + 2 ^ α = 2 ^ α * (3 * 2 ^ s + 1) := by
        rw [pow_add, mul_add, mul_one]
        ring
      rw [this]
      exact le_trans (Nat.mul_le_mul_left _ hoddprod) hmge
    have hlt' : m < 2 ^ (n + 1) := hlt
    by_cases hα0 : α = 0
    · have hs_ge : n ≤ s := by simpa [hα0] using hval
      have hle : 3 * 2 ^ n + 1 ≤ m := by
        rw [hα0] at hmgt
        have : 3 * 2 ^ s + 1 ≤ m := by simpa using hmgt
        exact le_trans (three_mul_two_pow_mono hs_ge) this
      have : 2 ^ (n + 1) < 3 * 2 ^ n + 1 := two_pow_succ_lt_three_mul n
      exact (not_le_of_gt this (hle.trans (le_of_lt hlt'))).elim
    · have hαpos : 1 ≤ α := Nat.one_le_iff_ne_zero.mpr hα0
      have hαs : n + 1 ≤ α + s := by
        have : α - 1 + s = α + s - 1 := tsub_add_eq_add_tsub hαpos
        omega
      have hle : 3 * 2 ^ (n + 1) + 2 ^ α ≤ m :=
        le_trans (three_mul_two_pow_mono_add hαs) hmgt
      have : 2 ^ (n + 1) < 3 * 2 ^ (n + 1) + 2 ^ α :=
        two_pow_lt_three_mul_add_pos (n + 1) (2 ^ α) (pow_pos two_pos _)
      exact (not_le_of_gt this (hle.trans (le_of_lt hlt'))).elim
  -- Case 2: every odd prime factor is Fermat
  have hPN_empty : PN = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
  have hprodP' : ∏ p ∈ P, p = ∏ p ∈ PF, p := by
    rw [hprodP, hPN_empty, Finset.prod_empty, mul_one]
  have hsumP' : s = ∑ p ∈ PF, c p := by
    rw [hsumP, hPN_empty, Finset.sum_empty, add_zero]
  by_cases hFempty : PF = ∅
  · have hPempty : P = ∅ := by
      have : P = PF ∪ PN := by
        ext p
        simp only [PF, PN, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hp
          by_cases h : p = 2 ^ c p + 1
          · exact Or.inl ⟨hp, h⟩
          · exact Or.inr ⟨hp, h⟩
        · rintro (h | h) <;> exact h.1
      simp [this, hFempty, hPN_empty]
    have hs0 : s = 0 := by simp [s, hPempty]
    have hαn : n + 1 ≤ α := by
      have hαpos : 1 ≤ α := by
        have : n ≤ α - 1 := by simpa [hs0] using hval
        have : 0 < n := pow_pos two_pos t
        omega
      have : n ≤ α - 1 := by simpa [hs0] using hval
      omega
    have : 2 ^ (n + 1) ≤ m := by
      calc
        2 ^ (n + 1) ≤ 2 ^ α := Nat.pow_le_pow_right (by decide : 0 < 2) hαn
        _ = 2 ^ α * ∏ p ∈ P, p := by simp [hPempty]
        _ ≤ m := hmge
    omega
  have hF_ne : PF.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
  have hFermat : ∀ p ∈ PF, ∃ k, p = fermatNumber k ∧ c p = 2 ^ k := by
    intro p hp
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have heq : p = 2 ^ c p + 1 := (Finset.mem_filter.mp hp).2
    have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hpP
    have hpp : p.Prime := (mem_primeFactors.mp (Finset.mem_of_mem_erase hpP)).1
    exact eq_fermatNumber_of_two_pow_add_one hpp hp2 heq
  let kOf (p : ℕ) : ℕ := Nat.log 2 (c p)
  have hkOf : ∀ p ∈ PF, p = fermatNumber (kOf p) ∧ c p = 2 ^ kOf p := by
    intro p hp
    obtain ⟨k, hpeq, hc⟩ := hFermat p hp
    have : kOf p = k := by
      simp only [kOf, hc]
      exact Nat.log_pow one_lt_two k
    simpa [this] using And.intro hpeq hc
  have hkOf_inj : Set.InjOn kOf (PF : Set ℕ) := by
    intro p hp q hq heq
    have hp' := hkOf p hp
    have hq' := hkOf q hq
    rw [hp'.1, hq'.1, heq]
  let K : Finset ℕ := PF.image kOf
  have hsumK : ∑ p ∈ PF, c p = ∑ k ∈ K, 2 ^ k := by
    rw [Finset.sum_image hkOf_inj]
    exact Finset.sum_congr rfl fun p hp => (hkOf p hp).2
  by_cases hbig : ∃ p ∈ PF, t ≤ kOf p
  · obtain ⟨p, hpPF, hpt⟩ := hbig
    have hp_eq : p = fermatNumber (kOf p) := (hkOf p hpPF).1
    have hp_prime : p.Prime := by
      have hpP : p ∈ P := (Finset.mem_filter.mp hpPF).1
      exact (mem_primeFactors.mp (Finset.mem_of_mem_erase hpP)).1
    have hpdvd : p ∣ m :=
      dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp hpPF).1)
    have hkle : kOf p = t := by
      have hk_le : kOf p ≤ t := by
        by_contra h
        have hkt : t + 1 ≤ kOf p := by omega
        have hFp : fermatNumber (t + 1) ≤ p := by
          rw [hp_eq]
          exact fermatNumber_mono hkt
        have hFnext : 2 ^ (n + 1) < fermatNumber (t + 1) := by
          simpa [n] using fermatNumber_succ_gt_bound ht
        have : p < 2 ^ (n + 1) :=
          lt_of_le_of_lt (le_of_dvd hm hpdvd) hlt
        omega
      omega
    have hpFt : p = fermatNumber t := by rw [hp_eq, hkle]
    have hFt_val : fermatNumber t = 2 ^ n + 1 := by
      simp [fermatNumber, n]
    have hm_eq : m = p := by
      obtain ⟨u, hu⟩ := hpdvd
      have hupos : 0 < u := by
        have : 0 < p * u := by
          rwa [hu] at hm
        exact (Nat.mul_pos_iff_of_pos_left hp_prime.pos).mp this
      have hu1 : u = 1 := by
        by_contra hune
        have hu2 : 2 ≤ u := by omega
        have h2p : 2 * p ≤ m := by
          rw [hu]
          simpa [mul_comm] using Nat.mul_le_mul_left p hu2
        have : 2 * fermatNumber t ≤ m := by rwa [hpFt] at h2p
        have : 2 ^ (n + 1) < 2 * fermatNumber t := by
          rw [hFt_val, pow_succ]
          have : 0 < 2 ^ n := pow_pos two_pos _
          omega
        omega
      rw [hu, hu1, mul_one]
    subst hm_eq
    exact ⟨hpFt, hpFt ▸ hp_prime⟩
  have hk_le : ∀ p ∈ PF, kOf p ≤ t - 1 := by
    intro p hp
    have : ¬ t ≤ kOf p := fun h => hbig ⟨p, hp, h⟩
    have : kOf p < t := Nat.lt_of_not_ge this
    exact Nat.le_sub_one_of_lt this
  have hKss : K ⊆ Finset.range t := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have : kOf p ≤ t - 1 := hk_le p hp
    have : kOf p < t := by
      have htn : t = 0 ∨ 1 ≤ t := by omega
      rcases htn with rfl | htpos
      · have : kOf p ≤ 0 := by simpa using hk_le p hp
        omega
      · have : t - 1 < t := Nat.sub_lt htpos (by decide)
        omega
    exact Finset.mem_range.mpr this
  have hs_le : s ≤ n - 1 := by
    rw [hsumP', hsumK]
    have hle : ∑ k ∈ K, 2 ^ k ≤ ∑ k ∈ Finset.range t, 2 ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg hKss (fun _ _ _ => Nat.zero_le _)
    have heq : ∑ k ∈ Finset.range t, 2 ^ k = 2 ^ t - 1 := sum_range_two_pow t
    have : n = 2 ^ t := rfl
    omega
  have hα_ge : n + 1 ≤ α + s := by
    have hs_lt : s < n := by
      have hn1 : 1 ≤ n := Nat.one_le_two_pow
      have : n - 1 < n := Nat.sub_lt hn1 (by decide)
      omega
    have hαpos : 1 ≤ α := by
      by_contra h
      have : α = 0 := by omega
      have : n ≤ s := by simpa [this] using hval
      omega
    have : α - 1 + s = α + s - 1 := tsub_add_eq_add_tsub hαpos
    omega
  have hFge : 2 ^ s + 1 ≤ ∏ p ∈ PF, p := by
    have := prod_two_pow_add_one_ge PF c hF_ne
    rw [← hsumP'] at this
    exact le_trans this hPF_ge
  have hge : 2 ^ (n + 1) + 2 ^ α ≤ m := by
    calc
      2 ^ (n + 1) + 2 ^ α ≤ 2 ^ (α + s) + 2 ^ α := by
        have : 2 ^ (n + 1) ≤ 2 ^ (α + s) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) hα_ge
        omega
      _ = 2 ^ α * (2 ^ s + 1) := by
        rw [Nat.mul_add, pow_add, mul_one]
      _ ≤ 2 ^ α * ∏ p ∈ PF, p := Nat.mul_le_mul_left _ hFge
      _ = 2 ^ α * ∏ p ∈ P, p := by rw [hprodP']
      _ ≤ m := hmge
  have : 2 ^ (n + 1) < m := by
    have : 0 < 2 ^ α := pow_pos two_pos _
    omega
  omega

private lemma a_set_nonempty (n : ℕ) :
    { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }.Nonempty :=
  ⟨2 ^ (n + 1), ⟨pow_pos two_pos _, two_pow_dvd_totient_two_pow n⟩⟩

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  set F := fermatNumber 33
  let S : Set ℕ := { m : ℕ | m > 0 ∧ 2 ^ (2 ^ 33) ∣ totient m }
  have haS : a (2 ^ 33) = sInf S := rfl
  have hSne : S.Nonempty := a_set_nonempty (2 ^ 33)
  have hpow : (2 : ℕ) ^ (2 ^ 33 + 1) ∈ S :=
    ⟨pow_pos two_pos _, two_pow_dvd_totient_two_pow (2 ^ 33)⟩
  have hmin : ∀ m ∈ S, m < 2 ^ (2 ^ 33 + 1) → m = F ∧ F.Prime := by
    intro m hm hlt
    exact unique_small_of_two_pow_dvd_totient (by decide : 33 ≠ 0) hm.1 hm.2 hlt
  have hgoal : a (2 ^ 33) =
      if F.Prime then F else 2 ^ (2 ^ 33 + 1) := by
    rw [haS]
    by_cases hF : F.Prime
    · rw [if_pos hF]
      have hFmem : F ∈ S := by
        refine ⟨?_, ?_⟩
        · exact lt_of_lt_of_le (by decide : 0 < 3) (three_le_fermatNumber 33)
        · exact two_pow_dvd_totient_fermat hF
      have hFlt : F < 2 ^ (2 ^ 33 + 1) := fermatNumber_lt_two_pow_succ 33
      refine Nat.le_antisymm (Nat.sInf_le hFmem) ?_
      have hInf : sInf S ∈ S := Nat.sInf_mem hSne
      have hnotlt : ¬ sInf S < F := by
        intro hltF
        have hlt2 : sInf S < 2 ^ (2 ^ 33 + 1) := lt_trans hltF hFlt
        have huniq := hmin (sInf S) hInf hlt2
        exact (lt_irrefl _ (huniq.1 ▸ hltF))
      exact Nat.le_of_not_gt hnotlt
    · rw [if_neg hF]
      refine Nat.le_antisymm (Nat.sInf_le hpow) ?_
      have hInf : sInf S ∈ S := Nat.sInf_mem hSne
      have hnotlt : ¬ sInf S < 2 ^ (2 ^ 33 + 1) := by
        intro hlt
        exact hF (hmin (sInf S) hInf hlt).2
      exact Nat.le_of_not_gt hnotlt
  exact hgoal
