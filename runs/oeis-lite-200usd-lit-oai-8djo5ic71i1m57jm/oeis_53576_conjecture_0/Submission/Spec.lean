import FormalConjectures.Util.ProblemImports


open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
private lemma odd_dvd_two_pow_eq_one {d N : ℕ} (hd : d ∣ 2 ^ N) (hodd : Odd d) : d = 1 := by
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 hd with ⟨k, hk, rfl⟩
  cases k with
  | zero => simp
  | succ k =>
      exfalso
      exact hodd.not_two_dvd_nat (dvd_pow_self 2 (Nat.succ_ne_zero k))

private lemma two_mul_totient_le_of_even {m : ℕ} (hm : Even m) : 2 * Nat.totient m ≤ m := by
  revert hm
  refine Nat.strong_induction_on m ?_
  intro m ih hm
  rcases hm with ⟨n, rfl⟩
  rw [← two_mul n]
  by_cases hn0 : n = 0
  · subst hn0; simp [Nat.totient_zero]
  by_cases hn : Even n
  · rw [Nat.totient_two_mul_of_even hn]
    have hnlt : n < n + n := by nlinarith [Nat.pos_of_ne_zero hn0]
    exact Nat.mul_le_mul_left 2 (ih n hnlt hn)
  · have hon : Odd n := Nat.not_even_iff_odd.mp hn
    rw [Nat.totient_two_mul_of_odd hon]
    exact Nat.mul_le_mul_left 2 (Nat.totient_le n)

private lemma admissible_below_two_pow_succ_totient_eq {N m : ℕ}
    (hmpos : 0 < m) (hdvd : 2 ^ N ∣ Nat.totient m) (hlt : m < 2 ^ (N + 1)) :
    Nat.totient m = 2 ^ N := by
  have hphi_pos : 0 < Nat.totient m := Nat.totient_pos.mpr hmpos
  rcases hdvd with ⟨c, hc⟩
  have hcpos : 0 < c := by
    by_contra hc0
    have : c = 0 := Nat.eq_zero_of_not_pos hc0
    rw [this, mul_zero] at hc
    exact (Nat.ne_of_gt hphi_pos) hc
  have hltphi : Nat.totient m < 2 * 2 ^ N := by
    calc
      Nat.totient m ≤ m := Nat.totient_le m
      _ < 2 ^ (N + 1) := hlt
      _ = 2 * 2 ^ N := by rw [pow_succ']
  rw [hc] at hltphi hphi_pos
  have hc_lt_two : c < 2 := by
    have h' : 2 ^ N * c < 2 ^ N * 2 := by simpa [mul_comm] using hltphi
    exact (Nat.mul_lt_mul_left (pow_pos (by decide : 0 < 2) N)).1 h'
  interval_cases c <;> simp_all

private lemma not_even_of_totient_eq_pow_two_and_lt {N m : ℕ}
    (hphi : Nat.totient m = 2 ^ N) (hlt : m < 2 ^ (N + 1)) : Odd m := by
  rw [← Nat.not_even_iff_odd]
  intro hm
  have hle := two_mul_totient_le_of_even hm
  rw [hphi] at hle
  have : 2 ^ (N + 1) ≤ m := by
    simpa [pow_succ'] using hle
  omega

private lemma sum_range_two_pow (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ i) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hpos : 0 < 2 ^ n := pow_pos (by decide : 0 < 2) n
      rw [pow_succ']
      omega

private lemma finset_sum_two_pow_eq_pow_iff_singleton_33 {s : Finset ℕ}
    (hsum : (∑ i ∈ s, 2 ^ i) = 2 ^ 33) : s = {33} := by
  classical
  have h_nonneg : ∀ i ∈ s, 0 ≤ 2 ^ i := by intro i hi; exact Nat.zero_le _
  have hle33 : ∀ i ∈ s, i ≤ 33 := by
    intro i hi
    by_contra hnot
    have hgt : 33 < i := Nat.lt_of_not_ge hnot
    have hterm : 2 ^ i ≤ ∑ j ∈ s, 2 ^ j := Finset.single_le_sum h_nonneg hi
    rw [hsum] at hterm
    have hpowlt : 2 ^ 33 < 2 ^ i := Nat.pow_lt_pow_right (by decide : 1 < 2) hgt
    exact (not_le_of_gt hpowlt) hterm
  by_cases h33 : 33 ∈ s
  · have hsum_erase : (∑ i ∈ s.erase 33, 2 ^ i) = 0 := by
      have hdecomp := Finset.sum_erase_add s (fun i => 2 ^ i) h33
      rw [hsum] at hdecomp
      have : (∑ i ∈ s.erase 33, 2 ^ i) + 2 ^ 33 = 0 + 2 ^ 33 := by simpa using hdecomp
      exact Nat.add_right_cancel this
    have herase_empty : s.erase 33 = ∅ := by
      apply Finset.ext
      intro i
      constructor
      · intro hi
        exfalso
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg (s := s.erase 33)
          (f := fun i => 2 ^ i) (by intro j hj; exact Nat.zero_le _)).1 hsum_erase i hi
        have hpos : 0 < 2 ^ i := pow_pos (by decide : 0 < 2) i
        omega
      · intro hi
        simpa using hi
    rcases (Finset.erase_eq_empty_iff s 33).1 herase_empty with hs_empty | hs_single
    · exfalso; simpa [hs_empty] using h33
    · exact hs_single
  · have hsubset : s ⊆ Finset.range 33 := by
      intro i hi
      have hne : i ≠ 33 := by
        intro h; subst h; exact h33 hi
      exact Finset.mem_range.2 (lt_of_le_of_ne (hle33 i hi) hne)
    have hle_sum : (∑ i ∈ s, 2 ^ i) ≤ ∑ i ∈ Finset.range 33, 2 ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro i hi1 hi2; exact Nat.zero_le _)
    rw [hsum, sum_range_two_pow] at hle_sum
    have hpos : 0 < 2 ^ 33 := pow_pos (by decide : 0 < 2) 33
    omega


/-- The arithmetical core: the only number below `2^(2^33+1)` whose totient is
`2^(2^33)` is `F_33`, and this can happen only when `F_33` is prime.

This is the classical classification of solutions of `φ(n)=2^k`: such an `n`
is a product of a power of two and distinct Fermat primes.  In the present
special case the binary expansion of `2^33` forces the only odd solution below
`2^(2^33+1)` to be the single Fermat number `F_33`.
-/
private theorem totient_eq_big_power_below_classification {m : ℕ}
    (hmpos : 0 < m)
    (hphi : Nat.totient m = 2 ^ (2 ^ 33))
    (hlt : m < 2 ^ (2 ^ 33 + 1)) :
    m = Nat.fermatNumber 33 ∧ (Nat.fermatNumber 33).Prime := by
  classical
  let A : ℕ := 2 ^ (2 ^ 33)
  let P : ℕ := ∏ p ∈ m.primeFactors, p
  let Q : ℕ := ∏ p ∈ m.primeFactors, (p - 1)
  have hphiA : Nat.totient m = A := hphi
  have hoddm : Odd m :=
    not_even_of_totient_eq_pow_two_and_lt (N := 2 ^ 33) (m := m) hphi hlt
  have hformula : A = (m / P) * Q := by
    rw [← hphiA]
    dsimp [P, Q]
    rw [Nat.totient_eq_div_primeFactors_mul m]
  have hquot_dvd_A : m / P ∣ A := ⟨Q, hformula⟩
  have hPdvd : P ∣ m := by simpa [P] using Nat.prod_primeFactors_dvd m
  have hquot_dvd_m : m / P ∣ m := div_dvd_of_dvd hPdvd
  have hquot_odd : Odd (m / P) := by
    rw [← Nat.not_even_iff_odd]
    intro h2
    exact hoddm.not_two_dvd_nat (dvd_trans (even_iff_two_dvd.mp h2) hquot_dvd_m)
  have hquot_one : m / P = 1 := odd_dvd_two_pow_eq_one (N := 2 ^ 33) hquot_dvd_A hquot_odd
  have hQ : Q = A := by
    have := hformula
    rw [hquot_one, one_mul] at this
    exact this.symm
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have hm_eq_P : m = P := by
    rcases hPdvd with ⟨c, hc⟩
    have hc1 : c = 1 := by
      have := hquot_one
      rw [hc, mul_comm P c, Nat.mul_div_left c hPpos] at this
      exact this
    calc
      m = P * c := hc
      _ = P * 1 := by rw [hc1]
      _ = P := by rw [mul_one]
  have hp_form : ∀ p ∈ m.primeFactors, ∃ i : ℕ, p = Nat.fermatNumber i := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpne2 : p ≠ 2 := by
      intro hp2
      exact hoddm.not_two_dvd_nat (hp2 ▸ Nat.dvd_of_mem_primeFactors hp)
    have hpminus_dvd_Q : p - 1 ∣ Q := by
      dsimp [Q]
      exact Finset.dvd_prod_of_mem (fun x => x - 1) hp
    have hpminus_dvd_A : p - 1 ∣ A := hQ ▸ hpminus_dvd_Q
    have hpminus_dvd_pow : p - 1 ∣ 2 ^ (2 ^ 33) := hpminus_dvd_A
    rcases (Nat.dvd_prime_pow Nat.prime_two).1 hpminus_dvd_pow with ⟨r, hrle, hr⟩
    have hp_eq : p = 2 ^ r + 1 := (Nat.sub_eq_iff_eq_add hpprime.one_le).1 hr
    have hrne0 : r ≠ 0 := by
      intro hr0
      apply hpne2
      rw [hp_eq, hr0]
      rfl
    have hprime_pow : (2 ^ r + 1).Prime := by simpa [← hp_eq] using hpprime
    rcases Nat.pow_of_pow_add_prime (a := 2) (n := r) (by decide : 1 < 2) hrne0 hprime_pow with ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    rw [Nat.fermatNumber]
    exact hp_eq
  let idx : m.primeFactors → ℕ := fun p => Classical.choose (hp_form p p.property)
  have hidx_spec : ∀ p : m.primeFactors, (p : ℕ) = Nat.fermatNumber (idx p) := by
    intro p
    exact Classical.choose_spec (hp_form p p.property)
  have hidx_inj : Set.InjOn idx (Finset.univ : Finset m.primeFactors) := by
    intro x hx y hy hxy
    apply Subtype.ext
    calc
      (x : ℕ) = Nat.fermatNumber (idx x) := hidx_spec x
      _ = Nat.fermatNumber (idx y) := by rw [hxy]
      _ = (y : ℕ) := (hidx_spec y).symm
  let S : Finset ℕ := (Finset.univ : Finset m.primeFactors).image idx
  have hQpow : Q = 2 ^ (∑ x : m.primeFactors, 2 ^ idx x) := by
    calc
      Q = ∏ x : m.primeFactors, ((x : ℕ) - 1) := by
        dsimp [Q]
        exact (Finset.prod_attach m.primeFactors (fun p => p - 1)).symm
      _ = ∏ x : m.primeFactors, 2 ^ (2 ^ idx x) := by
        apply Finset.prod_congr rfl
        intro x hx
        rw [hidx_spec x, Nat.fermatNumber, Nat.add_sub_cancel]
      _ = 2 ^ (∑ x : m.primeFactors, 2 ^ idx x) := by
        exact Finset.prod_pow_eq_pow_sum Finset.univ (fun x : m.primeFactors => 2 ^ idx x) 2
  have hsum_univ : (∑ x : m.primeFactors, 2 ^ idx x) = 2 ^ 33 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    calc
      2 ^ (∑ x : m.primeFactors, 2 ^ idx x) = Q := hQpow.symm
      _ = 2 ^ (2 ^ 33) := hQ
  have hsumS : (∑ i ∈ S, 2 ^ i) = 2 ^ 33 := by
    change (∑ i ∈ (Finset.univ : Finset m.primeFactors).image idx, 2 ^ i) = 2 ^ 33
    rw [Finset.sum_image hidx_inj]
    exact hsum_univ
  have hS : S = {33} := finset_sum_two_pow_eq_pow_iff_singleton_33 hsumS
  have h_all_idx : ∀ p : m.primeFactors, idx p = 33 := by
    intro p
    have hpS : idx p ∈ S := by
      dsimp [S]
      exact Finset.mem_image_of_mem idx (Finset.mem_univ p)
    simpa [hS] using hpS
  have hprimeFactors_eq : m.primeFactors = {Nat.fermatNumber 33} := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      have hpeq := hidx_spec ⟨p, hp⟩
      rw [h_all_idx ⟨p, hp⟩] at hpeq
      simpa using hpeq
    · intro hp
      have h33S : 33 ∈ S := by simp [hS]
      rcases Finset.mem_image.1 h33S with ⟨q, hqmem, hqidx⟩
      have hqeq := hidx_spec q
      rw [hqidx] at hqeq
      have hpF : p = Nat.fermatNumber 33 := Finset.mem_singleton.mp hp
      have hpq : p = (q : ℕ) := hpF.trans hqeq.symm
      exact hpq.symm ▸ q.property
  have hm_eq_F : m = Nat.fermatNumber 33 := by
    rw [hm_eq_P]
    dsimp [P]
    rw [hprimeFactors_eq]
    simp
  have hFprime : (Nat.fermatNumber 33).Prime := by
    have : Nat.fermatNumber 33 ∈ m.primeFactors := by rw [hprimeFactors_eq]; simp
    exact Nat.prime_of_mem_primeFactors this
  exact ⟨hm_eq_F, hFprime⟩

private lemma fermatNumber_lt_two_pow_succ (n : ℕ) :
    Nat.fermatNumber n < 2 ^ (2 ^ n + 1) := by
  have hNpos : 0 < 2 ^ n := pow_pos (by decide : 0 < 2) n
  have hone : 1 < 2 ^ (2 ^ n) := one_lt_pow hNpos.ne' (by decide : 1 < 2)
  calc
    Nat.fermatNumber n = 2 ^ (2 ^ n) + 1 := rfl
    _ < 2 ^ (2 ^ n) + 2 ^ (2 ^ n) := Nat.add_lt_add_left hone _
    _ = 2 ^ (2 ^ n + 1) := by
      rw [← two_mul]
      exact (pow_succ' 2 (2 ^ n)).symm

private lemma fermatNumber_sub_one (n : ℕ) : Nat.fermatNumber n - 1 = 2 ^ (2 ^ n) := by
  rw [Nat.fermatNumber, Nat.add_sub_cancel]

private lemma lower_bound_prime_case {m : ℕ}
    (hm : m ∈ { m : ℕ | m > 0 ∧ 2 ^ (2 ^ 33) ∣ Nat.totient m })
    (hF : (Nat.fermatNumber 33).Prime) : Nat.fermatNumber 33 ≤ m := by
  by_contra hlt_not
  have hltF : m < Nat.fermatNumber 33 := Nat.lt_of_not_ge hlt_not
  rcases hm with ⟨hmpos, hdvd⟩
  have hlt : m < 2 ^ (2 ^ 33 + 1) := lt_trans hltF (fermatNumber_lt_two_pow_succ 33)
  let A : ℕ := 2 ^ (2 ^ 33)
  have htot : Nat.totient m = A :=
    admissible_below_two_pow_succ_totient_eq hmpos hdvd hlt
  have hm_ge : A ≤ m := htot ▸ Nat.totient_le m
  have hm_lt_succ : m < A + 1 := by
    change m < A + 1 at hltF
    exact hltF
  have hbase : 1 < A := by
    dsimp [A]
    exact one_lt_pow (pow_pos (by decide : 0 < 2) 33).ne' (by decide : 1 < 2)
  have hm_gt1 : 1 < m := lt_of_lt_of_le hbase hm_ge
  have hltphi : Nat.totient m < m := Nat.totient_lt m hm_gt1
  rw [htot] at hltphi
  exact (not_lt_of_ge (Nat.succ_le_of_lt hltphi)) hm_lt_succ

private lemma candidate_mem_prime :
    Nat.fermatNumber 33 ∈ { m : ℕ | m > 0 ∧ 2 ^ (2 ^ 33) ∣ Nat.totient m } ↔
    (Nat.fermatNumber 33).Prime := by
  constructor
  · intro h
    rcases h with ⟨hpos, hdvd⟩
    have hphi := admissible_below_two_pow_succ_totient_eq hpos hdvd (fermatNumber_lt_two_pow_succ 33)
    exact (Nat.totient_eq_iff_prime hpos).mp (by rw [hphi, fermatNumber_sub_one 33])
  · intro hF
    constructor
    · exact (Nat.two_lt_fermatNumber 33).trans' (by decide : 0 < 2)
    · rw [Nat.totient_prime hF, fermatNumber_sub_one 33]

private lemma pow_two_succ_totient_dvd (N : ℕ) : 2 ^ N ∣ Nat.totient (2 ^ (N + 1)) := by
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  change 2 ^ N ∣ 2 ^ N * 1
  exact dvd_mul_right _ _


private lemma candidate_mem_power :
    2 ^ (2 ^ 33 + 1) ∈ { m : ℕ | m > 0 ∧ 2 ^ (2 ^ 33) ∣ Nat.totient m } := by
  constructor
  · exact pow_pos (by decide : 0 < 2) _
  · exact pow_two_succ_totient_dvd (2 ^ 33)

theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  dsimp
  by_cases hF : (Nat.fermatNumber 33).Prime
  · rw [if_pos hF]
    unfold a
    apply le_antisymm
    · exact Nat.sInf_le ((candidate_mem_prime).2 hF)
    · exact le_csInf ⟨Nat.fermatNumber 33, (candidate_mem_prime).2 hF⟩ (fun m hm => lower_bound_prime_case hm hF)
  · rw [if_neg hF]
    unfold a
    apply le_antisymm
    · exact Nat.sInf_le candidate_mem_power
    · refine le_csInf ⟨2 ^ (2 ^ 33 + 1), candidate_mem_power⟩ ?_
      intro m hm
      by_contra hlt_not
      have hlt : m < 2 ^ (2 ^ 33 + 1) := Nat.lt_of_not_ge hlt_not
      rcases hm with ⟨hmpos, hdvd⟩
      have hphi := admissible_below_two_pow_succ_totient_eq hmpos hdvd hlt
      rcases totient_eq_big_power_below_classification hmpos hphi hlt with ⟨hmF, hFp⟩
      exact hF hFp
