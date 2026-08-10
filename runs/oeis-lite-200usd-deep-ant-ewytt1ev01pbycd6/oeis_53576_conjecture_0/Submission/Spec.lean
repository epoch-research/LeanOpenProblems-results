import FormalConjectures.Util.ProblemImports

open Nat Set

/-- Classification: an odd number whose totient is a power of two is a product of
distinct Fermat primes. -/
lemma classify : ∀ (q : ℕ), Odd q → ∀ (s : ℕ), Nat.totient q = 2 ^ s →
    ∃ S : Finset ℕ, q = ∏ j ∈ S, Nat.fermatNumber j ∧
      (∀ j ∈ S, (Nat.fermatNumber j).Prime) ∧ s = ∑ j ∈ S, 2 ^ j := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hodd s hs
    -- q is positive
    have hq0 : q ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hodd
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hq0) with hq1 | hq1
    · -- q = 1
      refine ⟨∅, by simp [← hq1], by simp, ?_⟩
      simp only [← hq1, Nat.totient_one] at hs
      have : s = 0 := by
        by_contra h
        have : 2 ^ 1 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr h)
        omega
      simp [this]
    · -- q > 1
      set p := q.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ q := Nat.minFac_dvd q
      have hp2 : p ≠ 2 := by
        rintro h
        rw [h] at hpdvd
        rw [Nat.odd_iff] at hodd
        omega
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      -- coprimality
      have hcop : Nat.Coprime p (ordCompl[p] q) := Nat.coprime_ordCompl hp hq0
      set r := ordCompl[p] q with hr_def
      set e := q.factorization p with he_def
      have hsplit : p ^ e * r = q := Nat.ordProj_mul_ordCompl_eq_self q p
      have hepos : 0 < e := hp.factorization_pos_of_dvd hq0 hpdvd
      have hcop2 : Nat.Coprime (p ^ e) r := hcop.pow_left e
      have htot : Nat.totient q = Nat.totient (p ^ e) * Nat.totient r := by
        rw [← hsplit, Nat.totient_mul hcop2]
      rw [hs, Nat.totient_prime_pow hp hepos] at htot
      -- htot : 2 ^ s = p ^ (e - 1) * (p - 1) * totient r
      -- p does not divide 2 ^ s
      have hpndvd : ¬ p ∣ 2 ^ s := by
        intro hdvd
        have := hp.dvd_of_dvd_pow hdvd
        have : p ∣ 2 := this
        have := Nat.le_of_dvd (by norm_num) this
        omega
      -- show e = 1
      have he1 : e = 1 := by
        by_contra hne
        have he2 : 2 ≤ e := by omega
        have : p ∣ p ^ (e - 1) := dvd_pow_self p (by omega)
        have hpd : p ∣ 2 ^ s := by
          rw [htot]
          exact Dvd.dvd.mul_right (this.mul_right _) _
        exact hpndvd hpd
      rw [he1] at htot
      simp only [Nat.sub_self, pow_zero, one_mul] at htot
      -- htot : 2 ^ s = (p - 1) * totient r
      -- p - 1 is a power of two
      have hpm1_dvd : (p - 1) ∣ 2 ^ s := ⟨_, htot⟩
      obtain ⟨t, htle, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hpm1_dvd
      -- ht : p - 1 = 2 ^ t
      have hpeq : p = 2 ^ t + 1 := by omega
      have ht0 : t ≠ 0 := by
        rintro rfl
        simp at ht
        omega
      obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (a := 2) (n := t) (by norm_num) ht0
        (by rw [← hpeq]; exact hp)
      -- hm : t = 2 ^ m,  p = fermatNumber m
      have hpF : p = Nat.fermatNumber m := by
        rw [hpeq, hm]; rfl
      -- totient r = 2 ^ (s - t)
      have htotr : Nat.totient r = 2 ^ (s - t) := by
        have hkey : 2 ^ t * Nat.totient r = 2 ^ t * 2 ^ (s - t) := by
          rw [← pow_add, Nat.add_sub_cancel' htle, ← ht, ← htot]
        exact Nat.eq_of_mul_eq_mul_left (by positivity) hkey
      -- r is odd, positive, < q
      have hr_dvd : r ∣ q := Nat.ordCompl_dvd q p
      have hr_odd : Odd r := hodd.of_dvd_nat hr_dvd
      have hrpos : 0 < r := by rcases hr_odd with ⟨k, hk⟩; omega
      have hr0 : r ≠ 0 := by omega
      have hrlt : r < q := by
        rw [← hsplit, he1, pow_one]
        have h1 : 1 * r < p * r := (Nat.mul_lt_mul_right hrpos).mpr (by omega)
        simpa using h1
      obtain ⟨S', hS'prod, hS'prime, hS'sum⟩ := ih r hrlt hr_odd (s - t) htotr
      -- m ∉ S'
      have hmnotin : m ∉ S' := by
        intro hmem
        have : Nat.fermatNumber m ∣ r := by
          rw [hS'prod]; exact Finset.dvd_prod_of_mem _ hmem
        rw [← hpF] at this
        exact Nat.not_dvd_ordCompl hp hq0 this
      refine ⟨insert m S', ?_, ?_, ?_⟩
      · rw [Finset.prod_insert hmnotin, ← hpF, ← hS'prod, ← hsplit, he1, pow_one]
      · intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · rw [← hpF]; exact hp
        · exact hS'prime j hj
      · rw [Finset.sum_insert hmnotin, ← hS'sum]
        -- s = 2 ^ m + (s - t) and t = 2 ^ m
        omega

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

/-- Main lemma, general in `K`. `N = 2^K`, and `fermatNumber K = 2^N + 1`. -/
lemma main_general (K : ℕ) :
    a (2 ^ K) = if (Nat.fermatNumber K).Prime then Nat.fermatNumber K else 2 ^ (2 ^ K + 1) := by
  set N := 2 ^ K with hN
  set F := Nat.fermatNumber K with hF
  have hNpos : 0 < N := by rw [hN]; positivity
  have h2N : 2 ≤ 2 ^ N := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hNpos
  have hFeq : F = 2 ^ N + 1 := by rw [hF, hN]; rfl
  unfold a
  set S := { m : ℕ | m > 0 ∧ 2 ^ N ∣ Nat.totient m } with hS
  -- membership: 2^(N+1) ∈ S
  have mem_pow : 2 ^ (N + 1) ∈ S := by
    refine ⟨by positivity, ?_⟩
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hne : S.Nonempty := ⟨2 ^ (N + 1), mem_pow⟩
  -- Claim A: every element is ≥ 2^N + 1
  have claimA : ∀ m ∈ S, 2 ^ N + 1 ≤ m := by
    rintro m ⟨hm0, hdvd⟩
    have hphipos : 0 < Nat.totient m := Nat.totient_pos.mpr hm0
    have hphi_ge : 2 ^ N ≤ Nat.totient m := Nat.le_of_dvd hphipos hdvd
    have hm1 : 2 ≤ m := by
      by_contra h
      push_neg at h
      interval_cases m
      rw [Nat.totient_one] at hphi_ge; omega
    have hphi_lt : Nat.totient m < m := Nat.totient_lt m hm1
    omega
  -- Now split on primality of F
  by_cases hFp : F.Prime
  · -- prime case
    rw [if_pos hFp]
    apply le_antisymm
    · apply Nat.sInf_le
      refine ⟨by rw [hFeq]; positivity, ?_⟩
      rw [Nat.totient_prime hFp, hFeq]
      simp
    · have hmem := Nat.sInf_mem hne
      have := claimA (sInf S) hmem
      rw [hFeq]
      omega
  · -- composite case
    rw [if_neg hFp]
    -- Claim B
    have claimB : ∀ m ∈ S, 2 ^ (N + 1) ≤ m := by
      rintro m ⟨hm0, hdvd⟩
      by_contra hlt
      push_neg at hlt
      have hm0' : m ≠ 0 := by omega
      have hgeA := claimA m ⟨hm0, hdvd⟩
      have hphipos : 0 < Nat.totient m := Nat.totient_pos.mpr hm0
      have hphi_ge : 2 ^ N ≤ Nat.totient m := Nat.le_of_dvd hphipos hdvd
      have hphi_lt : Nat.totient m < m := Nat.totient_lt m (by omega)
      have hphi_ltN : Nat.totient m < 2 ^ (N + 1) := by omega
      -- φ m = 2^N
      have h2Npos : 0 < 2 ^ N := by positivity
      have hphi_eq : Nat.totient m = 2 ^ N := by
        obtain ⟨c, hc⟩ := hdvd
        rw [hc] at hphi_ge hphi_ltN
        rw [pow_succ] at hphi_ltN
        have hge : 2 ^ N * 1 ≤ 2 ^ N * c := by rw [mul_one]; exact hphi_ge
        have hcge : 1 ≤ c := Nat.le_of_mul_le_mul_left hge h2Npos
        have hclt : c < 2 := Nat.lt_of_mul_lt_mul_left hphi_ltN
        rw [hc, show c = 1 by omega, mul_one]
      -- decompose m = 2^a2 * r
      have hsplit2 : 2 ^ (m.factorization 2) * ordCompl[2] m = m :=
        Nat.ordProj_mul_ordCompl_eq_self m 2
      set a2 := m.factorization 2 with ha2
      set r := ordCompl[2] m with hr2
      have hcopr : Nat.Coprime 2 r := Nat.coprime_ordCompl Nat.prime_two hm0'
      have hrodd : Odd r := by
        rw [Nat.odd_iff]
        have := Nat.not_dvd_ordCompl Nat.prime_two hm0'
        omega
      have hcop2 : Nat.Coprime (2 ^ a2) r := hcopr.pow_left a2
      have htotm : Nat.totient m = Nat.totient (2 ^ a2) * Nat.totient r := by
        rw [← hsplit2, Nat.totient_mul hcop2]
      rcases Nat.eq_zero_or_pos a2 with ha0 | hapos
      · -- a2 = 0 : m = r odd
        rw [ha0, pow_zero, Nat.totient_one, one_mul] at htotm
        have hphir : Nat.totient r = 2 ^ N := by rw [← htotm, hphi_eq]
        obtain ⟨T, hTprod, hTprime, hTsum⟩ := classify r hrodd N hphir
        have hsum2K : (∑ j ∈ T, 2 ^ j) = ∑ j ∈ ({K} : Finset ℕ), 2 ^ j := by
          rw [Finset.sum_singleton, ← hTsum, hN]
        have hTeq : T = ({K} : Finset ℕ) := Finset.geomSum_injective (le_refl 2) hsum2K
        have hKmem : K ∈ T := by rw [hTeq]; exact Finset.mem_singleton_self K
        have hFprime : (Nat.fermatNumber K).Prime := hTprime K hKmem
        rw [← hF] at hFprime
        exact hFp hFprime
      · -- a2 ≥ 1
        rw [Nat.totient_prime_pow Nat.prime_two hapos] at htotm
        rw [show (2 : ℕ) - 1 = 1 from rfl, mul_one] at htotm
        have hkey : 2 ^ (a2 - 1) * Nat.totient r = 2 ^ N := by rw [← htotm, hphi_eq]
        rcases Nat.lt_or_ge r 2 with hr1 | hr2
        · -- r = 1
          have hr_eq1 : r = 1 := by rcases hrodd with ⟨k, hk⟩; omega
          rw [hr_eq1, Nat.totient_one, mul_one] at hkey
          have haN : a2 - 1 = N := Nat.pow_right_injective (le_refl 2) hkey
          have hmval : m = 2 ^ a2 := by rw [← hsplit2, hr_eq1, mul_one]
          rw [hmval, show a2 = N + 1 by omega] at hlt
          omega
        · -- r ≥ 2
          have hphir_lt : Nat.totient r < r := Nat.totient_lt r hr2
          have hphir_dvd : Nat.totient r ∣ 2 ^ N := ⟨2 ^ (a2 - 1), by rw [← hkey]; ring⟩
          obtain ⟨s', hs'le, hs'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hphir_dvd
          have hsum : (a2 - 1) + s' = N := by
            have : 2 ^ ((a2 - 1) + s') = 2 ^ N := by rw [pow_add, ← hs', hkey]
            exact Nat.pow_right_injective (le_refl 2) this
          have hr_ge : 2 ^ s' + 1 ≤ r := by rw [← hs']; omega
          have hge_m : 2 ^ a2 * (2 ^ s' + 1) ≤ m := by
            rw [← hsplit2]; exact Nat.mul_le_mul_left _ hr_ge
          have hexp : 2 ^ a2 * (2 ^ s' + 1) = 2 ^ (N + 1) + 2 ^ a2 := by
            have hae : a2 + s' = N + 1 := by omega
            rw [Nat.mul_add, mul_one, ← pow_add, hae]
          rw [hexp] at hge_m
          have h2a2 : 0 < 2 ^ a2 := by positivity
          omega
    -- conclude composite case
    apply le_antisymm
    · exact Nat.sInf_le mem_pow
    · exact claimB (sInf S) (Nat.sInf_mem hne)

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  intro N_idx N F33
  exact main_general 33
