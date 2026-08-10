import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

namespace Oeis53576Aux

/-- If the powers of two indexed by a finset of naturals sum to `2 ^ t`,
then the finset is `{t}`. -/
lemma finset_eq_of_sum_two_pow_eq {S : Finset ℕ} {t : ℕ}
    (h : ∑ j ∈ S, 2 ^ j = 2 ^ t) : S = {t} := by
  have ht : t ∈ S := by
    by_contra ht
    have hsub : ∀ k ∈ S, k < t := by
      intro k hk
      have hle : 2 ^ k ≤ ∑ j ∈ S, 2 ^ j :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (2 ^ i)) hk
      rw [h] at hle
      have hkt : k ≤ t := by
        by_contra hcon
        push_neg at hcon
        have : (2:ℕ) ^ t < 2 ^ k := Nat.pow_lt_pow_right one_lt_two hcon
        omega
      rcases hkt.lt_or_eq with h1 | rfl
      · exact h1
      · exact absurd hk ht
    have := Nat.geomSum_lt le_rfl hsub
    omega
  have hze : ∑ j ∈ S.erase t, 2 ^ j = 0 := by
    have h2 := Finset.add_sum_erase S (fun j => 2 ^ j) ht
    simp only at h2
    omega
  have herase : S.erase t = ∅ := by
    rcases Finset.eq_empty_or_nonempty (S.erase t) with h' | ⟨x, hx⟩
    · exact h'
    · exfalso
      have hxle : 2 ^ x ≤ ∑ j ∈ S.erase t, 2 ^ j :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (2 ^ i)) hx
      have := Nat.two_pow_pos x
      omega
  rw [← Finset.insert_erase ht, herase]
  rfl

/-- Structure theorem: if `m < 2 * 2 ^ v` where `v` is the 2-adic valuation of `φ(m)`,
then `m` is a product of distinct Fermat primes and `v` is the corresponding
sum of powers of two. -/
lemma core :
    ∀ m : ℕ, 0 < m → m < 2 * 2 ^ ((Nat.totient m).factorization 2) →
      ∃ S : Finset ℕ, (∀ j ∈ S, (Nat.fermatNumber j).Prime) ∧
        m = ∏ j ∈ S, Nat.fermatNumber j ∧
        (Nat.totient m).factorization 2 = ∑ j ∈ S, 2 ^ j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hm hlt
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- m = 1
      have : m = 1 := by omega
      subst this
      exact ⟨∅, by simp, by simp, by simp⟩
    · -- m ≥ 2
      have hm1 : m ≠ 1 := by omega
      have hm0 : m ≠ 0 := by omega
      have hp : m.minFac.Prime := Nat.minFac_prime hm1
      set p := m.minFac with hp_def
      have hpdvd : p ∣ m := Nat.minFac_dvd m
      have he : 0 < m.factorization p := hp.factorization_pos_of_dvd hm0 hpdvd
      set e := m.factorization p with he_def
      set m' := ordCompl[p] m with hm'_def
      have hm'pos : 0 < m' := Nat.ordCompl_pos p hm0
      have hmeq : p ^ e * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hcopp : Nat.Coprime p m' := Nat.coprime_ordCompl hp hm0
      have hcop : Nat.Coprime (p ^ e) m' := Nat.Coprime.pow_left e hcopp
      have htot : Nat.totient m = Nat.totient (p ^ e) * Nat.totient m' := by
        rw [← hmeq, Nat.totient_mul hcop]
      have htotm'pos : Nat.totient m' ≠ 0 := (Nat.totient_pos.mpr hm'pos).ne'
      have htotppos : Nat.totient (p ^ e) ≠ 0 :=
        (Nat.totient_pos.mpr (pow_pos hp.pos e)).ne'
      set v' := (Nat.totient m').factorization 2 with hv'_def
      have hv'le : 2 ^ v' ≤ Nat.totient m' :=
        Nat.le_of_dvd (Nat.totient_pos.mpr hm'pos) (Nat.ordProj_dvd _ 2)
      have hv'le' : 2 ^ v' ≤ m' := hv'le.trans (Nat.totient_le m')
      have hvsplit : (Nat.totient m).factorization 2
          = (Nat.totient (p ^ e)).factorization 2 + v' := by
        rw [htot, Nat.factorization_mul htotppos htotm'pos, Finsupp.add_apply, hv'_def]
      rcases eq_or_ne p 2 with hp2 | hp2
      · -- p = 2 : impossible
        exfalso
        have hfp : (Nat.totient (p ^ e)).factorization 2 = e - 1 := by
          rw [Nat.totient_prime_pow hp he, hp2]
          simp [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) one_ne_zero,
            Nat.factorization_pow, Nat.Prime.factorization Nat.prime_two]
        have h2e : 2 * 2 ^ ((e - 1) + v') = 2 ^ e * 2 ^ v' := by
          rw [← pow_add, ← _root_.pow_succ']
          congr 1
          omega
        rw [hvsplit, hfp, h2e, ← hmeq, hp2] at hlt
        have hm'lt : m' < 2 ^ v' := Nat.lt_of_mul_lt_mul_left hlt
        omega
      · -- p odd
        have hpodd : Odd p := hp.odd_of_ne_two hp2
        have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
        set k := (p - 1).factorization 2 with hk_def
        have hkdvd : 2 ^ k ∣ p - 1 := Nat.ordProj_dvd _ 2
        have hk1 : 1 ≤ k := by
          have h2dvd : 2 ∣ p - 1 := by
            obtain ⟨c, hc⟩ := hpodd
            exact ⟨c, by omega⟩
          exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) h2dvd
        have hfp : (Nat.totient (p ^ e)).factorization 2 = k := by
          rw [Nat.totient_prime_pow hp he,
            Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') (by omega)]
          simp [Nat.factorization_pow, Nat.Prime.factorization hp,
            Finsupp.single_apply, hp2]
          exact hk_def.symm
        have hpge : 2 ^ k < p := by
          have : 2 ^ k ≤ p - 1 := Nat.le_of_dvd (by omega) hkdvd
          omega
        have hltm : m < 2 ^ (k + 1) * 2 ^ v' := by
          have h2e : 2 * 2 ^ (k + v') = 2 ^ (k + 1) * 2 ^ v' := by
            rw [← pow_add, ← _root_.pow_succ']
            congr 1
            omega
          rw [hvsplit, hfp, h2e] at hlt
          exact hlt
        -- key contradiction pattern
        have hkey : ¬ 2 ^ (k + 1) < p ^ e := by
          intro h1
          have h3 : 2 ^ (k + 1) * m' < 2 ^ (k + 1) * 2 ^ v' := by
            calc 2 ^ (k + 1) * m' < p ^ e * m' :=
                  Nat.mul_lt_mul_of_lt_of_le h1 le_rfl hm'pos
              _ = m := hmeq
              _ < 2 ^ (k + 1) * 2 ^ v' := hltm
          have h4 : m' < 2 ^ v' := Nat.lt_of_mul_lt_mul_left h3
          omega
        have he1 : e = 1 := by
          by_contra hne
          apply hkey
          calc 2 ^ (k + 1) ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
            _ < p ^ 2 := Nat.pow_lt_pow_left hpge (by norm_num)
            _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
        set u := ordCompl[2] (p - 1) with hu_def
        have hu_mul : 2 ^ k * u = p - 1 := Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
        have hu_odd : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
        have hu_pos : 0 < u := Nat.ordCompl_pos 2 (by omega)
        have hpeq : p = 2 ^ k + 1 := by
          rcases eq_or_ne u 1 with h1 | h1
          · rw [h1, mul_one] at hu_mul
            omega
          · exfalso
            apply hkey
            have hu3 : 3 ≤ u := by
              rcases Nat.lt_or_ge u 3 with h | h
              · interval_cases u
                · omega
                · exact absurd ⟨1, rfl⟩ hu_odd
              · exact h
            have h3k : 3 * 2 ^ k ≤ p - 1 := by
              calc 3 * 2 ^ k ≤ u * 2 ^ k := Nat.mul_le_mul_right _ hu3
                _ = 2 ^ k * u := mul_comm _ _
                _ = p - 1 := hu_mul
            have h2k1 : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by
              rw [pow_succ]
              ring
            have h2kpos : 0 < 2 ^ k := Nat.two_pow_pos k
            rw [he1, pow_one]
            omega
        -- k is a power of two
        obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (a := 2) one_lt_two
          (by omega : k ≠ 0) (by rw [← hpeq]; exact hp)
        have hpF : p = Nat.fermatNumber j := by
          rw [Nat.fermatNumber, ← hj, ← hpeq]
        -- m' satisfies the hypothesis of the induction
        have hm'lt : m' < 2 * 2 ^ v' := by
          by_contra hcon
          push_neg at hcon
          have h5 : 2 ^ (k + 1) * 2 ^ v' < p * m' := by
            calc 2 ^ (k + 1) * 2 ^ v' = 2 ^ k * (2 * 2 ^ v') := by ring
              _ < p * (2 * 2 ^ v') :=
                  Nat.mul_lt_mul_of_lt_of_le hpge le_rfl (by positivity)
              _ ≤ p * m' := Nat.mul_le_mul_left p hcon
          have h6 : p * m' = m := by rw [← hmeq, he1, pow_one]
          omega
        have hm'ltm : m' < m := by
          have hlt' : m' < p * m' := by
            have h1p : 1 * m' < p * m' :=
              Nat.mul_lt_mul_of_lt_of_le (by omega : 1 < p) le_rfl hm'pos
            rwa [one_mul] at h1p
          rw [← hmeq, he1, pow_one]
          exact hlt'
        obtain ⟨S', hS'prime, hS'prod, hS'sum⟩ := IH m' hm'ltm hm'pos hm'lt
        have hjS' : j ∉ S' := by
          intro hjmem
          have hdvd : Nat.fermatNumber j ∣ m' := by
            rw [hS'prod]
            exact Finset.dvd_prod_of_mem _ hjmem
          rw [← hpF] at hdvd
          have := Nat.eq_one_of_dvd_coprimes hcopp dvd_rfl hdvd
          omega
        refine ⟨insert j S', ?_, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · rw [← hpF]; exact hp
          · exact hS'prime i hi
        · rw [Finset.prod_insert hjS', ← hS'prod, ← hpF, ← hmeq, he1, pow_one]
        · rw [Finset.sum_insert hjS', hvsplit, hfp, hv'_def, hS'sum, hj]

end Oeis53576Aux

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
  have hF33eq : F33 = 2 ^ N + 1 := rfl
  have hNval : N = 2 ^ 33 := rfl
  have hNpos : 0 < N := by rw [hNval]; positivity
  have ha : a N = sInf { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } := rfl
  set s : Set ℕ := { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } with hs_def
  have hmem2 : 2 ^ (N + 1) ∈ s := by
    refine ⟨Nat.two_pow_pos _, ?_⟩
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos N)]
    simp
  have hlb : ∀ m ∈ s, 2 ^ N < m := by
    rintro m ⟨hm0, hmdvd⟩
    have h1 : 2 ^ N ≤ Nat.totient m := Nat.le_of_dvd (Nat.totient_pos.mpr hm0) hmdvd
    have hm1 : 1 < m := by
      by_contra hcon
      have hmm : m = 1 := by omega
      subst hmm
      rw [Nat.totient_one] at h1
      have : 1 < 2 ^ N := Nat.one_lt_two_pow_iff.mpr (by omega)
      omega
    exact h1.trans_lt (Nat.totient_lt m hm1)
  have hkey : ∀ m ∈ s, m < 2 ^ (N + 1) → m = F33 ∧ F33.Prime := by
    rintro m ⟨hm0, hmdvd⟩ hmlt
    have htpos : Nat.totient m ≠ 0 := (Nat.totient_pos.mpr hm0).ne'
    set v := (Nat.totient m).factorization 2 with hv_def
    have hNv : N ≤ v :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two htpos).mp hmdvd
    have hmlt' : m < 2 * 2 ^ v := by
      calc m < 2 ^ (N + 1) := hmlt
        _ = 2 * 2 ^ N := by rw [pow_succ]; ring
        _ ≤ 2 * 2 ^ v := by
            have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hNv
            omega
    obtain ⟨S, hSprime, hSprod, hSsum⟩ := Oeis53576Aux.core m hm0 hmlt'
    have h2vm : 2 ^ v ≤ m := by
      calc 2 ^ v = 2 ^ (∑ j ∈ S, 2 ^ j) := by rw [← hSsum]
        _ = ∏ j ∈ S, 2 ^ (2:ℕ) ^ j := (Finset.prod_pow_eq_pow_sum _ _ _).symm
        _ ≤ ∏ j ∈ S, Nat.fermatNumber j := by
            apply Finset.prod_le_prod'
            intro j _
            rw [Nat.fermatNumber]
            omega
        _ = m := hSprod.symm
    have hvN : v = N := by
      have h7 : 2 ^ v < 2 ^ (N + 1) := lt_of_le_of_lt h2vm hmlt
      have hvlt : v < N + 1 := by
        by_contra hcon
        push_neg at hcon
        have : (2:ℕ) ^ (N + 1) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hcon
        omega
      omega
    have hS33 : S = {33} := by
      apply Oeis53576Aux.finset_eq_of_sum_two_pow_eq
      rw [← hSsum, ← hv_def, hvN, hNval]
    constructor
    · rw [hSprod, hS33, Finset.prod_singleton]
    · have h33 : (33 : ℕ) ∈ S := by rw [hS33]; exact Finset.mem_singleton_self 33
      exact hSprime 33 h33
  rw [ha]
  by_cases hF : F33.Prime
  · rw [if_pos hF]
    have hFmem : F33 ∈ s := by
      refine ⟨by rw [hF33eq]; positivity, ?_⟩
      rw [Nat.totient_prime hF, hF33eq]
      simp
    refine le_antisymm (Nat.sInf_le hFmem) ?_
    have hne : s.Nonempty := ⟨F33, hFmem⟩
    have hmemInf : sInf s ∈ s := Nat.sInf_mem hne
    have := hlb _ hmemInf
    omega
  · rw [if_neg hF]
    refine le_antisymm (Nat.sInf_le hmem2) ?_
    have hne : s.Nonempty := ⟨_, hmem2⟩
    have hmemInf : sInf s ∈ s := Nat.sInf_mem hne
    by_contra hcon
    push_neg at hcon
    exact hF (hkey _ hmemInf hcon).2
