import FormalConjectures.Util.ProblemImports

open Nat Set Finset
open scoped BigOperators

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }


lemma prime_of_factorization_support {m p : ℕ} (hp : p ∈ m.factorization.support) : p.Prime := by
  have hne : m.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  by_contra hprime
  exact hne ((Nat.factorization_eq_zero_iff m p).mpr (Or.inl hprime))

lemma odd_factor_fermat {m N p : ℕ} (hm : m ≠ 0) (hphi : m.totient = 2 ^ N)
    (hp : p ∈ m.factorization.support) (hp2 : p ≠ 2) :
    ∃ j, p = Nat.fermatNumber j ∧ m.factorization p = 1 := by
  have hpprime : p.Prime := prime_of_factorization_support hp
  have hd : p ^ (m.factorization p - 1) * (p - 1) ∣ 2 ^ N := by
    rw [← hphi, Nat.totient_eq_prod_factorization hm]
    exact Finset.dvd_prod_of_mem (fun q => q ^ (m.factorization q - 1) * (q - 1)) hp
  obtain ⟨t, htle, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hfac1 : m.factorization p = 1 := by
    by_contra hne
    have hpos : 0 < m.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hgt : 0 < m.factorization p - 1 := by omega
    have hpdvd_pow : p ∣ p ^ (m.factorization p - 1) := by
      exact dvd_pow_self p (Nat.ne_of_gt hgt)
    have hpdvd_prod : p ∣ p ^ (m.factorization p - 1) * (p - 1) := dvd_mul_of_dvd_left hpdvd_pow _
    have hpdvd_two_pow : p ∣ 2 ^ t := by
      rw [← ht]
      exact hpdvd_prod
    have hpdvd_two : p ∣ 2 := hpprime.dvd_of_dvd_pow hpdvd_two_pow
    have : p = 2 := by
      exact (Nat.Prime.dvd_iff_eq Nat.prime_two (by exact hpprime.ne_one)).mp hpdvd_two |>.symm
    exact hp2 this
  have hpminus_dvd : p - 1 ∣ 2 ^ N := by
    -- p^(1-1)=1
    rw [hfac1, show p ^ (1 - 1) * (p - 1) = p - 1 by simp] at hd
    exact hd
  obtain ⟨r, hrle, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpminus_dvd
  have hp_eq : p = 2 ^ r + 1 := by
    rw [← hr]
    exact (Nat.sub_add_cancel hpprime.one_le).symm
  have hrne : r ≠ 0 := by
    intro hz
    have : p = 2 := by simpa [hz] using hp_eq
    exact hp2 this
  obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (a := 2) (n := r) (by norm_num) hrne (by simpa [hp_eq] using hpprime)
  refine ⟨j, ?_, hfac1⟩
  rw [Nat.fermatNumber, ← hj]
  exact hp_eq
open scoped BigOperators

lemma sum_range_two_pow (n : ℕ) : (∑ i ∈ Finset.range n, 2 ^ i) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hpos : 0 < 2 ^ n := by positivity
    rw [pow_succ]
    omega

lemma finset_sum_two_pow_eq_singleton_33 {S : Finset ℕ}
    (hS : ∑ j ∈ S, 2 ^ j = 2 ^ 33) : S = {33} := by
  have h33mem : 33 ∈ S := by
    by_contra h33
    have hsub : S ⊆ Finset.range 33 := by
      intro x hx
      have hxlepow : 2 ^ x ≤ 2 ^ 33 := by
        rw [← hS]
        exact Finset.single_le_sum (fun y _ => by positivity) hx
      have hxle : x ≤ 33 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hxlepow
      have hxne : x ≠ 33 := by intro h; exact h33 (h ▸ hx)
      exact Finset.mem_range.mpr (lt_of_le_of_ne hxle hxne)
    have hle : ∑ x ∈ S, 2 ^ x ≤ ∑ x ∈ Finset.range 33, 2 ^ x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x _ _; positivity)
    rw [hS, sum_range_two_pow] at hle
    have hpowpos : 0 < 2 ^ 33 := by positivity
    omega
  apply Finset.ext
  intro j
  constructor
  · intro hj
    have hjlepow : 2 ^ j ≤ 2 ^ 33 := by
      rw [← hS]
      exact Finset.single_le_sum (fun x _ => by positivity) hj
    have hjle : j ≤ 33 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hjlepow
    by_contra hjnot
    have hjne : j ≠ 33 := by simpa using hjnot
    have hle : 2 ^ j + 2 ^ 33 ≤ ∑ x ∈ S, 2 ^ x := by
      calc
        2 ^ j + 2 ^ 33 = ∑ x ∈ ({j,33} : Finset ℕ), 2 ^ x := by simp [hjne]
        _ ≤ ∑ x ∈ S, 2 ^ x := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp at hx
            rcases hx with rfl | rfl
            · exact hj
            · exact h33mem
          · intro x _ _; positivity
    rw [hS] at hle
    have : 0 < 2 ^ j := by positivity
    omega
  · intro hj
    have hj_eq : j = 33 := by simpa using hj
    simpa [hj_eq] using h33mem

lemma odd_phi_power_two_eq_fermat33 {m : ℕ} (hm : m ≠ 0) (hodd : Odd m)
    (hphi : m.totient = 2 ^ (2 ^ 33)) : m = Nat.fermatNumber 33 := by
  classical
  let S := m.factorization.support
  have hp2_ne (p : ℕ) (hp : p ∈ S) : p ≠ 2 := by
    intro hpeq
    have hpprime : p.Prime := prime_of_factorization_support hp
    have hpdvd : p ∣ m := (Nat.Prime.dvd_iff_one_le_factorization hpprime hm).mpr
      (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)))
    exact hodd.not_two_dvd_nat (hpeq ▸ hpdvd)
  let idx : {p // p ∈ S} → ℕ := fun x => Classical.choose (odd_factor_fermat hm hphi x.2 (hp2_ne x x.2))
  have hidx_spec (x : {p // p ∈ S}) : (x : ℕ) = Nat.fermatNumber (idx x) ∧ m.factorization (x : ℕ) = 1 :=
    Classical.choose_spec (odd_factor_fermat hm hphi x.2 (hp2_ne x x.2))
  have hinj : Function.Injective idx := by
    intro x y hxy
    apply Subtype.ext
    have hx := (hidx_spec x).1
    have hy := (hidx_spec y).1
    rw [hx, hy, hxy]
  let J : Finset ℕ := S.attach.image idx
  have hsumJ : ∑ j ∈ J, 2 ^ j = 2 ^ 33 := by
    have hprod1 : ∏ p ∈ S, (p ^ (m.factorization p - 1) * (p - 1)) = ∏ p ∈ S, (p - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hs := (hidx_spec ⟨p,hp⟩).2
      simp [hs]
    have hphi_prod : ∏ p ∈ S, (p - 1) = 2 ^ (2 ^ 33) := by
      rw [← hphi, Nat.totient_eq_prod_factorization hm]
      exact hprod1.symm
    have hprod_idx : ∏ x ∈ S.attach, (2 : ℕ) ^ (2 ^ idx x) = 2 ^ (2 ^ 33) := by
      rw [← hphi_prod]
      rw [← Finset.prod_attach S (fun p => p - 1)]
      apply Finset.prod_congr rfl
      intro x hx
      have hs := (hidx_spec x).1
      rw [hs, Nat.fermatNumber]
      simp
    have hpowsum : (2 : ℕ) ^ (∑ x ∈ S.attach, 2 ^ idx x) = 2 ^ (2 ^ 33) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact hprod_idx
    have hsum_attach : ∑ x ∈ S.attach, 2 ^ idx x = 2 ^ 33 :=
      (Nat.pow_right_injective (by norm_num : 1 < 2)) hpowsum
    rw [Finset.sum_image]
    · exact hsum_attach
    · intro x hx y hy hxy
      exact hinj hxy
  have hJ : J = {33} := finset_sum_two_pow_eq_singleton_33 hsumJ
  have hsupp_eq : S = {Nat.fermatNumber 33} := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      have hmemJ : idx ⟨p,hp⟩ ∈ J := by
        exact Finset.mem_image.mpr ⟨⟨p,hp⟩, by simp, rfl⟩
      rw [hJ] at hmemJ
      have hidx33 : idx ⟨p,hp⟩ = 33 := by simpa using hmemJ
      have hp_eq := (hidx_spec ⟨p,hp⟩).1
      rw [Finset.mem_singleton]
      simpa [hidx33] using hp_eq
    · intro hp
      have hp_eq : p = Nat.fermatNumber 33 := by simpa using hp
      subst p
      -- need show F33 in support. Since J={33}, there is x in S.attach with idx x=33.
      have h33J : 33 ∈ J := by simp [hJ]
      rcases Finset.mem_image.mp h33J with ⟨x, hxS, hxidx⟩
      have hx_eq := (hidx_spec x).1
      have : (x : ℕ) = Nat.fermatNumber 33 := by simpa [hxidx] using hx_eq
      simpa [this] using x.2
  have hfac_eq : m.factorization = (Finsupp.single (Nat.fermatNumber 33) 1 : ℕ →₀ ℕ) := by
    apply Finsupp.ext
    intro p
    by_cases hp : p ∈ S
    · have hp_eq : p = Nat.fermatNumber 33 := by
        have : p ∈ ({Nat.fermatNumber 33} : Finset ℕ) := by simpa [hsupp_eq] using hp
        simpa using this
      subst p
      have : (Nat.fermatNumber 33) ∈ S := by simp [hsupp_eq]
      rw [Finsupp.single_eq_same]
      exact (hidx_spec ⟨Nat.fermatNumber 33, this⟩).2
    · have hzero : m.factorization p = 0 := by
        by_contra hne
        exact hp ((Finsupp.mem_support_iff).mpr hne)
      rw [hzero]
      rw [Finsupp.single_eq_of_ne]
      intro hp_eq
      apply hp
      simp [hsupp_eq, hp_eq]
  calc
    m = m.factorization.prod (fun p k => p ^ k) := (Nat.factorization_prod_pow_eq_self hm).symm
    _ = Nat.fermatNumber 33 := by
      rw [hfac_eq]
      rw [Finsupp.prod_single_index]
      · simp
      · simp

private lemma factor_pos_of_mul_pos {a k : ℕ} (h : 0 < a * k) : 0 < k := by
  by_contra hk
  have : k = 0 := by omega
  subst k
  simp at h

private lemma two_mul_totient_le_of_even : ∀ m : ℕ, Even m → 2 * m.totient ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    rcases hm with ⟨n, rfl⟩
    rw [← two_mul n]
    by_cases n0 : n = 0
    · subst n; simp
    by_cases hn : Even n
    · rw [Nat.totient_two_mul_of_even hn]
      have hnlt' : n < n + n := by nlinarith [Nat.pos_of_ne_zero n0]
      have := ih n hnlt' hn
      nlinarith
    · have hodd : Odd n := Nat.not_even_iff_odd.mp hn
      rw [Nat.totient_two_mul_of_odd hodd]
      have := Nat.totient_le n
      nlinarith

private lemma two_pow_dvd_totient_two_pow_succ (N : ℕ) :
    2 ^ N ∣ (2 ^ (N + 1)).totient := by
  rw [Nat.totient_prime_pow Nat.prime_two]
  · rw [Nat.add_sub_cancel, show 2 - 1 = 1 by norm_num, mul_one]
  · positivity

private lemma totient_eq_of_dvd_of_lt_two_mul {m N : ℕ} (hmpos : 0 < m)
    (hdiv : 2 ^ N ∣ m.totient) (hlt : m < 2 ^ (N + 1)) : m.totient = 2 ^ N := by
  obtain ⟨k, hk⟩ := hdiv
  have hphipos : 0 < m.totient := Nat.totient_pos.mpr hmpos
  have hkpos : 0 < k := by
    apply factor_pos_of_mul_pos
    rw [← hk]
    exact hphipos
  have hlt' : 2 ^ N * k < 2 ^ N * 2 := by
    rw [← hk]
    have hle := Nat.totient_le m
    have hlt2 : m < 2 ^ N * 2 := by
      simpa [Nat.pow_succ', mul_comm, mul_left_comm, mul_assoc] using hlt
    exact lt_of_le_of_lt hle hlt2
  have hklt : k < 2 := (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ N)).mp hlt'
  have hk1 : k = 1 := by omega
  rw [hk, hk1, mul_one]

private lemma two_pow_succ_mem (N : ℕ) :
    2 ^ (N + 1) ∈ { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } := by
  constructor
  · positivity
  · exact two_pow_dvd_totient_two_pow_succ N

private lemma a_le_two_pow_succ (N : ℕ) : a N ≤ 2 ^ (N + 1) := by
  dsimp [a]
  exact Nat.sInf_le (two_pow_succ_mem N)

private lemma two_pow_succ_le_a_of_forall (N : ℕ)
    (h : ∀ m : ℕ, m ∈ { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } → 2 ^ (N + 1) ≤ m) :
    2 ^ (N + 1) ≤ a N := by
  dsimp [a]
  apply le_csInf
  · exact ⟨2 ^ (N + 1), two_pow_succ_mem N⟩
  · exact h

private lemma nat_lt_add_one_le {m K : ℕ} (h : m < K + 1) : m ≤ K := by
  have hz : (m : ℤ) < (K : ℤ) + 1 := by exact_mod_cast h
  have hzle : (m : ℤ) ≤ (K : ℤ) := by omega
  exact_mod_cast hzle

private lemma two_mul_two_pow_eq (N : ℕ) : 2 * 2 ^ N = 2 ^ (N + 1) := by
  rw [Nat.pow_succ']

private lemma le_mul_of_pos_right_nat (a : ℕ) {k : ℕ} (hk : 0 < k) : a ≤ a * k := by
  calc
    a = a * 1 := by simp
    _ ≤ a * k := Nat.mul_le_mul_left _ hk

private lemma fermatNumber_sub_one (n : ℕ) : Nat.fermatNumber n - 1 = 2 ^ (2 ^ n) := by
  rw [Nat.fermatNumber, Nat.add_sub_cancel]

private lemma lt_fermatNumber_le {n m : ℕ} (h : m < Nat.fermatNumber n) : m ≤ 2 ^ (2 ^ n) := by
  rw [Nat.fermatNumber] at h
  exact nat_lt_add_one_le h

private lemma two_pow_two_pow_33_gt_two : 2 < 2 ^ (2 ^ 33) := by
  have hle : 2 ≤ 2 ^ 33 := by norm_num
  calc
    2 = 2 ^ 1 := by norm_num
    _ < 2 ^ (2 ^ 33) := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  change a (2 ^ 33) = if (Nat.fermatNumber 33).Prime then Nat.fermatNumber 33 else 2 ^ (2 ^ 33 + 1)
  by_cases hprime : (Nat.fermatNumber 33).Prime
  · rw [if_pos hprime]
    apply le_antisymm
    · dsimp [a]
      apply Nat.sInf_le
      constructor
      · exact Nat.Prime.pos hprime
      · rw [Nat.totient_prime hprime, fermatNumber_sub_one]
        exact dvd_rfl
    · dsimp [a]
      apply le_csInf
      · exact ⟨Nat.fermatNumber 33, by
          constructor
          · exact Nat.Prime.pos hprime
          · rw [Nat.totient_prime hprime, fermatNumber_sub_one]
            exact dvd_rfl⟩
      · intro m hm
        by_contra hlt_not
        have hlt : m < Nat.fermatNumber 33 := Nat.lt_of_not_ge hlt_not
        have hmle : m ≤ 2 ^ (2 ^ 33) := lt_fermatNumber_le hlt
        have hdiv := hm.2
        obtain ⟨k, hk⟩ := hdiv
        have hphipos : 0 < m.totient := Nat.totient_pos.mpr hm.1
        have hkpos : 0 < k := by
          apply factor_pos_of_mul_pos
          rw [← hk]
          exact hphipos
        have hpow_le_phi : 2 ^ (2 ^ 33) ≤ m.totient := by
          rw [hk]
          exact le_mul_of_pos_right_nat _ hkpos
        have hmge : 2 ^ (2 ^ 33) ≤ m := le_trans hpow_le_phi (Nat.totient_le m)
        have hmgt2 : 2 < m := lt_of_lt_of_le two_pow_two_pow_33_gt_two hmge
        have htotlt : m.totient < m := Nat.totient_lt m (one_lt_two.trans hmgt2)
        exact (not_lt_of_ge hpow_le_phi) (lt_of_lt_of_le htotlt hmle)
  · rw [if_neg hprime]
    apply le_antisymm
    · exact a_le_two_pow_succ (2 ^ 33)
    · apply two_pow_succ_le_a_of_forall (2 ^ 33)
      intro m hm
      by_contra hlt_not
      have hlt : m < 2 ^ (2 ^ 33 + 1) := Nat.lt_of_not_ge hlt_not
      have hphi : m.totient = 2 ^ (2 ^ 33) :=
        totient_eq_of_dvd_of_lt_two_mul hm.1 hm.2 hlt
      by_cases hmeven : Even m
      · have hle := two_mul_totient_le_of_even m hmeven
        rw [hphi] at hle
        have : 2 ^ (2 ^ 33 + 1) ≤ m := by
          rw [← two_mul_two_pow_eq]
          exact hle
        exact hlt_not this
      · have hmodd : Odd m := Nat.not_even_iff_odd.mp hmeven
        have hmne : m ≠ 0 := Nat.ne_of_gt hm.1
        have hmF : m = Nat.fermatNumber 33 := odd_phi_power_two_eq_fermat33 hmne hmodd hphi
        have hphiF : (Nat.fermatNumber 33).totient = 2 ^ (2 ^ 33) := by
          simpa [hmF] using hphi
        have htotF : (Nat.fermatNumber 33).totient = Nat.fermatNumber 33 - 1 := by
          rw [hphiF, fermatNumber_sub_one]
        have hFprime : (Nat.fermatNumber 33).Prime :=
          (Nat.totient_eq_iff_prime (Nat.zero_lt_of_lt (Nat.two_lt_fermatNumber 33))).mp htotF
        exact hprime hFprime
