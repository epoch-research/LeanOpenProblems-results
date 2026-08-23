import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

lemma two_totient_le_of_even : ∀ m : ℕ, Even m → 2 * m.totient ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rintro ⟨k, rfl⟩
    rw [← two_mul k]
    rcases k.eq_zero_or_pos with rfl | hkpos
    · norm_num

    by_cases hk : Even k
    · rw [Nat.totient_two_mul_of_even hk]
      have hi := ih k (by omega) hk
      omega
    · have hk' : Odd k := Nat.not_even_iff_odd.mp hk
      rw [Nat.totient_two_mul_of_odd hk']
      exact Nat.mul_le_mul_left 2 (Nat.totient_le k)

lemma pow_two_witness (n : ℕ) :
    0 < 2 ^ (n + 1) ∧ 2 ^ n ∣ Nat.totient (2 ^ (n + 1)) := by
  constructor
  · positivity
  · rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp

lemma factorization_eq_one_of_odd_totient_pow {m n p : ℕ}
    (hm : Odd m) (ht : m.totient = 2 ^ n) (hp : p ∈ m.primeFactors) :
    m.factorization p = 1 := by
  have hm0 : m ≠ 0 := (hm.pos).ne'
  have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have pdm : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
  have hkpos : 0 < m.factorization p := pp.factorization_pos_of_dvd hm0 pdm
  have hpow : p ^ m.factorization p ∣ m :=
    (pp.pow_dvd_iff_le_factorization hm0).2 le_rfl
  have hd := Nat.totient_dvd_of_dvd hpow
  rw [Nat.totient_prime_pow pp hkpos, ht] at hd
  apply Nat.le_antisymm
  · by_contra hk
    have hk2 : 2 ≤ m.factorization p := by omega
    have hpd : p ∣ p ^ (m.factorization p - 1) * (p - 1) := by
      apply dvd_mul_of_dvd_left
      exact dvd_pow_self p (by omega)
    have hp2pow : p ∣ 2 ^ n := hpd.trans hd
    have hp2 : p ∣ 2 := pp.dvd_of_dvd_pow hp2pow
    have peq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left pp.ne_one
    exact hm.not_two_dvd_nat (peq ▸ pdm)
  · exact hkpos


lemma totient_eq_prod_primeFactors_sub_one_of_odd_pow {m n : ℕ}
    (hm : Odd m) (ht : m.totient = 2 ^ n) :
    m.totient = ∏ p ∈ m.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_prod_factorization (hm.pos.ne')]
  calc
    m.factorization.prod (fun p k => p ^ (k - 1) * (p - 1)) =
        m.factorization.prod (fun p _ => p - 1) := by
      apply Finsupp.prod_congr
      intro p hp
      have hp' : p ∈ m.primeFactors := by simpa [Nat.support_factorization] using hp
      rw [factorization_eq_one_of_odd_totient_pow hm ht hp']
      simp
    _ = ∏ p ∈ m.primeFactors, (p - 1) :=
      (Nat.prod_primeFactors_prod_factorization (fun p => p - 1)).symm

lemma primeFactor_eq_fermatNumber_of_odd_totient_pow {m n p : ℕ}
    (hm : Odd m) (ht : m.totient = 2 ^ n) (hp : p ∈ m.primeFactors) :
    ∃ i : ℕ, p = Nat.fermatNumber i := by
  have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have pdm : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
  have hprod := totient_eq_prod_primeFactors_sub_one_of_odd_pow hm ht
  have hdprod : p - 1 ∣ ∏ q ∈ m.primeFactors, (q - 1) :=
    Finset.dvd_prod_of_mem (fun q => q - 1) hp
  have hdpow : p - 1 ∣ 2 ^ n := by
    rw [← ht, hprod]
    exact hdprod
  obtain ⟨e, he_le, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdpow
  have he0 : e ≠ 0 := by
    intro he0
    subst e
    simp only [pow_zero] at he
    have peq : p = 2 := by omega
    exact hm.not_two_dvd_nat (peq ▸ pdm)
  have peq : p = 2 ^ e + 1 := Nat.eq_add_of_sub_eq pp.one_lt.le he
  obtain ⟨i, hi⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) he0 (peq ▸ pp)
  refine ⟨i, ?_⟩
  rw [Nat.fermatNumber, ← hi]
  exact peq


lemma exists_index_eq_of_sum_pow_two {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (k : ℕ)
    (hinj : Set.InjOn f (↑s : Set α))
    (hsum : ∑ x ∈ s, 2 ^ f x = 2 ^ k) :
    ∃ x ∈ s, f x = k := by
  classical
  have hle : ∀ x ∈ s, f x ≤ k := by
    intro x hx
    have hterm : 2 ^ f x ≤ ∑ y ∈ s, 2 ^ f y :=
      Finset.single_le_sum (s := s) (f := fun y => 2 ^ f y)
        (fun _ _ => Nat.zero_le _) hx
    rw [hsum] at hterm
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hterm
  by_contra hnone
  push_neg at hnone
  have hlt : ∀ x ∈ s, f x < k := by
    intro x hx
    have := hle x hx
    have := hnone x hx
    omega
  have himage : s.image f ⊆ Finset.range k := by
    rw [Finset.image_subset_iff]
    intro x hx
    simpa using hlt x hx
  have hbound : ∑ i ∈ s.image f, 2 ^ i ≤ ∑ i ∈ Finset.range k, 2 ^ i :=
    Finset.sum_le_sum_of_subset himage
  have himage_sum : ∑ i ∈ s.image f, 2 ^ i = ∑ x ∈ s, 2 ^ f x :=
    Finset.sum_image hinj
  have hgeom : ∑ i ∈ Finset.range k, 2 ^ i = 2 ^ k - 1 := by
    simpa using Nat.geomSum_eq (m := 2) (by norm_num) k
  rw [himage_sum, hsum, hgeom] at hbound
  have : 0 < 2 ^ k := by positivity
  omega

lemma fermatNumber_prime_dvd_of_odd_totient {m k : ℕ}
    (hm : Odd m) (ht : m.totient = 2 ^ (2 ^ k)) :
    (Nat.fermatNumber k).Prime ∧ Nat.fermatNumber k ∣ m := by
  classical
  let idx : ℕ → ℕ := fun p =>
    if hp : p ∈ m.primeFactors then
      Classical.choose (primeFactor_eq_fermatNumber_of_odd_totient_pow hm ht hp)
    else 0
  have hidx : ∀ p ∈ m.primeFactors, p = Nat.fermatNumber (idx p) := by
    intro p hp
    simp only [idx, dif_pos hp]
    exact Classical.choose_spec
      (primeFactor_eq_fermatNumber_of_odd_totient_pow hm ht hp)
  have hinj : Set.InjOn idx (↑m.primeFactors : Set ℕ) := by
    intro p hp q hq heq
    calc
      p = Nat.fermatNumber (idx p) := hidx p hp
      _ = Nat.fermatNumber (idx q) := by rw [heq]
      _ = q := (hidx q hq).symm
  have hprod := totient_eq_prod_primeFactors_sub_one_of_odd_pow hm ht
  have hprodPow : ∏ p ∈ m.primeFactors, 2 ^ (2 ^ idx p) = 2 ^ (2 ^ k) := by
    rw [← ht, hprod]
    apply Finset.prod_congr rfl
    intro p hp
    calc
      2 ^ (2 ^ idx p) = Nat.fermatNumber (idx p) - 1 := by
        simp [Nat.fermatNumber]
      _ = p - 1 := by rw [← hidx p hp]
  rw [Finset.prod_pow_eq_pow_sum] at hprodPow
  have hsum : ∑ p ∈ m.primeFactors, 2 ^ idx p = 2 ^ k :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hprodPow
  obtain ⟨p, hp, hpidx⟩ :=
    exists_index_eq_of_sum_pow_two m.primeFactors idx k hinj hsum
  have hpF : p = Nat.fermatNumber k := by
    rw [hidx p hp, hpidx]
  have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have pdm : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
  constructor
  · rwa [← hpF]
  · rwa [← hpF]

lemma fermatNumber_prime_dvd_of_small_witness {m k : ℕ}
    (hmpos : 0 < m)
    (hd : 2 ^ (2 ^ k) ∣ m.totient)
    (hlt : m < 2 ^ (2 ^ k + 1)) :
    (Nat.fermatNumber k).Prime ∧ Nat.fermatNumber k ∣ m := by
  obtain ⟨c, hc⟩ := hd
  have htpos : 0 < m.totient := Nat.totient_pos.mpr hmpos
  have htlt : m.totient < 2 ^ (2 ^ k + 1) :=
    lt_of_le_of_lt (Nat.totient_le m) hlt
  rw [hc, pow_succ] at htlt
  have hbase : 0 < 2 ^ (2 ^ k) := by positivity
  have hclt : c < 2 := (Nat.mul_lt_mul_left hbase).mp htlt
  have hcpos : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    subst c
    simp at hc
    exact hmpos.ne' hc
  have hc1 : c = 1 := by omega
  have ht : m.totient = 2 ^ (2 ^ k) := by simpa [hc1] using hc
  have hodd : Odd m := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have htwo := two_totient_le_of_even m heven
    rw [ht] at htwo
    have hcand : 2 ^ (2 ^ k + 1) ≤ m := by
      rw [pow_succ]
      simpa [mul_comm] using htwo
    omega
  exact fermatNumber_prime_dvd_of_odd_totient hodd ht

lemma a_formula (k : ℕ) :
    a (2 ^ k) = if (Nat.fermatNumber k).Prime then
      Nat.fermatNumber k else 2 ^ (2 ^ k + 1) := by
  by_cases hF : (Nat.fermatNumber k).Prime
  · rw [if_pos hF]
    unfold a
    have hwF : Nat.fermatNumber k ∈
        {m : ℕ | m > 0 ∧ 2 ^ (2 ^ k) ∣ m.totient} := by
      constructor
      · exact (Nat.three_le_fermatNumber k).trans_lt' (by norm_num)
      · rw [Nat.totient_prime hF, Nat.fermatNumber, Nat.add_sub_cancel]
    apply le_antisymm
    · exact Nat.sInf_le hwF
    · apply le_csInf ⟨_, hwF⟩
      intro m hm
      rcases hm with ⟨hmpos, hd⟩
      by_contra hnle
      have hltF : m < Nat.fermatNumber k := Nat.lt_of_not_ge hnle
      have hFcand : Nat.fermatNumber k < 2 ^ (2 ^ k + 1) := by
        rw [Nat.fermatNumber, pow_succ, Nat.mul_two]
        have he : 2 ^ k ≠ 0 := pow_ne_zero k (by norm_num)
        have hx : 1 < 2 ^ (2 ^ k) := Nat.one_lt_pow he (by norm_num)
        exact Nat.add_lt_add_left hx _
      have hsmall := fermatNumber_prime_dvd_of_small_witness hmpos hd
        (hltF.trans hFcand)
      exact hnle (Nat.le_of_dvd hmpos hsmall.2)
  · rw [if_neg hF]
    unfold a
    have hwP : 2 ^ (2 ^ k + 1) ∈
        {m : ℕ | m > 0 ∧ 2 ^ (2 ^ k) ∣ m.totient} :=
      pow_two_witness (2 ^ k)
    apply le_antisymm
    · exact Nat.sInf_le hwP
    · apply le_csInf ⟨_, hwP⟩
      intro m hm
      rcases hm with ⟨hmpos, hd⟩
      by_contra hnle
      have hlt : m < 2 ^ (2 ^ k + 1) := Nat.lt_of_not_ge hnle
      exact hF (fermatNumber_prime_dvd_of_small_witness hmpos hd hlt).1

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  exact a_formula 33
