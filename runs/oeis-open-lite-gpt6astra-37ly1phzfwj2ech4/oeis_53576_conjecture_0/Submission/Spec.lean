import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

-- An even integer has at most half as many units as residues.
private lemma even_totient_bound (m : ℕ) (hm : Even m) : 2 * totient m ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · simp [hz]
    obtain ⟨r, hr⟩ := hm.two_dvd
    subst m
    have hrpos : 0 < r := by omega
    rcases Nat.even_or_odd r with he | ho
    · rw [Nat.totient_two_mul_of_even he]
      have hi := ih r (by omega) he
      omega
    · rw [Nat.totient_two_mul_of_odd ho]
      have := Nat.totient_le r
      omega

-- Odd integers with power-of-two totient cannot have repeated prime factors.
private lemma odd_squarefree_of_totient_pow {m n : ℕ} (hm : Odd m)
    (ht : totient m = 2 ^ n) : Squarefree m := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hpd : p ∣ m := (dvd_mul_right p p).trans hd
  have htdiv := Nat.totient_dvd_of_dvd hd
  have hcalc : totient (p * p) = p * (p - 1) := by
    simpa [pow_two] using Nat.totient_prime_pow_succ hp 1
  rw [hcalc, ht] at htdiv
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow ((dvd_mul_right p (p - 1)).trans htdiv)
  have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  exact hm.not_two_dvd_nat (hpeq ▸ hpd)

private lemma prime_factor_fermat {m k p : ℕ} (hm : Odd m)
    (ht : totient m = 2 ^ (2 ^ k)) (hp : p.Prime) (hpd : p ∣ m) :
    ∃ i ≤ k, p = Nat.fermatNumber i := by
  have hd : p - 1 ∣ 2 ^ (2 ^ k) := by
    simpa [Nat.totient_prime hp, ht] using Nat.totient_dvd_of_dvd hpd
  obtain ⟨j, hj, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hpform : p = 2 ^ j + 1 := by have := hp.two_le; omega
  have hj0 : j ≠ 0 := by
    intro hz
    have hpeq : p = 2 := by simpa [hz] using hpform
    exact hm.not_two_dvd_nat (hpeq ▸ hpd)
  obtain ⟨i, hi⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < (2 : ℕ)) hj0
    (hpform ▸ hp)
  refine ⟨i, ?_, ?_⟩
  · rw [hi] at hj
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hj
  · simpa [Nat.fermatNumber, hi] using hpform

private lemma small_totient_candidate {m k : ℕ} (hm : 0 < m)
    (hd : 2 ^ (2 ^ k) ∣ totient m) (hlt : m < 2 ^ (2 ^ k + 1)) :
    m = Nat.fermatNumber k ∧ (Nat.fermatNumber k).Prime := by
  have hpow : 0 < (2 : ℕ) ^ (2 ^ k) := by positivity
  have htle : 2 ^ (2 ^ k) ≤ totient m := Nat.le_of_dvd (Nat.totient_pos.mpr hm) hd
  have ht : totient m = 2 ^ (2 ^ k) := by
    apply Nat.eq_of_dvd_of_lt_two_mul (Nat.totient_pos.mpr hm).ne' hd
    have := Nat.totient_le m
    rw [pow_succ] at hlt
    omega
  have ho : Odd m := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have := even_totient_bound m he
    rw [pow_succ] at hlt
    omega
  have hs := odd_squarefree_of_totient_pow ho ht
  have hf : Nat.fermatNumber k ∣ m := by
    by_contra hn
    have hdiv : m ∣ ∏ i ∈ Finset.range k, Nat.fermatNumber i := by
      rw [← Nat.prod_primeFactors_of_squarefree hs]
      apply Finset.prod_dvd_of_isRelPrime
      · intro p hp q hq hpq
        exact (Nat.coprime_iff_isRelPrime.mp
          ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
            (Nat.prime_of_mem_primeFactors hq)).mpr hpq))
      · intro p hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        obtain ⟨i, hik, hpi⟩ := prime_factor_fermat ho ht
          (Nat.prime_of_mem_primeFactors hp) hpd
        have hik' : i < k := by
          by_contra h
          have : i = k := by omega
          exact hn (by simpa [hpi, this] using hpd)
        rw [hpi]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hik')
    have hprodpos : 0 < ∏ i ∈ Finset.range k, Nat.fermatNumber i :=
      Finset.prod_pos (fun i _ => lt_trans (by decide : 0 < 2) (Nat.two_lt_fermatNumber i))
    have hle := Nat.le_of_dvd hprodpos hdiv
    rw [Nat.prod_fermatNumber, Nat.fermatNumber] at hle
    have := Nat.totient_le m
    omega
  have heq : m = Nat.fermatNumber k := by
    apply Nat.eq_of_dvd_of_lt_two_mul hm.ne' hf
    rw [pow_succ] at hlt
    unfold Nat.fermatNumber
    omega
  refine ⟨heq, ?_⟩
  apply (Nat.totient_eq_iff_prime (by have := Nat.two_lt_fermatNumber k; omega)).mp
  rw [← heq, ht, heq, Nat.fermatNumber]
  omega

private lemma fermat_totient_minimum (k : ℕ) :
    a (2 ^ k) = if (Nat.fermatNumber k).Prime then Nat.fermatNumber k
      else 2 ^ (2 ^ k + 1) := by
  have hmem : 2 ^ (2 ^ k + 1) ∈ {m : ℕ | 0 < m ∧ 2 ^ (2 ^ k) ∣ totient m} := by
    constructor
    · positivity
    · simp [Nat.totient_prime_pow_succ Nat.prime_two]
  have hnonempty : {m : ℕ | 0 < m ∧ 2 ^ (2 ^ k) ∣ totient m}.Nonempty := ⟨_, hmem⟩
  have hFle : Nat.fermatNumber k ≤ 2 ^ (2 ^ k + 1) := by
    have : 0 < (2 : ℕ) ^ (2 ^ k) := by positivity
    rw [Nat.fermatNumber, pow_succ]
    omega
  unfold a
  split_ifs with hp
  · apply le_antisymm
    · apply Nat.sInf_le
      constructor
      · have := Nat.two_lt_fermatNumber k
        omega
      · rw [Nat.totient_prime hp]
        simp [Nat.fermatNumber]
    · apply le_csInf hnonempty
      intro m hm
      by_cases hlt : m < 2 ^ (2 ^ k + 1)
      · exact (small_totient_candidate hm.1 hm.2 hlt).1.ge
      · exact hFle.trans (by omega)
  · apply le_antisymm (Nat.sInf_le hmem)
    apply le_csInf hnonempty
    intro m hm
    by_contra h
    have hlt : m < 2 ^ (2 ^ k + 1) := by omega
    exact hp (small_totient_candidate hm.1 hm.2 hlt).2

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  exact fermat_totient_minimum 33

theorem oeis_53576_conjecture_0.disproof : ¬ (type_of% @oeis_53576_conjecture_0) := sorry
