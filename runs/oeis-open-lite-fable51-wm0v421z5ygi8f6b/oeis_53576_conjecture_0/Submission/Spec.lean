import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

namespace A053576

/-- Key invariant: if `2^k ∣ φ m` then either `m ≥ 2^(k+1)`, or `m` is a product of distinct
Fermat primes `F_j` (`j ∈ S`) with `k ≤ ∑ 2^j`. -/
def Q (m : ℕ) : Prop :=
  ∀ k : ℕ, 2 ^ k ∣ φ m →
    2 ^ (k + 1) ≤ m ∨
    ∃ S : Finset ℕ, (∀ j ∈ S, (fermatNumber j).Prime) ∧
      m = ∏ j ∈ S, fermatNumber j ∧ k ≤ ∑ j ∈ S, 2 ^ j

lemma Q_one : Q 1 := by
  intro k hk
  right
  refine ⟨∅, by simp, by simp, ?_⟩
  simp only [totient_one, Nat.dvd_one] at hk
  have : k = 0 := by
    rcases Nat.pow_eq_one.mp hk with h | h
    · omega
    · exact h
  simp [this]

lemma Q_prime_pow (p n : ℕ) (hp : p.Prime) (hn : 0 < n) : Q (p ^ n) := by
  intro k hk
  rw [totient_prime_pow hp hn] at hk
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- p = 2
    left
    have hk1 : 2 ^ k ∣ 2 ^ (n - 1) := by simpa using hk
    have hk' := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hk1
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- p odd
    have hcop : Nat.Coprime (2 ^ k) (p ^ (n - 1)) :=
      Nat.Coprime.pow _ _ (Nat.coprime_two_left.mpr hodd)
    have hk2 : 2 ^ k ∣ p - 1 := hcop.dvd_of_dvd_mul_left hk
    obtain ⟨t, ht⟩ := hk2
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases hodd with ⟨r, hr⟩
      omega
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · simp at ht; omega
      · exact h
    have hp_ge : 2 ^ k + 1 ≤ p := by
      have : 2 ^ k ≤ 2 ^ k * t := Nat.le_mul_of_pos_right _ ht1
      omega
    rcases Nat.lt_or_ge 1 n with hn2 | hn1
    · -- n ≥ 2
      left
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
        _ = p ^ 2 := (sq p).symm
        _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn2
    · -- n = 1
      have hn1' : n = 1 := by omega
      subst hn1'
      rw [pow_one]
      rcases Nat.lt_or_ge 1 t with ht2 | ht1'
      · left
        have : 2 ^ k * 2 ≤ 2 ^ k * t := Nat.mul_le_mul_left _ ht2
        rw [pow_succ]; omega
      · have ht' : t = 1 := by omega
        subst ht'
        rw [mul_one] at ht
        have hpk : p = 2 ^ k + 1 := by omega
        have hk0 : k ≠ 0 := by
          rintro rfl
          simp at hpk
          omega
        obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) hk0 (hpk ▸ hp)
        right
        refine ⟨{j}, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_singleton] at hi
          subst hi
          rw [fermatNumber, ← hj, ← hpk]
          exact hp
        · simp [fermatNumber, ← hj, hpk]
        · simp [hj]

lemma Q_mul (a b : ℕ) (ha : 1 < a) (hb : 1 < b) (hab : Nat.Coprime a b)
    (Qa : Q a) (Qb : Q b) : Q (a * b) := by
  intro k hk
  rw [totient_mul hab] at hk
  have hφa : φ a ≠ 0 := (totient_pos.mpr (by omega)).ne'
  have hφb : φ b ≠ 0 := (totient_pos.mpr (by omega)).ne'
  obtain ⟨ka, ma, hma, hφa'⟩ := Nat.exists_eq_two_pow_mul_odd hφa
  obtain ⟨kb, mb, hmb, hφb'⟩ := Nat.exists_eq_two_pow_mul_odd hφb
  rw [hφa', hφb'] at hk
  have hk' : 2 ^ k ∣ 2 ^ (ka + kb) * (ma * mb) := by
    rw [pow_add]; convert hk using 1; ring
  have hcop : Nat.Coprime (2 ^ k) (ma * mb) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (hma.mul hmb))
  have hkle : k ≤ ka + kb :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hk')
  have hda : 2 ^ ka ∣ φ a := ⟨ma, hφa'⟩
  have hdb : 2 ^ kb ∣ φ b := ⟨mb, hφb'⟩
  have hla : 2 ^ ka ≤ a :=
    (Nat.le_of_dvd (totient_pos.mpr (by omega)) hda).trans (totient_le a)
  have hlb : 2 ^ kb ≤ b :=
    (Nat.le_of_dvd (totient_pos.mpr (by omega)) hdb).trans (totient_le b)
  rcases Qa ka hda with h1 | ⟨Sa, hSa, hSa', hSa''⟩
  · left
    calc 2 ^ (k + 1) ≤ 2 ^ (ka + 1 + kb) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ (ka + 1) * 2 ^ kb := pow_add _ _ _
      _ ≤ a * b := Nat.mul_le_mul h1 hlb
  rcases Qb kb hdb with h2 | ⟨Sb, hSb, hSb', hSb''⟩
  · left
    calc 2 ^ (k + 1) ≤ 2 ^ (ka + (kb + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ ka * 2 ^ (kb + 1) := pow_add _ _ _
      _ ≤ a * b := Nat.mul_le_mul hla h2
  right
  have hdisj : Disjoint Sa Sb := by
    rw [Finset.disjoint_left]
    intro j hja hjb
    have h1 : fermatNumber j ∣ a := hSa' ▸ Finset.dvd_prod_of_mem _ hja
    have h2 : fermatNumber j ∣ b := hSb' ▸ Finset.dvd_prod_of_mem _ hjb
    exact fermatNumber_ne_one j (Nat.eq_one_of_dvd_coprimes hab h1 h2)
  refine ⟨Sa ∪ Sb, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact hSa j h
    · exact hSb j h
  · rw [Finset.prod_union hdisj, hSa', hSb']
  · rw [Finset.sum_union hdisj]; omega

lemma Q_all (m : ℕ) (hm : 0 < m) : Q m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact Q_prime_pow p n hp hn
  | zero => omega
  | one => exact Q_one
  | coprime a b ha hb hab Qa Qb => exact Q_mul a b ha hb hab (Qa (by omega)) (Qb (by omega))

lemma key (n m : ℕ) (hm : 0 < m) (h : 2 ^ (2 ^ n) ∣ φ m) :
    (m = fermatNumber n ∧ (fermatNumber n).Prime) ∨ 2 ^ (2 ^ n + 1) ≤ m := by
  rcases Q_all m hm (2 ^ n) h with h1 | ⟨S, hS, hS', hS''⟩
  · right; exact h1
  · by_cases hall : ∀ j ∈ S, j < n
    · exfalso
      have := Nat.geomSum_lt (le_refl 2) hall
      omega
    push_neg at hall
    obtain ⟨j, hj, hnj⟩ := hall
    have hFj_dvd : fermatNumber j ∣ m := hS' ▸ Finset.dvd_prod_of_mem _ hj
    have hm_eq : m = fermatNumber j * ∏ i ∈ S.erase j, fermatNumber i := by
      rw [hS', ← Finset.mul_prod_erase S _ hj]
    rcases Nat.lt_or_ge n j with hlt | hge
    · right
      have h1 : 2 ^ (2 ^ n + 1) ≤ 2 ^ (2 ^ j) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have h2 : 2 ^ (n + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt
        rw [pow_succ] at h2
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      have h2 : 2 ^ (2 ^ j) ≤ fermatNumber j := by unfold fermatNumber; omega
      have h3 : fermatNumber j ≤ m := Nat.le_of_dvd hm hFj_dvd
      omega
    · have hjn : j = n := by omega
      subst hjn
      by_cases hS1 : S.erase j = ∅
      · left
        rw [hm_eq, hS1, Finset.prod_empty, mul_one]
        exact ⟨rfl, hS j hj⟩
      · right
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS1
        have hi' : fermatNumber i ∣ ∏ i ∈ S.erase j, fermatNumber i :=
          Finset.dvd_prod_of_mem _ hi
        have hprodpos : 0 < ∏ i ∈ S.erase j, fermatNumber i :=
          Finset.prod_pos (fun i _ => by have := three_le_fermatNumber i; omega)
        have h3 : 3 ≤ ∏ i ∈ S.erase j, fermatNumber i :=
          (three_le_fermatNumber i).trans (Nat.le_of_dvd hprodpos hi')
        rw [hm_eq]
        have hF : fermatNumber j = 2 ^ 2 ^ j + 1 := rfl
        rw [hF]
        calc 2 ^ (2 ^ j + 1) = 2 * 2 ^ 2 ^ j := by ring
          _ ≤ (2 ^ 2 ^ j + 1) * 3 := by omega
          _ ≤ (2 ^ 2 ^ j + 1) * ∏ i ∈ S.erase j, fermatNumber i := Nat.mul_le_mul_left _ h3

theorem general (n : ℕ) :
    a (2 ^ n) = if (fermatNumber n).Prime then fermatNumber n else 2 ^ (2 ^ n + 1) := by
  unfold a
  apply IsLeast.csInf_eq
  constructor
  · split_ifs with hp
    · refine ⟨by have := three_le_fermatNumber n; omega, ?_⟩
      rw [totient_prime hp]
      unfold fermatNumber
      simp
    · refine ⟨by positivity, ?_⟩
      rw [totient_prime_pow Nat.prime_two (Nat.succ_pos _)]
      simp
  · rintro m ⟨hm, hdvd⟩
    rcases key n m hm hdvd with ⟨rfl, hp⟩ | hle
    · simp [hp]
    · split_ifs with hp
      · have : fermatNumber n ≤ 2 ^ (2 ^ n + 1) := by
          unfold fermatNumber
          rw [pow_succ]
          have := Nat.one_le_two_pow (n := 2 ^ n)
          omega
        omega
      · exact hle

end A053576

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
  exact A053576.general N_idx

theorem oeis_53576_conjecture_0.disproof : ¬ (type_of% @oeis_53576_conjecture_0) := sorry
