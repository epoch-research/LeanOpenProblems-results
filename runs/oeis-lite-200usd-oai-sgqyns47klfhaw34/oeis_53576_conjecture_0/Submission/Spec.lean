import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

namespace OEIS53576

open Finset


lemma padicValNat_two_prod {α : Type*} (s : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat 2 (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat 2 (f x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction s using Finset.induction_on with
  | empty => simp [padicValNat.one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [padicValNat.mul]
      · have ih' := ih (by intro x hx; exact hf x (Finset.mem_insert_of_mem hx))
        rw [ih']
      · exact hf a (Finset.mem_insert_self a s)
      · exact Finset.prod_ne_zero_iff.mpr (by intro x hx; exact hf x (Finset.mem_insert_of_mem hx))

lemma sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hpos : 0 < 2 ^ n := by positivity
      rw [pow_succ]
      omega

lemma pow_two_dvd_totient_iff_ge {n t : ℕ} : 2 ^ n ∣ 2 ^ t ↔ n ≤ t := by
  exact pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)

lemma totient_two_pow_succ (n : ℕ) : Nat.totient (2 ^ (n + 1)) = 2 ^ n := by
  simpa using (Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos n))

lemma fermatNumber_sub_one (i : ℕ) : Nat.fermatNumber i - 1 = 2 ^ (2 ^ i) := by
  simp [Nat.fermatNumber]

lemma totient_fermatNumber_of_prime {i : ℕ} (h : (Nat.fermatNumber i).Prime) :
    Nat.totient (Nat.fermatNumber i) = 2 ^ (2 ^ i) := by
  rw [Nat.totient_prime h, fermatNumber_sub_one]

lemma mem_set_two_pow_succ (n : ℕ) :
    2 ^ (n + 1) ∈ { m : ℕ | m > 0 ∧ 2 ^ n ∣ Nat.totient m } := by
  constructor
  · positivity
  · rw [totient_two_pow_succ]

lemma mem_set_fermat_of_prime {i : ℕ} (h : (Nat.fermatNumber i).Prime) :
    Nat.fermatNumber i ∈ { m : ℕ | m > 0 ∧ 2 ^ (2 ^ i) ∣ Nat.totient m } := by
  constructor
  · exact h.pos
  · rw [totient_fermatNumber_of_prime h]

lemma a_eq_of_le_of_mem {n b : ℕ}
    (hb : b ∈ { m : ℕ | m > 0 ∧ 2 ^ n ∣ Nat.totient m })
    (hmin : ∀ m ∈ { m : ℕ | m > 0 ∧ 2 ^ n ∣ Nat.totient m }, b ≤ m) :
    a n = b := by
  apply le_antisymm
  · exact Nat.sInf_le hb
  · exact le_csInf ⟨b, hb⟩ hmin

lemma prime_branch_min {i : ℕ} (hF : (Nat.fermatNumber i).Prime) :
    a (2 ^ i) = Nat.fermatNumber i := by
  refine a_eq_of_le_of_mem (mem_set_fermat_of_prime hF) ?_
  intro m hm
  by_contra hlt
  have hmpos : 0 < m := hm.1
  have hdvd : 2 ^ (2 ^ i) ∣ Nat.totient m := hm.2
  have hφpos : 0 < Nat.totient m := Nat.totient_pos.mpr hmpos
  have hφge : 2 ^ (2 ^ i) ≤ Nat.totient m := Nat.le_of_dvd hφpos hdvd
  have hmle : m ≤ 2 ^ (2 ^ i) := by
    have : m < 2 ^ (2 ^ i) + 1 := by
      simpa [Nat.fermatNumber] using hlt
    exact Nat.le_of_lt_succ this
  have hm_ne1 : m ≠ 1 := by
    intro h1
    subst m
    simp at hdvd
  have hmgt1 : 1 < m := by omega
  have hφlt : Nat.totient m < m := Nat.totient_lt m hmgt1
  omega

lemma dvd_pow_two_eq_pow_two {d n : ℕ} (hd : d ∣ 2 ^ n) : ∃ k ≤ n, d = 2 ^ k := by
  exact (Nat.dvd_prime_pow Nat.prime_two).mp hd

lemma odd_prime_factor_is_fermat {m n p : ℕ}
    (hφ : Nat.totient m = 2 ^ n) (hp : p.Prime) (hpm : p ∣ m) (hpne : p ≠ 2) :
    ∃ j : ℕ, p = Nat.fermatNumber j ∧ 2 ^ j ≤ n := by
  have hdvdφ : p - 1 ∣ Nat.totient m := by
    simpa [Nat.totient_prime hp] using (Nat.totient_dvd_of_dvd (a := p) (b := m) hpm)
  have hdvd : p - 1 ∣ 2 ^ n := by simpa [hφ] using hdvdφ
  obtain ⟨r, hrle, hr⟩ := dvd_pow_two_eq_pow_two hdvd
  have hrpos : r ≠ 0 := by
    intro hz
    subst r
    simp at hr
    have hp_eq_two : p = 2 := by omega
    exact hpne hp_eq_two
  have hp_eq : p = 2 ^ r + 1 := by
    have hpos : 0 < p := hp.pos
    omega
  have hprime : (2 ^ r + 1).Prime := by simpa [← hp_eq] using hp
  obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (a := 2) (n := r) (by norm_num) hrpos hprime
  refine ⟨j, ?_, ?_⟩
  · rw [hp_eq, Nat.fermatNumber, hj]
  · rw [hj] at hrle
    exact hrle

lemma fermat_index_le_of_factor_lt {j n : ℕ}
    (hj : 2 ^ j ≤ n) (hn : n = 2 ^ 33) : j ≤ 33 := by
  subst n
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hj

lemma odd_power_two_totient_forces_F33 {N m : ℕ} (hN : N = 2 ^ (33 : ℕ))
    (hmodd : Odd m) (hφ : Nat.totient m = 2 ^ N)
    (_hlt : m < 2 ^ (N + 1)) :
    (Nat.fermatNumber 33).Prime := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let s := m.primeFactors
  have hm0 : m ≠ 0 := (Odd.pos hmodd).ne'
  have H (p : ℕ) (hpS : p ∈ s) : ∃ j : ℕ, p = Nat.fermatNumber j ∧ 2 ^ j ≤ N := by
    have hpdata := Nat.mem_primeFactors.mp hpS
    have hpne : p ≠ 2 := by
      intro hp2
      exact hmodd.not_two_dvd_nat (hp2 ▸ hpdata.2.1)
    exact odd_prime_factor_is_fermat hφ hpdata.1 hpdata.2.1 hpne
  let idx : ℕ → ℕ := fun p => if hp : p ∈ s then Classical.choose (H p hp) else 0
  have idx_spec {p : ℕ} (hpS : p ∈ s) :
      p = Nat.fermatNumber (idx p) ∧ 2 ^ idx p ≤ N := by
    dsimp [idx]
    rw [dif_pos hpS]
    exact Classical.choose_spec (H p hpS)
  let f : ℕ → ℕ := fun p => p ^ (m.factorization p - 1) * (p - 1)
  have hprodφ : Nat.totient m = ∏ p ∈ s, f p := by
    dsimp [s, f]
    rw [Nat.totient_eq_prod_factorization hm0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hf_ne {p : ℕ} (hpS : p ∈ s) : f p ≠ 0 := by
    dsimp [f]
    have hpdata := Nat.mem_primeFactors.mp hpS
    exact mul_ne_zero (pow_ne_zero _ hpdata.1.ne_zero) (Nat.sub_ne_zero_of_lt hpdata.1.one_lt)
  have hval_term {p : ℕ} (hpS : p ∈ s) :
      padicValNat 2 (f p) = 2 ^ idx p := by
    dsimp [f]
    have hpdata := Nat.mem_primeFactors.mp hpS
    have hpne : p ≠ 2 := by
      intro hp2
      exact hmodd.not_two_dvd_nat (hp2 ▸ hpdata.2.1)
    have hnot2p : ¬ 2 ∣ p := by
      intro h2p
      have h2eqp : 2 = p := ((Nat.dvd_prime hpdata.1).mp h2p).resolve_left (by norm_num)
      exact hpne h2eqp.symm
    have hnot2pow : ¬ 2 ∣ p ^ (m.factorization p - 1) := by
      intro hdiv
      exact hnot2p (Nat.prime_two.dvd_of_dvd_pow hdiv)
    have hpow_ne : p ^ (m.factorization p - 1) ≠ 0 := pow_ne_zero _ hpdata.1.ne_zero
    have hsub_ne : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hpdata.1.one_lt
    rw [padicValNat.mul hpow_ne hsub_ne]
    rw [padicValNat.eq_zero_of_not_dvd hnot2pow]
    have hpminus : p - 1 = 2 ^ (2 ^ idx p) := by
      calc
        p - 1 = Nat.fermatNumber (idx p) - 1 := congrArg (fun x : ℕ => x - 1) (idx_spec hpS).1
        _ = 2 ^ (2 ^ idx p) := fermatNumber_sub_one (idx p)
    rw [hpminus, padicValNat.prime_pow]
    simp
  have hvalφ : padicValNat 2 (Nat.totient m) = N := by
    rw [hφ, padicValNat.prime_pow]
  have hvalprod : padicValNat 2 (∏ p ∈ s, f p) = ∑ p ∈ s, padicValNat 2 (f p) := by
    exact padicValNat_two_prod s f (by intro p hp; exact hf_ne hp)
  rw [hprodφ, hvalprod] at hvalφ
  have hsum_eq : ∑ p ∈ s, 2 ^ idx p = N := by
    rw [← hvalφ]
    apply Finset.sum_congr rfl
    intro p hpS
    exact (hval_term hpS).symm
  by_contra hF33
  have hno33 {p : ℕ} (hpS : p ∈ s) : idx p ≠ 33 := by
    intro hpidx
    have hpprime := (Nat.mem_primeFactors.mp hpS).1
    have hpeq := (idx_spec hpS).1
    rw [hpidx] at hpeq
    exact hF33 (hpeq ▸ hpprime)
  have hidxlt {p : ℕ} (hpS : p ∈ s) : idx p < 33 := by
    have hle := (idx_spec hpS).2
    rw [hN] at hle
    have hle' : idx p ≤ 33 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    exact lt_of_le_of_ne hle' (hno33 hpS)
  have hinj : Set.InjOn idx (↑s : Set ℕ) := by
    intro p hp q hq heq
    have hp' := idx_spec hp
    have hq' := idx_spec hq
    calc
      p = Nat.fermatNumber (idx p) := hp'.1
      _ = Nat.fermatNumber (idx q) := by rw [heq]
      _ = q := hq'.1.symm
  have himage_sum : ∑ p ∈ s, 2 ^ idx p = ∑ j ∈ s.image idx, 2 ^ j := by
    exact (Finset.sum_image (s := s) (g := idx) (f := fun j => 2 ^ j) hinj).symm
  have hsubset : s.image idx ⊆ Finset.range 33 := by
    rw [Finset.image_subset_iff]
    intro p hpS
    exact Finset.mem_range.mpr (hidxlt hpS)
  have hle_image : ∑ j ∈ s.image idx, 2 ^ j ≤ ∑ j ∈ Finset.range 33, 2 ^ j := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro j hj hjnot; positivity)
  have hsum_le : ∑ p ∈ s, 2 ^ idx p ≤ 2 ^ (33 : ℕ) - 1 := by
    rw [himage_sum]
    exact hle_image.trans_eq (sum_range_two_pow 33)
  rw [hsum_eq, hN] at hsum_le
  omega

lemma even_totient_le_half {m : ℕ} (hm : Even m) : 2 * Nat.totient m ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases hm with ⟨k, rfl⟩
    rw [← two_mul k]

    by_cases hk0 : k = 0
    · subst k
      simp
    by_cases hke : Even k
    · have hklt : k < k + k := by nlinarith [Nat.pos_of_ne_zero hk0]
      have hrec : 2 * Nat.totient k ≤ k := ih k hklt hke
      rw [Nat.totient_two_mul_of_even hke]
      nlinarith
    · have hko : Odd k := Nat.not_even_iff_odd.mp hke
      rw [Nat.totient_two_mul_of_odd hko]
      have hle : Nat.totient k ≤ k := Nat.totient_le k
      nlinarith

lemma composite_branch_min_aux {N : ℕ} (hN : N = 2 ^ (33 : ℕ))
    (hF : ¬ (Nat.fermatNumber 33).Prime) :
    a N = 2 ^ (N + 1) := by
  refine a_eq_of_le_of_mem (mem_set_two_pow_succ N) ?_
  intro m hm
  by_contra hnotle
  have hlt : m < 2 ^ (N + 1) := Nat.lt_of_not_ge hnotle
  have hmpos : 0 < m := hm.1
  have hdvd : 2 ^ N ∣ Nat.totient m := hm.2
  have hφpos : 0 < Nat.totient m := Nat.totient_pos.mpr hmpos
  have hφge : 2 ^ N ≤ Nat.totient m := Nat.le_of_dvd hφpos hdvd
  have hm_ne1 : m ≠ 1 := by
    intro h1
    subst m
    simp at hdvd
    have hNpos : 0 < N := by
      rw [hN]
      positivity
    omega
  have hmgt1 : 1 < m := by omega
  have hφltm : Nat.totient m < m := Nat.totient_lt m hmgt1
  have hφlt : Nat.totient m < 2 ^ (N + 1) := lt_trans hφltm hlt
  have hφ_eq : Nat.totient m = 2 ^ N := by
    obtain ⟨k, hk⟩ := hdvd
    have hkpos : 0 < k := by
      by_contra hk0
      have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hk0', mul_zero] at hk
      omega
    have hklt : k < 2 := by
      rw [hk] at hφlt
      have : k * 2 ^ N < 2 * 2 ^ N := by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hφlt
      exact (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ N)).mp (by simpa [mul_comm] using this)
    have : k = 1 := by omega
    subst k
    simpa [mul_comm] using hk
  by_cases heven : Even m
  · have hhalf := even_totient_le_half heven
    rw [hφ_eq] at hhalf
    exact (not_lt_of_ge hhalf) (by simpa [mul_comm, pow_succ] using hlt)
  · have hodd : Odd m := Nat.not_even_iff_odd.mp heven
    exact hF (odd_power_two_totient_forces_F33 hN hodd hφ_eq hlt)

end OEIS53576

-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  let N : ℕ := 2 ^ (33 : ℕ)
  have hN : N = 2 ^ (33 : ℕ) := rfl
  change a N = if (Nat.fermatNumber 33).Prime then Nat.fermatNumber 33 else 2 ^ (N + 1)
  by_cases h : (Nat.fermatNumber 33).Prime
  · rw [if_pos h]
    have hp := OEIS53576.prime_branch_min h
    rw [← hN] at hp
    exact hp
  · rw [if_neg h]
    exact OEIS53576.composite_branch_min_aux hN h
