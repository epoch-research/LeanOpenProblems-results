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
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  have fermatNumber_eq (n : ℕ) : Nat.fermatNumber n = 2 ^ 2 ^ n + 1 := rfl
  
  open Classical in
  let g_func (p : ℕ) : ℕ := if h : ∃ i, p = fermatNumber i then Classical.choose h else 0
  
  
  have sInf_eq (S : Set ℕ) (X : ℕ) (h1 : X ∈ S) (h2 : ∀ m ∈ S, X ≤ m) :
    sInf S = X := by
    have h3 : BddBelow S := OrderBot.bddBelow S
    have h_le : sInf S ≤ X := csInf_le h3 h1
    have h_ge : X ≤ sInf S := le_csInf (Set.nonempty_of_mem h1) h2
    omega
  
  
  have m_ge_F (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (h_dvd : 2 ^ N ∣ totient m) :
    m ≥ 2 ^ N + 1 := by
    have H2 : 2 ^ N > 1 := Nat.one_lt_two_pow hN.ne'
    have Hm1 : m ≠ 1 := by
      rintro rfl
      rw [totient_one] at h_dvd
      have : 2 ^ N ≤ 1 := Nat.le_of_dvd (by decide) h_dvd
      omega
    have H3 : totient m > 0 := Nat.totient_pos.mpr hm
    have H4 : 2 ^ N ≤ totient m := Nat.le_of_dvd H3 h_dvd
    have hm2 : 1 < m := by omega
    have H5 : totient m ≤ m - 1 := le_sub_one_of_lt (totient_lt m hm2)
    omega
  
  
  have a_N_eq_F33 (N F33 : ℕ) (hN : 0 < N) (hF : F33 = 2 ^ N + 1) (h_prime : F33.Prime) :
    sInf { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } = F33 := by
    have H0 : 2 ^ N ≥ 1 := Nat.one_le_two_pow
    apply sInf_eq
    · simp only [mem_setOf_eq]
      refine ⟨by omega, ?_⟩
      have h_tot : totient F33 = F33 - 1 := (totient_eq_iff_prime (by omega)).mpr h_prime
      rw [h_tot, hF]
      have : 2 ^ N + 1 - 1 = 2 ^ N := by omega
      rw [this]
    · rintro m ⟨hm1, hm2⟩
      have H := m_ge_F N m hN hm1 hm2
      rw [hF]
      exact H
  
  
  have p_minus_one_dvd_phi {m p N : ℕ} (hp : p.Prime) (hpm : p ∣ m) (h_phi : totient m = 2 ^ N) :
    p - 1 ∣ 2 ^ N := by
    by_cases hm0 : m = 0
    · subst hm0
      rw [totient_zero] at h_phi
      have H : 2 ^ N > 0 := Nat.two_pow_pos N
      omega
    have H_phi : totient m = ∏ q ∈ m.factorization.support, q ^ (m.factorization q - 1) * (q - 1) := totient_eq_prod_factorization hm0
    have hdvd1 : p - 1 ∣ p ^ (m.factorization p - 1) * (p - 1) := dvd_mul_left _ _
    have hmem : p ∈ m.factorization.support := by
      rw [Nat.support_factorization, Nat.mem_primeFactors]
      exact ⟨hp, hpm, hm0⟩
    have hdvd2 : p ^ (m.factorization p - 1) * (p - 1) ∣ ∏ q ∈ m.factorization.support, q ^ (m.factorization q - 1) * (q - 1) := by
      exact Finset.dvd_prod_of_mem (fun q => q ^ (m.factorization q - 1) * (q - 1)) hmem
    rw [← H_phi, h_phi] at hdvd2
    exact dvd_trans hdvd1 hdvd2
  
  
  have eq_two_pow_of_dvd {i m : ℕ} (h : i ∣ 2 ^ m) : ∃ k ≤ m, i = 2 ^ k := (dvd_prime_pow prime_two).mp h
  
  
  have p_minus_one_eq_two_pow {m p N : ℕ} (hp : p.Prime) (hpm : p ∣ m) (h_phi : totient m = 2 ^ N) :
    ∃ k ≤ N, p - 1 = 2 ^ k := eq_two_pow_of_dvd (p_minus_one_dvd_phi hp hpm h_phi)
  
  
  have prime_pow_add_one {a : ℕ} (ha : a ≠ 0) (h : Nat.Prime (2 ^ a + 1)) : ∃ k, a = 2 ^ k := by
    exact pow_of_pow_add_prime Nat.one_lt_two ha h
  
  
  have Fermat_prime_form {m p N : ℕ} (hp : p.Prime) (hpm : p ∣ m) (h_phi : totient m = 2 ^ N) (hp_odd : p ≠ 2) :
    ∃ k, p = 2 ^ (2 ^ k) + 1 := by
    obtain ⟨a, _, ha2⟩ := p_minus_one_eq_two_pow hp hpm h_phi
    have ha_pos : a ≠ 0 := by
      rintro rfl
      rw [pow_zero] at ha2
      have : p = 2 := by omega
      exact hp_odd this
    have hp_eq : p = 2 ^ a + 1 := by { have : p ≥ 2 := hp.two_le; omega }
    have h_prime : Nat.Prime (2 ^ a + 1) := by
      rw [← hp_eq]
      exact hp
    obtain ⟨k, hk⟩ := prime_pow_add_one ha_pos h_prime
    use k
    rw [hk] at hp_eq
    exact hp_eq
  
  
  have H5_abstract (M : ℕ) (h1 : 1 ≤ M) : M + 1 - 2 = M - 1 := by
    omega
  
  
  have k_le_prod_F_gen (N : ℕ) (P : Finset ℕ) (g : ℕ → ℕ)
    (h_inj : Set.InjOn g P)
    (h_img : ∀ p ∈ P, g p < N)
    (h_eq : ∀ p ∈ P, p = fermatNumber (g p)) :
    ∏ p ∈ P, p ≤ 2 ^ (2 ^ N) - 1 := by
    let S := P.image g
    have H1 : ∏ p ∈ P, p = ∏ i ∈ S, fermatNumber i := by
      rw [Finset.prod_image]
      · apply Finset.prod_congr rfl
        intro p hp
        exact h_eq p hp
      · intro p hp q hq hpq
        exact h_inj hp hq hpq
    have H2 : S ⊆ Finset.range N := by
      intro i hi
      rw [Finset.mem_image] at hi
      rcases hi with ⟨p, hp, rfl⟩
      rw [Finset.mem_range]
      exact h_img p hp
    have H3 : ∏ i ∈ S, fermatNumber i ≤ ∏ i ∈ Finset.range N, fermatNumber i := by
      apply Finset.prod_le_prod_of_subset_of_one_le' H2
      intro i _ _
      have : 3 ≤ fermatNumber i := three_le_fermatNumber i
      exact le_trans (by decide) this
    have H4 : ∏ i ∈ Finset.range N, fermatNumber i = fermatNumber N - 2 := prod_fermatNumber N
    have H5 : fermatNumber N - 2 = 2 ^ (2 ^ N) - 1 := by
      rw [fermatNumber_eq]
      exact H5_abstract (2 ^ (2 ^ N)) Nat.one_le_two_pow
    rw [H4, H5] at H3
    rw [H1]
    exact H3
  
  
  have coprime_two_pow_odd {c k : ℕ} (hk : Odd k) : Coprime (2 ^ c) k := by
    have H : ¬ 2 ∣ k := hk.not_two_dvd_nat
    have H2 : Coprime 2 k := (Nat.Prime.coprime_iff_not_dvd prime_two).mpr H
    exact Coprime.pow_left c H2
  
  
  have m_ge_two_pow_M_plus_one (M m c k : ℕ)
    (h_phi : totient m = 2 ^ M)
    (hm : m = 2 ^ c * k)
    (hk_odd : Odd k)
    (hk_le : k ≤ 2 ^ M - 1)
    (hM : 0 < M) :
    m ≥ 2 ^ (M + 1) := by
    have hk_phi : totient (2 ^ c * k) = totient (2 ^ c) * totient k := by
      exact totient_mul (coprime_two_pow_odd hk_odd)
    rw [← hm, h_phi] at hk_phi
    by_cases hk1 : k = 1
    · subst hk1
      rw [totient_one, mul_one] at hk_phi
      by_cases hc0 : c = 0
      · subst hc0
        rw [pow_zero, totient_one] at hk_phi
        have H1 : 2 ^ M = 1 := hk_phi
        have H2 : 2 ^ M > 1 := Nat.one_lt_two_pow hM.ne'
        clear hk_phi hm h_phi
        omega
      · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
        have h_tot : totient (2 ^ c) = 2 ^ (c - 1) := by
          have H1 : totient (2 ^ c) = 2 ^ (c - 1) * (2 - 1) := totient_prime_pow prime_two hc_pos
          rw [H1]
          ring
        rw [h_tot] at hk_phi
        have Hc : c - 1 = M := by
          have H_pow : 2 ^ (c - 1) = 2 ^ M := hk_phi.symm
          exact Nat.pow_right_injective (by decide) H_pow
        have Hc2 : c = M + 1 := by
          clear hk_phi hm h_phi
          have : c - 1 + 1 = M + 1 := by omega
          rw [Nat.sub_add_cancel hc_pos] at this
          exact this
        subst Hc2
        rw [hm, mul_one]
    · have hk_pos : 0 < k := by
        by_cases h0 : k = 0
        · subst h0
          have H_dvd : 2 ∣ 0 := dvd_zero 2
          exact False.elim (hk_odd.not_two_dvd_nat H_dvd)
        · omega
      have hk_gt1 : 1 < k := by omega
      have hk_phi_le : totient k ≤ k - 1 := le_sub_one_of_lt (totient_lt k hk_gt1)
      have hk_phi_pos : 0 < totient k := Nat.totient_pos.mpr (by omega)
      have H_c_pos : 0 < c := by
        by_cases hc0 : c = 0
        · subst hc0
          rw [pow_zero, totient_one, one_mul] at hk_phi
          have h_M_ge_2 : 2 ^ M ≥ 2 := Nat.one_lt_two_pow hM.ne'
          have H_ineq : 2 ^ M ≤ 2 ^ M - 2 := by
            calc
              2 ^ M = totient k := hk_phi
              _ ≤ k - 1 := hk_phi_le
              _ ≤ 2 ^ M - 2 := by omega
          clear hk_phi hm h_phi
          omega
        · omega
      have h_tot : totient (2 ^ c) = 2 ^ (c - 1) := by
        have H1 : totient (2 ^ c) = 2 ^ (c - 1) * (2 - 1) := totient_prime_pow prime_two H_c_pos
        rw [H1]
        ring
      rw [h_tot] at hk_phi
      have H_eq : m * totient k = 2 ^ (M + 1) * k := by
        calc
          m * totient k = (2 ^ c * k) * totient k := by rw [hm]
          _ = 2 ^ c * (k * totient k) := by ring
          _ = (2 ^ (c - 1) * 2) * (totient k * k) := by
            have : 2 ^ c = 2 ^ (c - 1) * 2 := by
              have h0 : c - 1 + 1 = c := Nat.sub_add_cancel H_c_pos
              nth_rw 1 [← h0]
              rw [pow_add, pow_one]
            rw [this]
            ring
          _ = 2 * (2 ^ (c - 1) * totient k) * k := by ring
          _ = 2 * 2 ^ M * k := by
            have : 2 ^ (c - 1) * totient k = 2 ^ M := hk_phi.symm
            rw [this]
          _ = 2 ^ (M + 1) * k := by
            have : 2 * 2 ^ M = 2 ^ (M + 1) := by rw [pow_succ, mul_comm]
            rw [this]
      have H_ineq : 2 ^ (M + 1) * totient k < 2 ^ (M + 1) * k := by
        exact Nat.mul_lt_mul_of_pos_left (totient_lt k hk_gt1) (Nat.two_pow_pos (M + 1))
      have H_ineq2 : 2 ^ (M + 1) * totient k < m * totient k := by
        exact H_eq.symm ▸ H_ineq
      have H_ineq3 : 2 ^ (M + 1) < m := by
        exact Nat.lt_of_mul_lt_mul_right H_ineq2
      clear hk_phi hm h_phi
      omega
  
  
  have H_F34_gen (N M k : ℕ) (hN : N = 2 ^ k) (hM : M = k + 1) : 2 ^ (N + 1) ≤ fermatNumber M := by
    rw [fermatNumber_eq]
    rw [hN, hM]
    have H_pow : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
    rw [H_pow]
    have H_ineq : 2 ^ k + 1 ≤ 2 ^ k * 2 := by
      have : 2 ^ k ≥ 1 := Nat.one_le_two_pow
      omega
    have H_ineq2 := Nat.pow_le_pow_right (n := 2) (by decide) H_ineq
    omega
  
  
  have odd_phi_two_pow_squarefree (k M : ℕ) (hk : Odd k) (hk0 : 0 < k) (h_phi : totient k = 2 ^ M) :
    k = ∏ p ∈ k.factorization.support, p := by
    have H_phi : totient k = ∏ p ∈ k.factorization.support, p ^ (k.factorization p - 1) * (p - 1) := totient_eq_prod_factorization (Nat.ne_of_gt hk0)
    have H_eq : ∀ p ∈ k.factorization.support, k.factorization p = 1 := by
      intro p hp
      have hp_mem := hp
      rw [Finsupp.mem_support_iff] at hp
      have he : 0 < k.factorization p := zero_lt_iff.mpr hp
      by_cases he1 : k.factorization p = 1
      · exact he1
      · have he2 : 1 < k.factorization p := by omega
        have hdvd1 : p ∣ p ^ (k.factorization p - 1) * (p - 1) := by
          apply dvd_mul_of_dvd_left
          exact dvd_pow_self p (by omega)
        have hdvd2 : p ^ (k.factorization p - 1) * (p - 1) ∣ ∏ q ∈ k.factorization.support, (q ^ (k.factorization q - 1) * (q - 1)) := by
          exact Finset.dvd_prod_of_mem (fun q => q ^ (k.factorization q - 1) * (q - 1)) hp_mem
        have hdvd3 : p ∣ totient k := by
          rw [H_phi]
          exact dvd_trans hdvd1 hdvd2
        rw [h_phi] at hdvd3
        have hp3 : p = 2 := by
          have h_prime : p.Prime := by
            have hp_mem2 := hp_mem
            rw [Nat.support_factorization, Nat.mem_primeFactors] at hp_mem2
            exact hp_mem2.1
          exact (prime_dvd_prime_iff_eq h_prime prime_two).mp (h_prime.dvd_of_dvd_pow hdvd3)
        have H2 : 2 ∣ k := by
          have : p ∣ k := by
            have hp_mem3 := hp_mem
            rw [Nat.support_factorization, Nat.mem_primeFactors] at hp_mem3
            exact hp_mem3.2.1
          rwa [hp3] at this
        have H3 : ¬ 2 ∣ k := hk.not_two_dvd_nat
        contradiction
    have H_k : k = ∏ p ∈ k.factorization.support, p ^ (k.factorization p) := by
      exact (Nat.factorization_prod_pow_eq_self hk0.ne').symm
    calc
      k = ∏ p ∈ k.factorization.support, p ^ (k.factorization p) := H_k
      _ = ∏ p ∈ k.factorization.support, p ^ 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [H_eq p hp]
      _ = ∏ p ∈ k.factorization.support, p := by
        apply Finset.prod_congr rfl
        intro p _
        rw [pow_one]
  
  
  have p_eq_fermat (p : ℕ) (hk : ∃ i, p = 2 ^ (2 ^ i) + 1) : ∃ i, p = fermatNumber i := by
    obtain ⟨i, hi⟩ := hk
    use i
    exact hi
  
  
  have fermat_prime_of_dvd_k (k N m : ℕ) (hk : Odd k)
    (h_dvd : k ∣ m) (h_phi_m : totient m = 2 ^ N) (p : ℕ) (hp : p ∈ k.factorization.support) :
    ∃ i, p = fermatNumber i := by
    have hp_prime : p.Prime := by
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact hp.1
    have hp_dvd : p ∣ m := by
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact dvd_trans hp.2.1 h_dvd
    have hp_odd : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ k := by
        rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
        exact hp.2.1
      exact hk.not_two_dvd_nat this
    have hk_F := Fermat_prime_form hp_prime hp_dvd h_phi_m hp_odd
    exact p_eq_fermat p hk_F
  
  
  have g_func_eq (p : ℕ) (h : ∃ i, p = fermatNumber i) : p = fermatNumber (g_func p) := by
    unfold g_func
    rw [dif_pos h]
    exact Classical.choose_spec h
  
  
  have g_func_inj (P : Finset ℕ) (H : ∀ p ∈ P, ∃ i, p = fermatNumber i) :
    Set.InjOn g_func P := by
    intro p hp q hq hpq
    have hp2 := g_func_eq p (H p hp)
    have hq2 := g_func_eq q (H q hq)
    rw [hpq] at hp2
    exact hp2.trans hq2.symm
  
  
  have Fermat_prime_form_bound (N p m k : ℕ) (hN : N = 2 ^ 33)
    (hm_lt : m < 2 ^ (N + 1))
    (hp : p.Prime)
    (hpm : p ∣ m)
    (h_phi : totient m = 2 ^ N)
    (hF33_not_prime : ¬ (fermatNumber 33).Prime)
    (hk_eq : p = fermatNumber k) :
    k < 33 := by
    by_cases h33 : k = 33
    · subst h33
      have : p.Prime := hp
      rw [hk_eq] at this
      exact False.elim (hF33_not_prime this)
    · by_cases h_lt : k < 33
      · exact h_lt
      · have h_gt : 34 ≤ k := by omega
        have hp_ge : fermatNumber 34 ≤ p := by
          rw [hk_eq]
          apply fermatNumber_mono
          omega
        have hm_pos : 0 < m := by
          by_cases h : m = 0
          · subst h
            rw [totient_zero] at h_phi
            have : 2 ^ N = 0 := h_phi.symm
            omega
          · omega
        have hm_ge : fermatNumber 34 ≤ m := by
          exact le_trans hp_ge (Nat.le_of_dvd hm_pos hpm)
        have H_N : 2 ^ (N + 1) ≤ fermatNumber 34 := by
          exact H_F34_gen N 34 33 hN rfl
        have h_contra : fermatNumber 34 < fermatNumber 34 := by
          exact lt_of_lt_of_le (lt_of_le_of_lt hm_ge hm_lt) H_N
        exact False.elim (Nat.lt_irrefl _ h_contra)
  
  
  have totient_eq_two_pow (N m : ℕ) (hm : m < 2 ^ (N + 1)) (hm0 : 0 < m) (h_dvd : 2 ^ N ∣ totient m) :
    totient m = 2 ^ N := by
    have H2 : 2 ^ N > 0 := Nat.two_pow_pos N
    have H3 : totient m > 0 := Nat.totient_pos.mpr hm0
    have H4 : 2 ^ N ≤ totient m := Nat.le_of_dvd H3 h_dvd
    have H5 : totient m < 2 ^ (N + 1) := by
      by_cases h1 : 1 < m
      · have h_lt : totient m < m := totient_lt m h1
        omega
      · have H1 : m = 1 := by omega
        subst H1
        rw [totient_one]
        omega
    obtain ⟨k, hk⟩ := h_dvd
    rw [hk] at H4 H5 ⊢
    have hk_pos : 0 < k := by
      contrapose! H3
      have : k = 0 := by omega
      subst this
      rw [hk, mul_zero]
    have hk_lt2 : k < 2 := by
      rw [pow_succ] at H5
      exact (Nat.mul_lt_mul_left H2).mp H5
    have : k = 1 := by omega
    subst this
    rw [mul_one]
  
  
  have a_N_eq_two_pow_succ (N F33 : ℕ) (hN_idx : N = 2 ^ 33) (hF : F33 = 2 ^ N + 1) (h_not_prime : ¬ F33.Prime) :
    sInf { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } = 2 ^ (N + 1) := by
    have H0 : 2 ^ N ≥ 1 := Nat.one_le_two_pow
    apply sInf_eq
    · simp only [mem_setOf_eq]
      refine ⟨by positivity, ?_⟩
      have : totient (2 ^ (N + 1)) = 2 ^ N * (2 - 1) := totient_prime_pow prime_two (Nat.succ_pos N)
      rw [this]
      have h_sub : 2 - 1 = 1 := rfl
      rw [h_sub, mul_one]
    · rintro m ⟨hm1, hm2⟩
      by_cases hm_lt : m < 2 ^ (N + 1)
      · have h_phi : totient m = 2 ^ N := totient_eq_two_pow N m hm_lt hm1 hm2
        obtain ⟨c, k, hk_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hm1)
        have hk0 : 0 < k := by
          by_cases h : k = 0
          · subst h
            rw [mul_zero] at hm_eq
            exact False.elim (Nat.ne_of_gt hm1 hm_eq)
          · exact Nat.pos_of_ne_zero h
        have hk_phi : totient (2 ^ c * k) = totient (2 ^ c) * totient k := totient_mul (coprime_two_pow_odd hk_odd)
        have h_phi_k_dvd : totient k ∣ 2 ^ N := by
          have H_tot : totient m = totient (2 ^ c) * totient k := by
            rw [hm_eq]
            exact hk_phi
          rw [h_phi] at H_tot
          exact Dvd.intro (totient (2 ^ c)) (by rw [H_tot, mul_comm])
        have h_phi_k_pow : ∃ M ≤ N, totient k = 2 ^ M := eq_two_pow_of_dvd h_phi_k_dvd
        obtain ⟨M, hM_le, h_phi_k⟩ := h_phi_k_pow
        have hk_sqfree : k = ∏ p ∈ k.factorization.support, p := odd_phi_two_pow_squarefree k M hk_odd hk0 h_phi_k
        have hk_factors_F : ∀ p ∈ k.factorization.support, ∃ i, p = fermatNumber i := by
          intro p hp
          exact fermat_prime_of_dvd_k k N m hk_odd (Dvd.intro_left (2 ^ c) hm_eq.symm) h_phi p hp
        have H_inj := g_func_inj k.factorization.support hk_factors_F
        have H_img : ∀ p ∈ k.factorization.support, g_func p < 33 := by
          intro p hp
          have hp_eq : p = fermatNumber (g_func p) := g_func_eq p (hk_factors_F p hp)
          have hp_prime : p.Prime := by
            rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
            exact hp.1
          have hp_dvd_m : p ∣ m := by
            rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
            exact dvd_trans hp.2.1 (Dvd.intro_left (2 ^ c) hm_eq.symm)
          have hp_odd2 : p ≠ 2 := by
            rintro rfl
            have : 2 ∣ k := by
              rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
              exact hp.2.1
            exact hk_odd.not_two_dvd_nat this
          have h_not_prime2 : ¬ (fermatNumber 33).Prime := by
            have H_F33 : F33 = fermatNumber 33 := by
              rw [hF, hN_idx]
              rw [← fermatNumber_eq 33]
            rw [← H_F33]
            exact h_not_prime
          exact Fermat_prime_form_bound N p m (g_func p) hN_idx hm_lt hp_prime hp_dvd_m h_phi h_not_prime2 hp_eq
        have H_eq2 : ∀ p ∈ k.factorization.support, p = fermatNumber (g_func p) := by
          intro p hp
          exact g_func_eq p (hk_factors_F p hp)
        have H_prod_le : ∏ p ∈ k.factorization.support, p ≤ 2 ^ (2 ^ 33) - 1 := k_le_prod_F_gen 33 k.factorization.support g_func H_inj H_img H_eq2
        have hk_le_bound : k ≤ 2 ^ N - 1 := by
          calc
            k = ∏ p ∈ k.factorization.support, p := hk_sqfree
            _ ≤ 2 ^ (2 ^ 33) - 1 := H_prod_le
            _ = 2 ^ N - 1 := by rw [hN_idx]
        have hN_pos : 0 < N := by
          rw [hN_idx]
          exact Nat.two_pow_pos 33
        have H_m_ge : m ≥ 2 ^ (N + 1) := m_ge_two_pow_M_plus_one N m c k h_phi hm_eq hk_odd hk_le_bound hN_pos
        exact False.elim (not_le_of_gt hm_lt H_m_ge)
      · exact Nat.ge_of_not_lt hm_lt

  intro N_idx N F33
  have hN_idx_eq : N_idx = 33 := rfl
  have hN : N = 2 ^ 33 := by
    change 2 ^ N_idx = 2 ^ 33
    rw [hN_idx_eq]
  have hF : F33 = 2 ^ N + 1 := by
    change Nat.fermatNumber N_idx = 2 ^ N + 1
    rw [hN_idx_eq]
    exact Eq.trans (fermatNumber_eq 33) (congrArg (fun x => 2 ^ x + 1) hN.symm)
  have hN_pos : 0 < N := by
    rw [hN]
    exact Nat.two_pow_pos 33
  rw [a]
  split_ifs with h_prime
  · exact a_N_eq_F33 N F33 hN_pos hF h_prime
  · exact a_N_eq_two_pow_succ N F33 hN hF h_prime

theorem oeis_53576_conjecture_0.disproof : ¬ (type_of% @oeis_53576_conjecture_0) := sorry

