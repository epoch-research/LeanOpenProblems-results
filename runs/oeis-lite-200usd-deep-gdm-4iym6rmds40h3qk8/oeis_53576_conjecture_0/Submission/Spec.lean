import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

lemma k_add_sub_eq {k N : ℕ} (hk : k ≥ 1) (h_lt : k - 1 ≤ N) :
    k + (N - (k - 1)) = N + 1 := by
  omega

lemma even_not_mem {N_idx : ℕ} (_ : N_idx = 33) (m : ℕ)
    (hm_pos : m > 0)
    (hm_even : Even m)
    (hlt : m < 2 ^ (2 ^ N_idx + 1)) :
    m ∉ { m : ℕ | m > 0 ∧ 2 ^ (2 ^ N_idx) ∣ totient m } := by
  intro hm
  generalize h_N : 2 ^ N_idx = N at hlt hm
  simp only [mem_setOf_eq] at hm
  have h_dvd_tot : 2 ^ N ∣ totient m := hm.2
  obtain ⟨k, d, hd_odd, h_eq⟩ := exists_eq_two_pow_mul_odd (Nat.ne_of_gt hm_pos)
  have hk_pos : k ≥ 1 := by
    by_contra! hk_zero
    have : k = 0 := by omega
    have h_eq2 : m = d := by rw [h_eq, this, pow_zero, one_mul]
    have h_even_d : Even d := by rwa [← h_eq2]
    exact (Nat.not_even_iff_odd.mpr hd_odd) h_even_d
  have h_coprime : Coprime (2 ^ k) d := hd_odd.coprime_two_right.symm.pow_left k
  have h_tot_mul : totient m = totient (2 ^ k) * totient d := by
    rw [h_eq, totient_mul h_coprime]
  have h_tot_pow : totient (2 ^ k) = 2 ^ (k - 1) := by
    have h_eq2 : k = (k - 1) + 1 := by omega
    nth_rw 1 [h_eq2]
    have := totient_prime_pow_succ prime_two (k - 1)
    norm_num at this
    exact this
  have h_tot_final : totient m = 2 ^ (k - 1) * totient d := by
    rw [h_tot_mul, h_tot_pow]
  rw [h_tot_final] at h_dvd_tot
  have hd_pos : d > 0 := by
    by_contra! hd_zero
    have : d = 0 := by omega
    subst this
    simp only [mul_zero] at h_eq
    omega
  have hd_tot_pos : totient d > 0 := totient_pos.mpr hd_pos
  by_cases hd1 : d = 1
  · rw [hd1, totient_one, mul_one] at h_dvd_tot
    have h_pow_le : 2 ^ N ≤ 2 ^ (k - 1) := by
      refine Nat.le_of_dvd ?_ h_dvd_tot
      · positivity
    have hk_le : N ≤ k - 1 := by
      exact (Nat.pow_le_pow_iff_right (by decide)).mp h_pow_le
    have hk_le2 : k ≥ N + 1 := by omega
    have hm_ge : m ≥ 2 ^ (N + 1) := by
      rw [h_eq, hd1, mul_one]
      exact (Nat.pow_le_pow_iff_right (by decide)).mpr hk_le2
    omega
  · have hd_ge3 : d ≥ 3 := by
      have : d ≠ 1 := hd1
      have : d ≠ 2 := by
        intro hc
        have : Even 2 := by decide
        have : Even d := by rw [hc]; exact this
        exact (Nat.not_even_iff_odd.mpr hd_odd) this
      omega
    have hd_tot_lt : totient d < d := totient_lt d (by omega)
    have hd_tot_le : totient d ≤ d - 1 := by omega
    have h_dvd_pow : 2 ^ (N - (k - 1)) ∣ totient d := by
      by_cases hk_lt : k - 1 ≤ N
      · have h_eq_sub : 2 ^ N = 2 ^ (N - (k - 1)) * 2 ^ (k - 1) := by
          rw [← pow_add, Nat.sub_add_cancel hk_lt]
        rw [h_eq_sub] at h_dvd_tot
        rw [mul_comm (2 ^ (k - 1)) (totient d)] at h_dvd_tot
        refine Nat.dvd_of_mul_dvd_mul_right ?_ h_dvd_tot
        · positivity
      · have hk_le2 : k ≥ N + 1 := by omega
        have hm_ge : m ≥ 2 ^ (N + 1) := by
          rw [h_eq]
          have : 2 ^ k * d ≥ 2 ^ (N + 1) * 3 := by
            refine Nat.mul_le_mul ?_ hd_ge3
            exact (Nat.pow_le_pow_iff_right (by decide)).mpr hk_le2
          omega
        omega
    have h_tot_d_ge : 2 ^ (N - (k - 1)) ≤ totient d := Nat.le_of_dvd hd_tot_pos h_dvd_pow
    by_cases hk_lt : k - 1 ≤ N
    · have hd_ge : d ≥ 2 ^ (N - (k - 1)) + 1 := by
        have : totient d ≤ d - 1 := hd_tot_le
        have : 2 ^ (N - (k - 1)) ≤ totient d := h_tot_d_ge
        omega
      have hm_ge : m ≥ 2 ^ (N + 1) := by
        have h_pow_add : k + (N - (k - 1)) = N + 1 := k_add_sub_eq hk_pos hk_lt
        have h_calc : 2 ^ k * (2 ^ (N - (k - 1)) + 1) = 2 ^ (N + 1) + 2 ^ k := by
          rw [mul_add, mul_one]
          rw [← pow_add, h_pow_add]
        have hm_ge_calc : 2 ^ k * (2 ^ (N - (k - 1)) + 1) ≤ 2 ^ k * d := Nat.mul_le_mul_left (2 ^ k) hd_ge
        rw [h_calc] at hm_ge_calc
        rw [← h_eq] at hm_ge_calc
        exact Nat.le_trans (Nat.le_add_right _ _) hm_ge_calc
      omega
    · have hk_le2 : k ≥ N + 1 := by omega
      have hm_ge : m ≥ 2 ^ (N + 1) := by
        rw [h_eq]
        have : 2 ^ k * d ≥ 2 ^ (N + 1) * 3 := by
          refine Nat.mul_le_mul ?_ hd_ge3
          exact (Nat.pow_le_pow_iff_right (by decide)).mpr hk_le2
        omega
      omega

lemma totient_pow_two_succ (n : ℕ) : totient (2 ^ (n + 1)) = 2 ^ n := by
  have := totient_prime_pow_succ prime_two n
  norm_num at this
  exact this

lemma mem_set_of_two_pow (n : ℕ) : 2 ^ (n + 1) ∈ { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m } := by
  simp only [mem_setOf_eq, gt_iff_lt]
  refine ⟨by positivity, ?_⟩
  rw [totient_pow_two_succ]

lemma a_le_two_pow_succ (n : ℕ) : a n ≤ 2 ^ (n + 1) := by
  dsimp [a]
  apply csInf_le
  · use 0; intro x hx; exact Nat.zero_le x
  · exact mem_set_of_two_pow n

lemma not_dvd_pow_sub_one {N : ℕ} (hN : N ≥ 1) : ¬ 2 ^ N ∣ 2 ^ (N - 1) := by
  intro hdvd
  have h_le : 2 ^ N ≤ 2 ^ (N - 1) := Nat.le_of_dvd (by positivity) hdvd
  have h_exp : N ≤ N - 1 := (Nat.pow_le_pow_iff_right (by decide)).mp h_le
  omega

lemma lt_two_pow_not_mem {N : ℕ} (hN : N ≥ 1) (m : ℕ) (hm_pos : m > 0) (hm_le : m ≤ 2 ^ N) :
    m ∉ { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } := by
  intro hm
  simp only [mem_setOf_eq] at hm
  have h_dvd : 2 ^ N ∣ totient m := hm.2
  rcases lt_or_eq_of_le hm_le with hlt | heq
  · have h_tot_lt : totient m < 2 ^ N := lt_of_le_of_lt (totient_le m) hlt
    have h_tot_pos : totient m > 0 := totient_pos.mpr hm_pos
    exact Nat.not_dvd_of_pos_of_lt h_tot_pos h_tot_lt h_dvd
  · subst heq
    have h_tot_eq : totient (2 ^ N) = 2 ^ (N - 1) := by
      have h_eq2 : N = (N - 1) + 1 := by omega
      nth_rw 1 [h_eq2]
      have := totient_prime_pow_succ prime_two (N - 1)
      norm_num at this
      exact this
    rw [h_tot_eq] at h_dvd
    exact not_dvd_pow_sub_one hN h_dvd

lemma sInf_eq_of_mem_of_lt_not_mem {s : Set ℕ} {x : ℕ} (hx : x ∈ s) (h_not : ∀ m < x, m ∉ s) :
    sInf s = x := by
  have h_ne : s.Nonempty := ⟨x, hx⟩
  have h_le : sInf s ≤ x := Nat.sInf_le hx
  have h_ge : x ≤ sInf s := by
    by_contra! h_lt
    have h_not_mem := h_not (sInf s) h_lt
    have h_mem := Nat.sInf_mem h_ne
    exact h_not_mem h_mem
  omega

lemma a_N_of_prime {N_idx : ℕ} (_ : N_idx = 33) {N : ℕ} (hN : N = 2 ^ N_idx)
    {F33 : ℕ} (hF33 : F33 = Nat.fermatNumber N_idx) (h_prime : F33.Prime) :
    a N = F33 := by
  dsimp [a]
  have hF33_eq : F33 = 2 ^ N + 1 := by
    rw [hF33, Nat.fermatNumber, hN]
  have hN_ge : N ≥ 1 := by
    rw [hN]
    exact Nat.one_le_pow N_idx 2 (by decide)
  have hF33_pos : F33 > 0 := by
    rw [hF33_eq]
    positivity
  have h_mem : F33 ∈ { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } := by
    simp only [mem_setOf_eq]
    refine ⟨hF33_pos, ?_⟩
    have h_tot_F33 : totient F33 = F33 - 1 := totient_prime h_prime
    rw [h_tot_F33, hF33_eq]
    simp only [add_tsub_cancel_right, dvd_refl]
  apply sInf_eq_of_mem_of_lt_not_mem h_mem
  intro m hm
  simp only [mem_setOf_eq]
  intro hm_mem
  have hm_pos : m > 0 := hm_mem.1
  have hm_le : m ≤ 2 ^ N := by omega
  exact lt_two_pow_not_mem hN_ge m hm_pos hm_le hm_mem

lemma prime_factor_form {m : ℕ} (_ : Odd m) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m)
    {N : ℕ} (h_phi : totient m = 2 ^ N) :
    ∃ j ≤ N, p = 2 ^ j + 1 := by
  have hdvd : p - 1 ∣ totient m := by
    have h1 : totient p ∣ totient m := totient_dvd_of_dvd hpm
    rw [totient_prime hp] at h1
    exact h1
  rw [h_phi] at hdvd
  have h_dvd_pow := (Nat.dvd_prime_pow prime_two).mp hdvd
  obtain ⟨j, hj_le, hj_eq⟩ := h_dvd_pow
  have hp_ge : p ≥ 1 := by
    have := hp.two_le
    omega
  have hp_eq : p = 2 ^ j + 1 := by omega
  use j, hj_le

lemma prime_factor_lt_N {N_idx : ℕ} (hm_odd : Odd m) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m)
    {N : ℕ} (hN : N = 2 ^ N_idx) {F33 : ℕ} (hF33 : F33 = Nat.fermatNumber N_idx)
    (h_phi : totient m = 2 ^ N) (h_lt : m < 2 ^ (N + 1)) (h_composite : ¬ F33.Prime) :
    ∃ j < N, p = 2 ^ j + 1 := by
  have ⟨j, hj_le, hj_eq⟩ := prime_factor_form hm_odd hp hpm h_phi
  have h_ne : j ≠ N := by
    intro hc
    subst hc
    have h_p_eq_F33 : p = F33 := by
      rw [hF33, Nat.fermatNumber, ← hN, hj_eq]
    have hp_prime_eq : F33.Prime := h_p_eq_F33 ▸ hp
    exact h_composite hp_prime_eq
  have hj_lt : j < N := lt_of_le_of_ne hj_le h_ne
  use j, hj_lt

lemma factorization_eq_one {m : ℕ} (hm_odd : Odd m) (hm_pos : m > 0) {N : ℕ} (h_phi : totient m = 2 ^ N)
    {p : ℕ} (hp : p ∈ m.primeFactors) :
    m.factorization p = 1 := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hm_factor_pos : 0 < m.factorization p := hp_prime.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
  have h_dvd_prod : p ^ (m.factorization p - 1) * (p - 1) ∣ totient m := by
    rw [totient_eq_prod_factorization (by omega)]
    have h_prod_dvd : (fun q ↦ q ^ (m.factorization q - 1) * (q - 1)) p ∣ ∏ q ∈ m.primeFactors, q ^ (m.factorization q - 1) * (q - 1) := by
      apply Finset.dvd_prod_of_mem (fun q ↦ q ^ (m.factorization q - 1) * (q - 1)) hp
    exact h_prod_dvd
  have h_dvd_tot : p ^ (m.factorization p - 1) ∣ totient m := by
    have h_dvd_mul : p ^ (m.factorization p - 1) ∣ p ^ (m.factorization p - 1) * (p - 1) := dvd_mul_right _ _
    exact dvd_trans h_dvd_mul h_dvd_prod
  rw [h_phi] at h_dvd_tot
  have h_dvd_pow := (Nat.dvd_prime_pow prime_two).mp h_dvd_tot
  obtain ⟨k, hk_le, hk_eq⟩ := h_dvd_pow
  by_cases h_exp : m.factorization p - 1 = 0
  · omega
  · have hk_pos : k > 0 := by
      by_contra! hk_zero
      have hk_eq_zero : k = 0 := by omega
      subst hk_eq_zero
      rw [pow_zero] at hk_eq
      have hp_gt_one : 1 < p := by
        have := hp_prime.two_le
        omega
      have h_exp_pos : 0 < m.factorization p - 1 := Nat.pos_of_ne_zero h_exp
      have h_one_lt : p ^ (m.factorization p - 1) > 1 := Nat.one_lt_pow h_exp_pos.ne' hp_gt_one
      omega
    have hp_dvd : p ∣ 2 ^ k := by
      rw [← hk_eq]
      refine dvd_pow_self p (by omega)
    have hp_eq_two : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime prime_two).mp (hp_prime.dvd_of_dvd_pow hp_dvd)
    subst hp_eq_two
    have h_even_m : Even m := even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    have h_contradiction : False := Nat.not_even_iff_odd.mpr hm_odd h_even_m
    cases h_contradiction

lemma totient_eq_prod_primeFactors_sub_one {m : ℕ} (hm_odd : Odd m) (hm_pos : m > 0)
    {N : ℕ} (h_phi : totient m = 2 ^ N) :
    totient m = ∏ p ∈ m.primeFactors, (p - 1) := by
  rw [totient_eq_prod_factorization (by omega)]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have h_fact := factorization_eq_one hm_odd hm_pos h_phi hp
  rw [h_fact]
  simp only [tsub_self, pow_zero, one_mul]

lemma dvd_pow_add_one (a : ℕ) {b : ℕ} (hb : Odd b) :
    2 ^ a + 1 ∣ (2 ^ a) ^ b + 1 := by
  have := Odd.nat_add_dvd_pow_add_pow hb (x := 2 ^ a) (y := 1)
  simpa only [one_pow] using this

lemma pow_two_of_prime {j : ℕ} (hj_pos : j > 0) (hp : (2 ^ j + 1).Prime) :
    ∃ k, j = 2 ^ k := by
  obtain ⟨k, b, hb_odd, h_eq⟩ := exists_eq_two_pow_mul_odd hj_pos.ne'
  use k
  by_contra! h_ne
  have hb_ge3 : b ≥ 3 := by
    have h_ne1 : b ≠ 1 := by
      intro hc
      subst hc
      rw [mul_one] at h_eq
      exact h_ne h_eq
    have h_ne0 : b ≠ 0 := by
      intro hc
      subst hc
      simp only [mul_zero] at h_eq
      omega
    have h_ne2 : b ≠ 2 := by
      intro hc
      have h_even_b : Even b := by rw [hc]; decide
      exact (Nat.not_even_iff_odd.mpr hb_odd) h_even_b
    omega
  let a := 2 ^ k
  have h_mul : j = a * b := h_eq
  have h_dvd : 2 ^ a + 1 ∣ 2 ^ j + 1 := by
    rw [h_mul, pow_mul]
    exact dvd_pow_add_one a hb_odd
  have hp_eq := hp.eq_one_or_self_of_dvd (2 ^ a + 1) h_dvd
  rcases hp_eq with h_one | h_self
  · have : 2 ^ a + 1 ≥ 3 := by
      have ha_ge1 : a ≥ 1 := by
        dsimp [a]
        exact Nat.one_le_pow k 2 (by decide)
      have : 2 ^ a ≥ 2 := by
        have : 2 ^ a ≥ 2 ^ 1 := (Nat.pow_le_pow_iff_right (by decide)).mpr ha_ge1
        omega
      omega
    omega
  · have h_exp_eq : a = j := by
      have : 2 ^ a = 2 ^ j := by omega
      exact (Nat.pow_right_injective (by decide)) this
    have h_b_eq : b = 1 := by
      have h_meq : j * b = j := by
        have : j = j * b := by
          calc
            j = a * b := h_mul
            _ = j * b := by rw [h_exp_eq]
        omega
      have := mul_right_eq_self₀.mp h_meq
      rcases this with hb1 | hj0
      · exact hb1
      · omega
    omega

lemma sum_pow_two_range (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  have h := geom_sum_mul_add (1 : ℕ) n
  change (∑ i ∈ Finset.range n, 2 ^ i) * 1 + 1 = 2 ^ n at h
  rw [mul_one] at h
  have : 2 ^ n ≥ 1 := Nat.one_le_pow n 2 (by decide)
  omega

lemma k_unique {p : ℕ} {k1 k2 : ℕ} (h1 : p - 1 = 2 ^ 2 ^ k1) (h2 : p - 1 = 2 ^ 2 ^ k2) :
    k1 = k2 := by
  have : 2 ^ 2 ^ k1 = 2 ^ 2 ^ k2 := by omega
  have : 2 ^ k1 = 2 ^ k2 := (Nat.pow_right_injective (by decide)) this
  exact (Nat.pow_right_injective (by decide)) this

lemma prime_to_k_exists {N_idx : ℕ} (_ : N_idx = 33) {m : ℕ} (hm_odd : Odd m) {N : ℕ} (hN : N = 2 ^ N_idx)
    (h_phi : totient m = 2 ^ N) {F33 : ℕ} (hF33 : F33 = Nat.fermatNumber N_idx) (h_composite : ¬ F33.Prime)
    (h_lt : m < 2 ^ (N + 1)) {p : ℕ} (hp : p ∈ m.primeFactors) :
    ∃ k < N_idx, p - 1 = 2 ^ 2 ^ k := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h_dvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  have ⟨j, hj_lt, hj_eq⟩ : ∃ j < N, p = 2 ^ j + 1 :=
    prime_factor_lt_N hm_odd hp_prime h_dvd hN hF33 h_phi h_lt h_composite
  have hj_pos : j > 0 := by
    have : p.Prime := hp_prime
    have : p ≠ 2 := by
      intro hc
      subst hc
      have : Even m := even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.not_even_iff_odd.mpr hm_odd this
    have hp_ge : p ≥ 3 := by
      have := hp_prime.two_le
      omega
    have : 2 ^ j ≥ 2 := by omega
    have : j > 0 := by
      by_contra! hj_zero
      have : j = 0 := by omega
      subst this
      simp only [pow_zero] at *
      omega
    exact this
  have ⟨k, hk_eq⟩ : ∃ k, j = 2 ^ k := pow_two_of_prime hj_pos (hj_eq ▸ hp_prime)
  have hk_lt : k < N_idx := by
    have h_pow : 2 ^ k < 2 ^ N_idx := by
      calc
        2 ^ k = j := hk_eq.symm
        _ < N := hj_lt
        _ = 2 ^ N_idx := hN
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp h_pow
  use k, hk_lt
  rw [hj_eq, hk_eq]
  simp only [add_tsub_cancel_right]

lemma a_N_of_composite {N_idx : ℕ} (h_idx : N_idx = 33) {N : ℕ} (hN : N = 2 ^ N_idx)
    {F33 : ℕ} (hF33 : F33 = Nat.fermatNumber N_idx) (h_composite : ¬ F33.Prime) :
    a N = 2 ^ (N + 1) := by
  have hN_ge : N ≥ 1 := by
    rw [hN]
    exact Nat.one_le_pow N_idx 2 (by decide)
  apply sInf_eq_of_mem_of_lt_not_mem (mem_set_of_two_pow N)
  intro m hm
  simp only [mem_setOf_eq]
  intro hm_mem
  have hm_pos : m > 0 := hm_mem.1
  have hlt : m < 2 ^ (N + 1) := hm
  have h_phi_div : 2 ^ N ∣ totient m := hm_mem.2
  have hm_even_or_odd : Even m ∨ Odd m := Nat.even_or_odd m
  rcases hm_even_or_odd with hm_even | hm_odd
  · have hlt_idx : m < 2 ^ (2 ^ N_idx + 1) := hN ▸ hlt
    have hm_mem_idx : m ∈ { m : ℕ | m > 0 ∧ 2 ^ (2 ^ N_idx) ∣ totient m } := hN ▸ hm_mem
    have h_not_mem := even_not_mem h_idx m hm_pos hm_even hlt_idx
    exact h_not_mem hm_mem_idx
  · have h_phi_eq : totient m = 2 ^ N := by
      have h_tot_pos : totient m > 0 := totient_pos.mpr hm_pos
      have h_tot_lt : totient m < 2 ^ (N + 1) := lt_of_le_of_lt (totient_le m) hlt
      have h_pow_succ : 2 ^ (N + 1) = 2 ^ N * 2 := by rw [pow_succ]
      rw [h_pow_succ] at h_tot_lt
      rcases h_phi_div with ⟨c, hc⟩
      rw [hc] at h_tot_lt h_tot_pos
      have h_pow_pos : 2 ^ N > 0 := by positivity
      have h_mul_lt : 2 ^ N * c < 2 ^ N * 2 := hc ▸ h_tot_lt
      have hc_lt : c < 2 := Nat.lt_of_mul_lt_mul_left h_mul_lt
      have hc_pos : c > 0 := by
        by_contra! hc0
        have : c = 0 := by omega
        subst this
        rw [mul_zero] at hc
        omega
      have : c = 1 := by omega
      rw [hc, this, mul_one]
    let S := m.primeFactors
    let g : ℕ → ℕ := fun p ↦
      if hp : p ∈ S then
        Classical.choose (prime_to_k_exists h_idx hm_odd hN h_phi_eq hF33 h_composite hlt hp)
      else 0
    have h_g_spec : ∀ p ∈ S, g p < N_idx ∧ p - 1 = 2 ^ 2 ^ (g p) := by
      intro p hp
      dsimp [g]
      rw [dif_pos hp]
      exact Classical.choose_spec (prime_to_k_exists h_idx hm_odd hN h_phi_eq hF33 h_composite hlt hp)
    have h_inj : ∀ p1 ∈ S, ∀ p2 ∈ S, g p1 = g p2 → p1 = p2 := by
      intro p1 hp1 p2 hp2 h_g
      have h1 := (h_g_spec p1 hp1).2
      have h2 := (h_g_spec p2 hp2).2
      rw [h_g] at h1
      have hp1_prime : p1.Prime := Nat.prime_of_mem_primeFactors hp1
      have hp2_prime : p2.Prime := Nat.prime_of_mem_primeFactors hp2
      have hp1_ge : p1 ≥ 1 := by
        have := hp1_prime.two_le
        omega
      have hp2_ge : p2 ≥ 1 := by
        have := hp2_prime.two_le
        omega
      omega
    have h_tot_eq_prod : totient m = ∏ p ∈ S, 2 ^ 2 ^ (g p) := by
      rw [totient_eq_prod_primeFactors_sub_one hm_odd hm_pos h_phi_eq]
      refine Finset.prod_congr rfl ?_
      intro p hp
      exact (h_g_spec p hp).2
    let K := S.image g
    have h_inj_on : Set.InjOn g ↑S := h_inj
    have h_prod_image : ∏ p ∈ S, (2 ^ 2 ^ (g p) : ℕ) = ∏ k ∈ K, (2 ^ 2 ^ k : ℕ) := by
      exact (@Finset.prod_image ℕ ℕ ℕ _ (fun k ↦ 2 ^ 2 ^ k) _ S g h_inj_on).symm
    have h_K_subset : K ⊆ Finset.range N_idx := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨p, hp, rfl⟩ := hk
      rw [Finset.mem_range]
      exact (h_g_spec p hp).1
    have h_prod_le : ∏ k ∈ K, (2 ^ 2 ^ k : ℕ) ≤ ∏ k ∈ Finset.range N_idx, (2 ^ 2 ^ k : ℕ) := by
      apply Finset.prod_le_prod_of_subset_of_one_le' h_K_subset
      intro k hk_range hk_not_mem
      exact Nat.one_le_pow (2 ^ k) 2 (by decide)
    have h_prod_pow1 : ∏ k ∈ K, 2 ^ 2 ^ k = 2 ^ ∑ k ∈ K, 2 ^ k := by
      exact Finset.prod_pow_eq_pow_sum K (fun k ↦ 2 ^ k) 2
    have h_prod_pow2 : ∏ k ∈ Finset.range N_idx, 2 ^ 2 ^ k = 2 ^ ∑ k ∈ Finset.range N_idx, 2 ^ k := by
      exact Finset.prod_pow_eq_pow_sum (Finset.range N_idx) (fun k ↦ 2 ^ k) 2
    have h_sum_eq : ∑ k ∈ Finset.range N_idx, 2 ^ k = N - 1 := by
      rw [sum_pow_two_range N_idx, ← hN]
    have h_final_le : 2 ^ N ≤ 2 ^ (N - 1) := by
      calc
        2 ^ N = totient m := h_phi_eq.symm
        _ = ∏ p ∈ S, 2 ^ 2 ^ (g p) := h_tot_eq_prod
        _ = ∏ k ∈ K, 2 ^ 2 ^ k := h_prod_image
        _ ≤ ∏ k ∈ Finset.range N_idx, 2 ^ 2 ^ k := h_prod_le
        _ = 2 ^ (∑ k ∈ Finset.range N_idx, 2 ^ k) := h_prod_pow2
        _ = 2 ^ (N - 1) := by rw [h_sum_eq]
    have h_N_le : N ≤ N - 1 := (Nat.pow_le_pow_iff_right (by decide)).mp h_final_le
    omega

theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  intro N_idx N F33
  by_cases h : F33.Prime
  · rw [if_pos h]
    exact a_N_of_prime rfl rfl rfl h
  · rw [if_neg h]
    exact a_N_of_composite rfl rfl rfl h
