import FormalConjectures.Util.ProblemImports
set_option warn.sorry true

open Finset Nat BigOperators Int

/--
A386548: The sequence $a(n) = [x^n] \left( \frac{1 - x}{1 - x + x^2} \right)^n$.
This is formally defined by the combinatorial formula $a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} (-1)^k \binom{n+k-1}{k} \binom{n-k-1}{n-2k}$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n / 2 + 1))
    (fun k ↦
      let sign : ℤ := if k % 2 = 0 then 1 else -1
      -- Nat.choose handles binomial(n, k) = 0 if k > n due to truncated subtraction on Nat.
      let term1 : ℕ := (n + k - 1).choose k
      let term2 : ℕ := (n - k - 1).choose (n - 2 * k)
      sign * (term1 : ℤ) * (term2 : ℤ))

lemma add_eq_mod_of_mod_add_mod_eq_zero {a b M : ℕ} (h1 : (a + b) % M = 0) (ha : a < M) (hb : b < M) (hnz : a ≠ 0) : a + b = M := by
  have hdvd : M ∣ a + b := Nat.dvd_of_mod_eq_zero h1
  rcases hdvd with ⟨k, hk⟩
  have hk_lt : k < 2 := by
    by_contra! h
    have : a + b ≥ 2 * M := by
      rw [hk]
      nlinarith
    have : a + b < 2 * M := by omega
    omega
  have hk_nz : k ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hk
    omega
  have hk1 : k = 1 := by omega
  rw [hk, hk1, mul_one]

theorem mod_add_mod_eq_pow {p n j k i : ℕ} [hp : Fact p.Prime] (hi : i ∈ Finset.Ico 1 (k + 1)) (hj : ¬ p ∣ j) (hjn : j ≤ n * p^k) :
    j % p ^ i + (n * p^k - j) % p ^ i = p ^ i := by
  have h_ico : 1 ≤ i ∧ i < k + 1 := by rwa [mem_Ico] at hi
  have h_p_pos : p > 0 := hp.out.pos
  have h_pow_pos : p ^ i > 0 := Nat.pow_pos h_p_pos
  have h_dvd : p ^ i ∣ n * p ^ k := by
    have h_i_le_k : i ≤ k := by omega
    have h1 : p ^ i ∣ p ^ k := pow_dvd_pow p h_i_le_k
    exact dvd_mul_of_dvd_right h1 n
  have h_mod_zero : (n * p ^ k) % p ^ i = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  have h_add_eq : j + (n * p ^ k - j) = n * p ^ k := Nat.add_sub_of_le hjn
  have h_mod_add : (j % p ^ i + (n * p ^ k - j) % p ^ i) % p ^ i = 0 := by
    rw [← Nat.add_mod, h_add_eq, h_mod_zero]
  have h_lt1 : j % p ^ i < p ^ i := Nat.mod_lt j h_pow_pos
  have h_lt2 : (n * p ^ k - j) % p ^ i < p ^ i := Nat.mod_lt (n * p ^ k - j) h_pow_pos
  have h_nz : j % p ^ i ≠ 0 := by
    intro hc
    have h_dvd2 : p ^ i ∣ j := Nat.dvd_of_mod_eq_zero hc
    have h_dvd3 : p ∣ p ^ i := dvd_pow_self p (by omega)
    have h_dvd_j : p ∣ j := dvd_trans h_dvd3 h_dvd2
    exact hj h_dvd_j
  exact add_eq_mod_of_mod_add_mod_eq_zero h_mod_add h_lt1 h_lt2 h_nz

lemma sub_one_mod {C M : ℕ} (hM : M > 0) (hC : C % M = 0) (hC_pos : C > 0) : (C - 1) % M = M - 1 := by
  have hdvd : M ∣ C := Nat.dvd_of_mod_eq_zero hC
  rcases hdvd with ⟨q, rfl⟩
  have hq_pos : q > 0 := by
    cases q
    · contradiction
    · omega
  have h_eq2 : M * q - 1 = M * (q - 1) + (M - 1) := by
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq_pos)
    simp only [Nat.succ_sub_one]
    -- M * succ q' = M * q' + M
    rw [mul_succ]
    omega
  rw [h_eq2, Nat.add_mod]
  have h_mod : M * (q - 1) % M = 0 := Nat.mul_mod_right M (q - 1)
  rw [h_mod, zero_add, Nat.mod_mod]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem padicValNat_choose_ge_k {p n j k : ℕ} [hp : Fact p.Prime] (hj : ¬ p ∣ j) (hjn : j ≤ n * p^k) (_hk : k > 0) (hn : n > 0) :
    padicValNat p (choose (n * p^k) j) ≥ k := by
  let b := log p (n * p^k) + 1
  have h_log_lt : log p (n * p^k) < b := by omega
  have h_choose := padicValNat_choose hjn h_log_lt
  rw [h_choose]
  have h_pow_le : p ^ k ≤ n * p ^ k := by
    rw [mul_comm]
    exact Nat.le_mul_of_pos_right _ hn
  have h_le : k ≤ log p (n * p^k) := Nat.le_log_of_pow_le hp.out.one_lt h_pow_le
  have h_subset : Ico 1 (k + 1) ⊆ Ico 1 b := by
    rw [subset_iff]
    intro x hx
    rw [mem_Ico] at hx ⊢
    omega
  have h_filter : Ico 1 (k + 1) ⊆ filter (fun i ↦ p ^ i ≤ j % p ^ i + (n * p ^ k - j) % p ^ i) (Ico 1 b) := by
    rw [subset_iff]
    intro x hx
    rw [mem_filter]
    have hx_ico : x ∈ Ico 1 (k + 1) := hx
    refine ⟨h_subset hx, ?_⟩
    rw [mod_add_mod_eq_pow hx_ico hj hjn]
  have h_card : card (Ico 1 (k + 1)) ≤ card (filter (fun i ↦ p ^ i ≤ j % p ^ i + (n * p ^ k - j) % p ^ i) (Ico 1 b)) := card_le_card h_filter
  have h_ico_card : card (Ico 1 (k + 1)) = k := Nat.card_Ico 1 (k + 1)
  omega

theorem padicValNat_choose_ge_k_second {p n i k : ℕ} [hp : Fact p.Prime] (hi_pos : i > 0) (hi_p : ¬ p ∣ i) (_hk : k > 0) (hn : n > 0) :
    padicValNat p (choose (n * p^k + i - 1) i) ≥ k := by
  have h_p_pos : p > 0 := hp.out.pos
  have h_n_p_pos : n * p ^ k > 0 := by
    have : p ^ k > 0 := Nat.pow_pos h_p_pos
    exact Nat.mul_pos hn this
  have h_eq : n * p^k + i - 1 = (n * p^k - 1) + i := by omega
  have h_choose_eq : choose (n * p^k + i - 1) i = choose (n * p^k - 1 + i) i := by rw [h_eq]
  rw [h_choose_eq]
  let b := log p (n * p^k - 1 + i) + 1
  have h_log_lt : log p (n * p^k - 1 + i) < b := by omega
  have h_choose' := padicValNat_choose' (p := p) (n := n * p^k - 1) (k := i) (b := b) h_log_lt
  rw [h_choose']
  have h_pow_le : p ^ k ≤ n * p ^ k := by
    rw [mul_comm]
    exact Nat.le_mul_of_pos_right _ hn
  have h_pow_le2 : p ^ k ≤ n * p ^ k - 1 + i := by omega
  have h_le : k ≤ log p (n * p^k - 1 + i) := Nat.le_log_of_pow_le hp.out.one_lt h_pow_le2
  have h_subset : Ico 1 (k + 1) ⊆ Ico 1 b := by
    rw [subset_iff]
    intro x hx
    rw [mem_Ico] at hx ⊢
    omega
  have h_filter : Ico 1 (k + 1) ⊆ filter (fun m ↦ p ^ m ≤ i % p ^ m + (n * p ^ k - 1) % p ^ m) (Ico 1 b) := by
    rw [subset_iff]
    intro m hm
    rw [mem_filter]
    have hm_ico : m ∈ Ico 1 (k + 1) := hm
    have hm_range : 1 ≤ m ∧ m ≤ k := by
      rw [mem_Ico] at hm
      omega
    refine ⟨h_subset hm, ?_⟩
    have h_pow_pos : p ^ m > 0 := Nat.pow_pos h_p_pos
    have h_dvd : p ^ m ∣ n * p ^ k := by
      have h1 : p ^ m ∣ p ^ k := pow_dvd_pow p hm_range.2
      exact dvd_mul_of_dvd_right h1 n
    have h_mod_zero : (n * p ^ k) % p ^ m = 0 := Nat.mod_eq_zero_of_dvd h_dvd
    have h_sub_mod := sub_one_mod h_pow_pos h_mod_zero h_n_p_pos
    rw [h_sub_mod]
    have h_i_nz : i % p ^ m ≠ 0 := by
      intro hc
      have h_dvd2 : p ^ m ∣ i := Nat.dvd_of_mod_eq_zero hc
      have h_dvd3 : p ∣ p ^ m := dvd_pow_self p (by omega)
      have h_dvd_i : p ∣ i := dvd_trans h_dvd3 h_dvd2
      exact hi_p h_dvd_i
    have h_i_ge : i % p ^ m ≥ 1 := Nat.pos_of_ne_zero h_i_nz
    omega
  have h_card : card (Ico 1 (k + 1)) ≤ card (filter (fun m ↦ p ^ m ≤ i % p ^ m + (n * p ^ k - 1) % p ^ m) (Ico 1 b)) := card_le_card h_filter
  have h_ico_card : card (Ico 1 (k + 1)) = k := Nat.card_Ico 1 (k + 1)
  omega


lemma term1_dvd {p n j k : ℕ} [hp : Fact p.Prime] (hj_pos : j > 0) (hj_p : ¬ p ∣ j) (hk : k > 0) (hn : n > 0) :
    p ^ k ∣ (n * p^k + j - 1).choose j := by
  have h_val := padicValNat_choose_ge_k_second hj_pos hj_p hk hn
  rw [padicValNat_dvd_iff]
  exact Or.inr h_val

lemma term_choose_dvd {p n j k : ℕ} [hp : Fact p.Prime] (hj : ¬ p ∣ j) (hjn : j ≤ n * p^k) (hk : k > 0) (hn : n > 0) :
    p ^ k ∣ (n * p^k).choose j := by
  have h_val := padicValNat_choose_ge_k hj hjn hk hn
  rw [padicValNat_dvd_iff]
  exact Or.inr h_val

/--
Conjecture: the stronger supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{2k}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $k$.
-/
lemma dvd_mul_of_dvd_dvd {p : ℤ} {A B : ℤ} {k : ℕ} (h1 : p ^ k ∣ A) (h2 : p ^ k ∣ B) : p ^ (2 * k) ∣ A * B := by
  have h_pow : p ^ (2 * k) = p ^ k * p ^ k := by
    rw [two_mul, pow_add]
  rw [h_pow]
  exact mul_dvd_mul h1 h2

theorem oeis_A386548_supercongruence_conjecture :
  ∀ (p : ℕ), Nat.Prime p → p ≥ 5 →
  ∀ (n k : ℕ), n > 0 → k > 0 →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (2 * k) : ℤ)] := by
  intro p hp hp5 n k hn hk
  have hp_fact : Fact p.Prime := ⟨hp⟩
  rw [Int.modEq_iff_dvd]
  -- Let's test exact_mod_cast
  have h_test (j : ℕ) (hj_pos : j > 0) (hj_p : ¬ p ∣ j) : (p ^ k : ℤ) ∣ ((n * p^k + j - 1).choose j : ℤ) := by
    exact_mod_cast term1_dvd hj_pos hj_p hk hn
  sorry



