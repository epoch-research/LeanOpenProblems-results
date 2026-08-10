import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def f_tuple (n k : ℕ) : ℕ :=
  if 0 < k then
    let max_j : ℕ := (n - 1) / k
    Finset.prod (range (max_j + 1)) fun j => n - j * k
  else
    1

def A297707 (n : ℕ) : ℕ :=
  Finset.prod (Ico 1 n) fun k => f_tuple n k

local notation "a" => A297707

noncomputable def Nat.prevPrime (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).max.getD 0

def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

theorem one_le_f_tuple (n k : ℕ) (hn : 0 < n) : 1 ≤ f_tuple n k := by
  by_cases hk : 0 < k
  · dsimp [f_tuple]
    rw [if_pos hk]
    have h_all : ∀ j ∈ range ((n - 1) / k + 1), 1 ≤ n - j * k := by
      intro j hj
      have h_mem : j < (n - 1) / k + 1 := mem_range.mp hj
      have h_le : j * k ≤ n - 1 := by
        have : j ≤ (n - 1) / k := by omega
        have h_mul := Nat.div_mul_le_self (n - 1) k
        have h_mono : j * k ≤ ((n - 1) / k) * k := Nat.mul_le_mul_right k this
        exact le_trans h_mono h_mul
      omega
    exact Finset.one_le_prod' h_all
  · dsimp [f_tuple]
    rw [if_neg hk]

theorem factorial_eq_prod_range_sub (n : ℕ) : Nat.factorial n = ∏ j ∈ range n, (n - j) := by
  induction' n with k ih
  · simp
  · rw [Nat.factorial_succ]
    rw [prod_range_succ']
    have h_sub : ∀ j ∈ range k, k + 1 - (j + 1) = k - j := by
      intro j hj
      omega
    have h_congr : ∏ j ∈ range k, (k + 1 - (j + 1)) = ∏ j ∈ range k, (k - j) := by
      apply prod_congr rfl
      exact h_sub
    rw [h_congr]
    rw [ih]
    have h_0 : k + 1 - 0 = k + 1 := by omega
    rw [h_0]
    ring

theorem a_ge_factorial (n : ℕ) (hn : 2 < n) : Nat.factorial n ≤ a n := by
  have h1 : 1 ∈ Ico 1 n := by
    rw [mem_Ico]
    constructor
    · decide
    · linarith
  have h_one : ∀ k ∈ Ico 1 n, 1 ≤ f_tuple n k := by
    intro k hk
    have : 0 < n := by omega
    exact one_le_f_tuple n k this
  have h_le : f_tuple n 1 ≤ a n := Finset.single_le_prod' h_one h1
  have hd2 : f_tuple n 1 = ∏ j ∈ range n, (n - j) := by
    dsimp [f_tuple]
    have h_div : (n - 1) / 1 = n - 1 := Nat.div_one (n - 1)
    rw [h_div]
    have h_add : n - 1 + 1 = n := by omega
    rw [h_add]
    congr 1
    ext j
    rw [Nat.mul_one]
  rw [hd2] at h_le
  rw [factorial_eq_prod_range_sub n]
  exact h_le

theorem factorial_gt_two_mul (n : ℕ) (hn : 4 ≤ n) : 2 * n < Nat.factorial n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · decide
  · rw [Nat.factorial_succ]
    have : 2 * (k + 1) = 2 * k + 2 := by omega
    have h1 : (k + 1) * Nat.factorial k = k * Nat.factorial k + Nat.factorial k := by ring
    have h2 : 2 * k + 2 < k * Nat.factorial k + Nat.factorial k := by
      have h3 : 2 * k < Nat.factorial k := ih
      have h4 : 2 < k * Nat.factorial k := by
        have : 4 ≤ k := hk
        have : 1 ≤ Nat.factorial k := Nat.factorial_pos k
        nlinarith
      omega
    omega

theorem a_gt_two_mul (n : ℕ) (hn : 2 < n) : 2 * n < a n := by
  by_cases h4 : 4 ≤ n
  · have h1 : 2 * n < Nat.factorial n := factorial_gt_two_mul n h4
    have h2 : Nat.factorial n ≤ a n := a_ge_factorial n hn
    exact lt_of_lt_of_le h1 h2
  · have : n = 3 := by omega
    subst this
    decide

theorem prevPrime_gt (n : ℕ) (hn : 2 < n) : n < Nat.prevPrime (a n) := by
  have h_ne : n ≠ 0 := by omega
  obtain ⟨p, hp, h_lt1, h_le2⟩ := Nat.exists_prime_lt_and_le_two_mul n h_ne
  have h_lt_a : p < a n := by
    have h_gt : 2 * n < a n := a_gt_two_mul n hn
    omega
  have h_mem : p ∈ Finset.filter Nat.Prime (Finset.range (a n)) := by
    rw [mem_filter, mem_range]
    exact ⟨h_lt_a, hp⟩
  have h_le := Finset.le_max (α := ℕ) (s := Finset.filter Nat.Prime (Finset.range (a n))) h_mem
  dsimp [Nat.prevPrime]
  generalize (Finset.filter Nat.Prime (Finset.range (a n))).max = m at h_le ⊢
  cases m
  · simp at h_le
  · rw [WithBot.coe_le_coe] at h_le
    rename_i val
    change n < val
    omega

theorem prime_dvd_a_of_le (n : ℕ) (p : ℕ) (hn : 2 < n) (hp : p.Prime) (hpn : p ≤ n) : p ∣ a n := by
  have h1 : 1 ∈ Ico 1 n := by
    rw [mem_Ico]
    constructor
    · decide
    · linarith
  have hd1 : (fun k_1 => if 0 < k_1 then let max_j := (n - 1) / k_1; ∏ j ∈ range (max_j + 1), (n - j * k_1) else 1) 1 ∣ a n := by
    apply Finset.dvd_prod_of_mem (s := Ico 1 n)
    exact h1
  have hd2 : (fun k_1 => if 0 < k_1 then let max_j := (n - 1) / k_1; ∏ j ∈ range (max_j + 1), (n - j * k_1) else 1) 1 = ∏ j ∈ range n, (n - j) := by
    dsimp
    have h_div : (n - 1) / 1 = n - 1 := Nat.div_one (n - 1)
    rw [h_div]
    have h_add : n - 1 + 1 = n := by omega
    rw [h_add]
    congr 1
    ext j
    rw [Nat.mul_one]
  rw [hd2] at hd1
  have hp_ge_2 : 2 ≤ p := hp.two_le
  have hp_ge_1 : 1 ≤ p := by omega
  have hj : n - p < n := by omega
  have h_mem : n - p ∈ range n := mem_range.mpr hj
  have h_dvd_prod : n - (n - p) ∣ ∏ j ∈ range n, (n - j) := by
    apply Finset.dvd_prod_of_mem (s := range n)
    exact h_mem
  have h_sub : n - (n - p) = p := by omega
  rw [h_sub] at h_dvd_prod
  exact dvd_trans h_dvd_prod hd1

theorem a_diff_composite_ge (n : ℕ) (hn : 2 < n) : IsComposite (a n - Nat.prevPrime (a n)) → (a n - Nat.prevPrime (a n)) ≥ (n + 1) ^ 2 := by
  intro hc
  have hX_comp : 1 < a n - Nat.prevPrime (a n) ∧ ¬ Nat.Prime (a n - Nat.prevPrime (a n)) := hc
  have h_lt : Nat.prevPrime (a n) < a n := by
    have : n < Nat.prevPrime (a n) := prevPrime_gt n hn
    have h_gt : 2 * n < a n := a_gt_two_mul n hn
    omega
  let X := a n - Nat.prevPrime (a n)
  have hX_prop : X = a n - Nat.prevPrime (a n) := rfl
  have h_prime_X : ¬ Nat.Prime X := hX_comp.2
  have h_ge_2 : 2 ≤ X := by omega
  let p := minFac X
  have hp_prime : p.Prime := minFac_prime (by omega)
  have hp_dvd : p ∣ X := minFac_dvd X
  have hp_gt_n : p > n := by
    by_contra h_le
    push_neg at h_le
    have hp_dvd_a : p ∣ a n := prime_dvd_a_of_le n p hn hp_prime h_le
    have hp_dvd_prev : p ∣ Nat.prevPrime (a n) := by
      dsimp [Nat.prevPrime]
      have h_sub_eq : a n - X = (Finset.filter Nat.Prime (Finset.range (a n))).max.getD 0 := by
        dsimp [Nat.prevPrime] at hX_prop ⊢
        omega
      rw [← h_sub_eq]
      exact Nat.dvd_sub hp_dvd_a hp_dvd
    have h_gt_n : n < Nat.prevPrime (a n) := prevPrime_gt n hn
    dsimp [Nat.prevPrime] at h_gt_n hp_dvd_prev
    have h_sub_eq : a n - X = (Finset.filter Nat.Prime (Finset.range (a n))).max.getD 0 := by
      dsimp [Nat.prevPrime] at hX_prop ⊢
      omega
    generalize h_max : (Finset.filter Nat.Prime (Finset.range (a n))).max = m at h_sub_eq h_gt_n hp_dvd_prev
    cases m
    · change a n - X = 0 at h_sub_eq
      change n < 0 at h_gt_n
      omega
    · rename_i val
      change a n - X = val at h_sub_eq
      change n < val at h_gt_n
      change p ∣ val at hp_dvd_prev
      have h_mem : val ∈ Finset.filter Nat.Prime (Finset.range (a n)) := Finset.mem_of_max h_max
      rw [mem_filter] at h_mem
      have h_val_prime : val.Prime := h_mem.2
      have hp_ne_1 : p ≠ 1 := hp_prime.ne_one
      have h_eq : val = p := by
        have := h_val_prime.dvd_iff_eq hp_ne_1
        rw [← this]
        exact hp_dvd_prev
      subst h_eq
      omega
  have hp_ge : p ≥ n + 1 := by omega
  generalize hk : X / p = k
  have hX_eq : X = p * k := by
    rw [← hk]
    exact (Nat.mul_div_cancel' hp_dvd).symm
  have hk_ne_1 : k ≠ 1 := by
    intro hk1
    have : X = p := by
      rw [hX_eq, hk1]
      ring
    have : Nat.Prime X := by
      rw [this]
      exact hp_prime
    contradiction
  have hX_pos : X > 0 := by omega
  have hk_pos : k > 0 := by
    by_contra hk0
    push_neg at hk0
    have : k = 0 := by omega
    rw [this] at hX_eq
    rw [mul_zero] at hX_eq
    omega
  have hk_ge : 2 ≤ k := by omega
  let p' := minFac k
  have hp'_prime : p'.Prime := minFac_prime (by omega)
  have hp'_dvd : p' ∣ k := minFac_dvd k
  have hp'_dvd_X : p' ∣ X := by
    rw [hX_eq]
    exact dvd_mul_of_dvd_right hp'_dvd p
  have hp'_gt_n : p' > n := by
    by_contra h_le
    push_neg at h_le
    have hp'_dvd_a : p' ∣ a n := prime_dvd_a_of_le n p' hn hp'_prime h_le
    have h_sub_eq : a n - X = (Finset.filter Nat.Prime (Finset.range (a n))).max.getD 0 := by
      dsimp [Nat.prevPrime] at hX_prop ⊢
      omega
    have hp'_dvd_prev : p' ∣ Nat.prevPrime (a n) := by
      dsimp [Nat.prevPrime]
      rw [← h_sub_eq]
      exact Nat.dvd_sub hp'_dvd_a hp'_dvd_X
    have h_gt_n : n < Nat.prevPrime (a n) := prevPrime_gt n hn
    dsimp [Nat.prevPrime] at h_sub_eq h_gt_n hp'_dvd_prev
    have h_sub_eq : a n - X = (Finset.filter Nat.Prime (Finset.range (a n))).max.getD 0 := by
      dsimp [Nat.prevPrime] at hX_prop ⊢
      omega
    generalize h_max : (Finset.filter Nat.Prime (Finset.range (a n))).max = m at h_sub_eq h_gt_n hp'_dvd_prev
    cases m
    · change a n - X = 0 at h_sub_eq
      change n < 0 at h_gt_n
      omega
    · rename_i val
      change a n - X = val at h_sub_eq
      change n < val at h_gt_n
      change p' ∣ val at hp'_dvd_prev
      have h_mem : val ∈ Finset.filter Nat.Prime (Finset.range (a n)) := Finset.mem_of_max h_max
      rw [mem_filter] at h_mem
      have h_val_prime : val.Prime := h_mem.2
      have hp'_ne_1 : p' ≠ 1 := hp'_prime.ne_one
      have h_eq : val = p' := by
        have := h_val_prime.dvd_iff_eq hp'_ne_1
        rw [← this]
        exact hp'_dvd_prev
      subst h_eq
      omega
  have hp'_ge : p' ≥ n + 1 := by omega
  have hk_ge_n1 : k ≥ n + 1 := by
    have : minFac k ≤ k := Nat.minFac_le hk_pos
    omega
  calc X = p * k := hX_eq
    _ ≥ (n + 1) * (n + 1) := Nat.mul_le_mul hp_ge hk_ge_n1
    _ = (n + 1) ^ 2 := by ring
