import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A129365: $a(n) = A092287(n)/A129364(n)$.
$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$
-/
def a (n : ℕ) : ℕ :=
  -- A092287(n) = Product Product gcd(j,k)
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  -- A129364(n) = Product (floor(n/k)!)^k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

  -- The conjecture guarantees that the division is exact.
  numerator / denominator

-- Helper function for A004125, b(n) = floor(n/2)
def b (n : ℕ) : ℕ := n / 2

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

def num (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k

def den (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma a_def (n : ℕ) : a n = num n / den n := by
  rfl

lemma self_lt_pow (q n : ℕ) (hq : q ≥ 2) : n < q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have : q ^ n * q ≥ (n + 1) * 2 := by
      apply Nat.mul_le_mul
      · exact ih
      · exact hq
    omega

lemma padicValNat_prod {α : Type*} [DecidableEq α] (p : ℕ) [hp : Fact (Nat.Prime p)] (s : Finset α) (f : α → ℕ)
  (hf : ∀ x ∈ s, f x ≠ 0) : padicValNat p (s.prod f) = ∑ x ∈ s, padicValNat p (f x) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [padicValNat.one]
  | insert ha s has ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have h_prod_ne_zero : Finset.prod s f ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      exact hf.2
    rw [padicValNat.mul hf.1 h_prod_ne_zero]
    rw [ih hf.2]

lemma padicValNat_gcd (p a b : ℕ) [hp : Fact (Nat.Prime p)] (ha : a ≠ 0) (hb : b ≠ 0) :
  padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
  have h_gcd_ne_zero : Nat.gcd a b ≠ 0 := by
    intro h
    apply ha
    cases Nat.gcd_eq_zero_iff.mp h with
    | intro h1 _ => exact h1
  apply le_antisymm
  · rw [le_min_iff]
    have h1 : p ^ padicValNat p (Nat.gcd a b) ∣ Nat.gcd a b := pow_padicValNat_dvd
    have h_gcd_dvd_a : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
    have h_gcd_dvd_b : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have h1a : p ^ padicValNat p (Nat.gcd a b) ∣ a := dvd_trans h1 h_gcd_dvd_a
    have h1b : p ^ padicValNat p (Nat.gcd a b) ∣ b := dvd_trans h1 h_gcd_dvd_b
    constructor
    · rwa [padicValNat_dvd_iff_le ha] at h1a
    · rwa [padicValNat_dvd_iff_le hb] at h1b
  · rw [← padicValNat_dvd_iff_le h_gcd_ne_zero]
    rw [Nat.dvd_gcd_iff]
    constructor
    · rw [padicValNat_dvd_iff_le ha]
      exact min_le_left _ _
    · rw [padicValNat_dvd_iff_le hb]
      exact min_le_right _ _

lemma min_padicValNat_eq_sum_if (q j k n : ℕ) [hq : Fact (Nat.Prime q)] (hj : j ∈ Finset.Icc 1 n) (hk : k ∈ Finset.Icc 1 n) :
  min (padicValNat q j) (padicValNat q k) = ∑ i ∈ Finset.Ico 1 (n + 1), if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
  rw [Finset.mem_Icc] at hj hk
  have hj_ne_zero : j ≠ 0 := by omega
  have hk_ne_zero : k ≠ 0 := by omega
  have hj_pos : 0 < j := by omega
  have hk_pos : 0 < k := by omega
  have hq_prime : Nat.Prime q := hq.out
  have hq_ge_2 : q ≥ 2 := Nat.Prime.two_le hq_prime
  have h_val_j_le : padicValNat q j ≤ n := by
    have h_pow_dvd : q ^ padicValNat q j ∣ j := pow_padicValNat_dvd
    have h_pow_le : q ^ padicValNat q j ≤ j := Nat.le_of_dvd hj_pos h_pow_dvd
    have h_val_lt_pow : padicValNat q j < q ^ padicValNat q j := self_lt_pow q (padicValNat q j) hq_ge_2
    omega
  have h_val_k_le : padicValNat q k ≤ n := by
    have h_pow_dvd : q ^ padicValNat q k ∣ k := pow_padicValNat_dvd
    have h_pow_le : q ^ padicValNat q k ≤ k := Nat.le_of_dvd hk_pos h_pow_dvd
    have h_val_lt_pow : padicValNat q k < q ^ padicValNat q k := self_lt_pow q (padicValNat q k) hq_ge_2
    omega
  let m := min (padicValNat q j) (padicValNat q k)
  have h_m_le : m ≤ n := by
    have : m ≤ padicValNat q j := min_le_left _ _
    omega
  have h1 : 1 ≤ m + 1 := by omega
  have h2 : m + 1 ≤ n + 1 := by omega
  rw [← Finset.sum_Ico_consecutive (fun i => if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) h1 h2]
  have h_left : ∑ i ∈ Finset.Ico 1 (m + 1), (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) = m := by
    have : ∑ i ∈ Finset.Ico 1 (m + 1), (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) = ∑ i ∈ Finset.Ico 1 (m + 1), 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h_i_le : i ≤ m := by omega
      have h_dvd_j : q ^ i ∣ j := by
        rw [padicValNat_dvd_iff_le hj_ne_zero]
        have : m ≤ padicValNat q j := min_le_left _ _
        omega
      have h_dvd_k : q ^ i ∣ k := by
        rw [padicValNat_dvd_iff_le hk_ne_zero]
        have : m ≤ padicValNat q k := min_le_right _ _
        omega
      rw [if_pos ⟨h_dvd_j, h_dvd_k⟩]
    rw [this]
    simp [m]
  have h_right : ∑ i ∈ Finset.Ico (m + 1) (n + 1), (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h_i_gt : m < i := by omega
    have h_not_dvd : ¬ (q ^ i ∣ j ∧ q ^ i ∣ k) := by
      intro h_both
      have h_le_j : i ≤ padicValNat q j := by
        rw [← padicValNat_dvd_iff_le hj_ne_zero]
        exact h_both.1
      have h_le_k : i ≤ padicValNat q k := by
        rw [← padicValNat_dvd_iff_le hk_ne_zero]
        exact h_both.2
      have h_le_m : i ≤ m := le_min h_le_j h_le_k
      omega
    rw [if_neg h_not_dvd]
  rw [h_left, h_right, add_zero]

lemma sum_if_eq_div (n q i : ℕ) :
  ∑ j ∈ Finset.Icc 1 n, (if q ^ i ∣ j then 1 else 0) = n / q ^ i := by
  rw [Finset.sum_boole]
  have h_eq : Finset.Icc 1 n = Finset.Ioc 0 n := Finset.Icc_succ_left_eq_Ioc 0 n
  rw [h_eq]
  exact Nat.Ioc_filter_dvd_card_eq_div n (q ^ i)

lemma double_sum_min_padicValNat (n q : ℕ) [hq : Fact (Nat.Prime q)] :
  ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, min (padicValNat q j) (padicValNat q k) =
    ∑ i ∈ Finset.Ico 1 (n + 1), (n / q ^ i) ^ 2 := by
  have h1 : ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, min (padicValNat q j) (padicValNat q k) =
    ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1), if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact min_padicValNat_eq_sum_if q j k n hj hk
  rw [h1]
  have h2 : ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1), (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) =
    ∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1), ∑ k ∈ Finset.Icc 1 n, (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Finset.sum_comm
  rw [h2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h_mul : ∀ j k, (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) = (if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0) := by
    intro j k
    by_cases hj : q ^ i ∣ j
    · by_cases hk : q ^ i ∣ k
      · simp [hj, hk]
      · simp [hj, hk]
    · simp [hj]
  have h_inner : ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) = (n / q ^ i) ^ 2 := by
    simp_rw [h_mul]
    have h_pull : ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ((if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0)) =
      (∑ j ∈ Finset.Icc 1 n, if q ^ i ∣ j then 1 else 0) * (∑ k ∈ Finset.Icc 1 n, if q ^ i ∣ k then 1 else 0) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    rw [h_pull]
    rw [sum_if_eq_div]
    ring
  exact h_inner

lemma num_val_eq_double_sum (n q : ℕ) [hq : Fact (Nat.Prime q)] :
  padicValNat q (num n) = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, min (padicValNat q j) (padicValNat q k) := by
  unfold num
  rw [padicValNat_prod q (Finset.Icc 1 n)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [padicValNat_prod q (Finset.Icc 1 n)]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hj hk
      have hj_ne_zero : j ≠ 0 := by omega
      have hk_ne_zero : k ≠ 0 := by omega
      rw [padicValNat_gcd q j k hj_ne_zero hk_ne_zero]
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hk_ne_zero : k ≠ 0 := by omega
      intro h_gcd
      rw [Nat.gcd_eq_zero_iff] at h_gcd
      omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    have hj_ne_zero : j ≠ 0 := by omega
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_ne_zero : k ≠ 0 := by omega
    intro h_gcd
    rw [Nat.gcd_eq_zero_iff] at h_gcd
    omega

lemma padicValNat_num (n q : ℕ) [hq : Fact (Nat.Prime q)] :
  padicValNat q (num n) = ∑ i ∈ Finset.Ico 1 (n + 1), (n / q ^ i) ^ 2 := by
  rw [num_val_eq_double_sum, double_sum_min_padicValNat]

lemma log_lt_n_plus_one (q n k : ℕ) : Nat.log q (n / k) < n + 1 := by
  have h_log : Nat.log q (n / k) ≤ n / k := Nat.log_le_self q (n / k)
  have h_div : n / k ≤ n := Nat.div_le_self n k
  omega

lemma padicValNat_den (n q : ℕ) [hq : Fact (Nat.Prime q)] :
  padicValNat q (den n) = ∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * q ^ i) := by
  unfold den
  have hq_prime : Nat.Prime q := hq.out
  have hq_ge_2 : q ≥ 2 := Nat.Prime.two_le hq_prime
  rw [padicValNat_prod q]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [padicValNat.pow k]
    · rw [padicValNat_factorial (log_lt_n_plus_one q n k)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.div_div_eq_div_mul]
    · exact Nat.factorial_ne_zero (n / k)
  · intro k hk
    have h_fac_pos : 0 < (n / k).factorial := Nat.factorial_pos (n / k)
    exact Nat.ne_of_gt (pow_pos h_fac_pos k)

lemma num_ne_zero (n : ℕ) : num n ≠ 0 := by
  unfold num
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rw [Finset.mem_Icc] at hj hk
  have hj_ne_zero : j ≠ 0 := by omega
  have hk_ne_zero : k ≠ 0 := by omega
  intro h_gcd
  rw [Nat.gcd_eq_zero_iff] at h_gcd
  omega

lemma den_ne_zero (n : ℕ) : den n ≠ 0 := by
  unfold den
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply pow_ne_zero
  exact Nat.factorial_ne_zero (n / k)

lemma sum_div_le_sq (M : ℕ) : ∑ k ∈ Finset.Icc 1 M, k * (M / k) ≤ M ^ 2 := by
  have h_le : ∀ k ∈ Finset.Icc 1 M, k * (M / k) ≤ M := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have : k * (M / k) ≤ M := Nat.mul_div_le M k
    exact this
  have h_sum_le : ∑ k ∈ Finset.Icc 1 M, k * (M / k) ≤ ∑ k ∈ Finset.Icc 1 M, M := Finset.sum_le_sum h_le
  rw [Finset.sum_const] at h_sum_le
  have h_card : (Finset.Icc 1 M).card = M := by
    simp
  rw [h_card, smul_eq_mul] at h_sum_le
  rw [sq]
  exact h_sum_le

lemma sum_div_eq_sq_of_le_two (M : ℕ) (hM : M ≤ 2) : ∑ k ∈ Finset.Icc 1 M, k * (M / k) = M ^ 2 := by
  interval_cases M
  · rfl
  · rfl
  · rfl

lemma div_eq_one_of_le_of_lt {a b : ℕ} (hb : b ≠ 0) (hle : b ≤ a) (hlt : a < b + b) : a / b = 1 := by
  have : a = b + (a - b) := by omega
  rw [this]
  rw [Nat.add_div_of_dvd_right (dvd_refl b)]
  have h_div_self : b / b = 1 := Nat.div_self (Nat.pos_of_ne_zero hb)
  have h_div_lt : (a - b) / b = 0 := by
    apply Nat.div_eq_of_lt
    omega
  rw [h_div_self, h_div_lt, add_zero]

lemma sum_div_lt_sq (M : ℕ) (hM : 3 ≤ M) : ∑ k ∈ Finset.Icc 1 M, k * (M / k) < M ^ 2 := by
  have h_le : ∀ k ∈ Finset.Icc 1 M, k * (M / k) ≤ M := by
    intro k hk
    exact Nat.mul_div_le M k
  have h_sum_lt : ∑ k ∈ Finset.Icc 1 M, k * (M / k) < ∑ k ∈ Finset.Icc 1 M, M := by
    apply Finset.sum_lt_sum h_le
    use M - 1
    constructor
    · rw [Finset.mem_Icc]; omega
    · have h_div : M / (M - 1) = 1 := by
        apply div_eq_one_of_le_of_lt <;> omega
      rw [h_div, mul_one]
      omega
  rw [Finset.sum_const] at h_sum_lt
  have h_card : (Finset.Icc 1 M).card = M := by simp
  rw [h_card, smul_eq_mul] at h_sum_lt
  rw [sq]
  exact h_sum_lt

lemma sum_div_eq_sq_global (n q i : ℕ) (hq : q ≥ 2) (hi : i ≥ 1) (h_le2 : n / q ^ i ≤ 2) :
  ∑ k ∈ Finset.Icc 1 n, k * (n / (k * q ^ i)) = (n / q ^ i) ^ 2 := by
  rcases (⟨n / q ^ i, rfl⟩ : ∃ M, M = n / q ^ i) with ⟨M, hM⟩
  have h_M_le_n : M ≤ n := by
    rw [hM]
    have h_qi_ge_2 : q ^ i ≥ 2 := by
      have : q ^ i ≥ q ^ 1 := Nat.pow_le_pow_right (by omega) hi
      rw [pow_one] at this
      omega
    have : n / q ^ i ≤ n / 2 := Nat.div_le_div_left h_qi_ge_2 (by omega)
    have : n / 2 ≤ n := Nat.div_le_self n 2
    omega
  have h_Ico : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    rw [← Finset.Ico_succ_right_eq_Icc]; rfl
  rw [h_Ico]
  have h1 : 1 ≤ M + 1 := by omega
  have h2 : M + 1 ≤ n + 1 := by omega
  rw [← Finset.sum_Ico_consecutive (fun k => k * (n / (k * q ^ i))) h1 h2]
  have h_left : ∑ k ∈ Finset.Ico 1 (M + 1), k * (n / (k * q ^ i)) = M ^ 2 := by
    have h_eq_Ico : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := Finset.Ico_succ_right_eq_Icc 1 M
    have h_eq : ∑ k ∈ Finset.Ico 1 (M + 1), k * (n / (k * q ^ i)) = ∑ k ∈ Finset.Icc 1 M, k * (M / k) := by
      rw [h_eq_Ico]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have : n / (k * q ^ i) = M / k := by
        rw [hM]
        rw [mul_comm]
        rw [← Nat.div_div_eq_div_mul]
      rw [this]
    rw [h_eq]
    apply sum_div_eq_sq_of_le_two
    omega
  have h_right : ∑ k ∈ Finset.Ico (M + 1) (n + 1), k * (n / (k * q ^ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h_k_gt : k > M := by omega
    have h_div_zero : n / (k * q ^ i) = 0 := by
      apply Nat.div_eq_of_lt
      have h_qi_pos : 0 < q ^ i := by positivity
      have h_lt : n / q ^ i < k := by rw [← hM]; omega
      rwa [← Nat.div_lt_iff_lt_mul h_qi_pos]
    rw [h_div_zero, mul_zero]
  rw [hM] at h_left h_right ⊢
  omega

lemma sum_div_le_sq_global (n q i : ℕ) (hq : q ≥ 2) (hi : i ≥ 1) :
  ∑ k ∈ Finset.Icc 1 n, k * (n / (k * q ^ i)) ≤ (n / q ^ i) ^ 2 := by
  rcases (⟨n / q ^ i, rfl⟩ : ∃ M, M = n / q ^ i) with ⟨M, hM⟩
  have h_Ico : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    rw [← Finset.Ico_succ_right_eq_Icc]; rfl
  rw [h_Ico]
  have h1 : 1 ≤ M + 1 := by omega
  have h2 : M + 1 ≤ n + 1 := by
    have h_qi_ge_2 : q ^ i ≥ 2 := by
      have : q ^ i ≥ q ^ 1 := Nat.pow_le_pow_right (by omega) hi
      rw [pow_one] at this
      omega
    have : n / q ^ i ≤ n / 2 := Nat.div_le_div_left h_qi_ge_2 (by omega)
    have : n / 2 ≤ n := Nat.div_le_self n 2
    omega
  rw [← Finset.sum_Ico_consecutive (fun k => k * (n / (k * q ^ i))) h1 h2]
  have h_left : ∑ k ∈ Finset.Ico 1 (M + 1), k * (n / (k * q ^ i)) ≤ M ^ 2 := by
    have h_eq_Ico : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := Finset.Ico_succ_right_eq_Icc 1 M
    have h_eq : ∑ k ∈ Finset.Ico 1 (M + 1), k * (n / (k * q ^ i)) = ∑ k ∈ Finset.Icc 1 M, k * (M / k) := by
      rw [h_eq_Ico]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have : n / (k * q ^ i) = M / k := by
        rw [hM]
        rw [mul_comm]
        rw [← Nat.div_div_eq_div_mul]
      rw [this]
    rw [h_eq]
    exact sum_div_le_sq M
  have h_right : ∑ k ∈ Finset.Ico (M + 1) (n + 1), k * (n / (k * q ^ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h_k_gt : k > M := by omega
    have h_div_zero : n / (k * q ^ i) = 0 := by
      apply Nat.div_eq_of_lt
      have h_qi_pos : 0 < q ^ i := by positivity
      have h_lt : n / q ^ i < k := by rw [← hM]; omega
      rwa [← Nat.div_lt_iff_lt_mul h_qi_pos]
    rw [h_div_zero, mul_zero]
  rw [hM] at h_left h_right ⊢
  omega

lemma sum_div_lt_sq_global (n q i : ℕ) (hq : q ≥ 2) (hi : i ≥ 1) (h_ge3 : n / q ^ i ≥ 3) :
  ∑ k ∈ Finset.Icc 1 n, k * (n / (k * q ^ i)) < (n / q ^ i) ^ 2 := by
  rcases (⟨n / q ^ i, rfl⟩ : ∃ M, M = n / q ^ i) with ⟨M, hM⟩
  have h_M_le_n : M ≤ n := by
    rw [hM]
    have h_qi_ge_2 : q ^ i ≥ 2 := by
      have : q ^ i ≥ q ^ 1 := Nat.pow_le_pow_right (by omega) hi
      rw [pow_one] at this
      omega
    have : n / q ^ i ≤ n / 2 := Nat.div_le_div_left h_qi_ge_2 (by omega)
    have : n / 2 ≤ n := Nat.div_le_self n 2
    omega
  have h_Ico : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    rw [← Finset.Ico_succ_right_eq_Icc]; rfl
  rw [h_Ico]
  have h1 : 1 ≤ M + 1 := by omega
  have h2 : M + 1 ≤ n + 1 := by omega
  rw [← Finset.sum_Ico_consecutive (fun k => k * (n / (k * q ^ i))) h1 h2]
  have h_left : ∑ k ∈ Finset.Ico 1 (M + 1), k * (n / (k * q ^ i)) < M ^ 2 := by
    have h_eq_Ico : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := Finset.Ico_succ_right_eq_Icc 1 M
    have h_eq : ∑ k ∈ Finset.Ico 1 (M + 1), k * (n / (k * q ^ i)) = ∑ k ∈ Finset.Icc 1 M, k * (M / k) := by
      rw [h_eq_Ico]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have : n / (k * q ^ i) = M / k := by
        rw [hM]
        rw [mul_comm]
        rw [← Nat.div_div_eq_div_mul]
      rw [this]
    rw [h_eq]
    apply sum_div_lt_sq M
    omega
  have h_right : ∑ k ∈ Finset.Ico (M + 1) (n + 1), k * (n / (k * q ^ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h_k_gt : k > M := by omega
    have h_div_zero : n / (k * q ^ i) = 0 := by
      apply Nat.div_eq_of_lt
      have h_qi_pos : 0 < q ^ i := by positivity
      have h_lt : n / q ^ i < k := by rw [← hM]; omega
      rwa [← Nat.div_lt_iff_lt_mul h_qi_pos]
    rw [h_div_zero, mul_zero]
  rw [hM] at h_left h_right ⊢
  omega

lemma den_dvd_num (n : ℕ) (hn : 0 < n) : den n ∣ num n := by
  have _ := hn
  have h_den_nz := den_ne_zero n
  have h_num_nz := num_ne_zero n
  rw [← Nat.factorization_le_iff_dvd h_den_nz h_num_nz]
  rw [Finsupp.le_def]
  intro p
  by_cases hp : Nat.Prime p
  · have : Fact (Nat.Prime p) := ⟨hp⟩
    rw [Nat.factorization_def (den n) hp]
    rw [Nat.factorization_def (num n) hp]
    rw [padicValNat_den n p, padicValNat_num n p]
    have h_rw : (∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * p ^ i)) =
                 ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1), k * (n / (k * p ^ i)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    rw [h_rw, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hq_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
    exact sum_div_le_sq_global n p i hq_ge_2 hi.1
  · have h1 : (den n).factorization p = 0 := Nat.factorization_eq_zero_of_not_prime (den n) hp
    have h2 : (num n).factorization p = 0 := Nat.factorization_eq_zero_of_not_prime (num n) hp
    rw [h1, h2]

/--
oeis_a129365_conjecture_B: If p is a prime then p|a(n) if and only if p <= n/3.
Note: Since `a n` is non-zero for $n > 0$, $p \mid a n$ iff $p$ is in the factorization of $a n$.
-/
theorem oeis_a129365_conjecture_B (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) :
  p ∣ a n ↔ p ≤ n / 3 := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have h_a_nz : a n ≠ 0 := by
    rw [a_def]
    have h_le : den n ≤ num n := by
      have h_num_pos : 0 < num n := by
        have := num_ne_zero n
        omega
      exact Nat.le_of_dvd h_num_pos (den_dvd_num n hn)
    have h_den_pos : 0 < den n := by
      have := den_ne_zero n
      omega
    have h_div_pos := Nat.div_pos h_le h_den_pos
    omega
  rw [dvd_iff_padicValNat_ne_zero h_a_nz]
  rw [a_def]
  rw [padicValNat.div_of_dvd (den_dvd_num n hn)]
  have h_den_le_num : padicValNat p (den n) ≤ padicValNat p (num n) := by
    rw [padicValNat_den n p, padicValNat_num n p]
    have h_rw : (∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * p ^ i)) =
                 ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1), k * (n / (k * p ^ i)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    have h_sum_comm_eq : (∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * p ^ i)) =
                         ∑ i ∈ Finset.Ico 1 (n + 1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ i)) := by
      rw [h_rw, Finset.sum_comm]
    rw [h_sum_comm_eq]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hq_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
    exact sum_div_le_sq_global n p i hq_ge_2 hi.1
  constructor
  · intro h_ne
    have h_lt : padicValNat p (den n) < padicValNat p (num n) := by omega
    by_contra h_gt
    push_neg at h_gt
    have h_div_le : n / p ≤ 2 := by
      have hp_pos : 0 < p := by omega
      have h_gt' : n / 3 < p := by omega
      have h_lt_mul : n < 3 * p := by
        have : p * 3 = 3 * p := mul_comm p 3
        rw [← this]
        rwa [Nat.div_lt_iff_lt_mul (by decide)] at h_gt'
      have h_div_lt : n / p < 3 := by
        rwa [Nat.div_lt_iff_lt_mul hp_pos]
      omega
    have h_all_le2 : ∀ i ∈ Finset.Ico 1 (n + 1), n / p ^ i ≤ 2 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have : p ^ i ≥ p := by
        have : p ^ i ≥ p ^ 1 := Nat.pow_le_pow_right (by omega) hi.1
        rwa [pow_one] at this
      have : n / p ^ i ≤ n / p := Nat.div_le_div_left this (by omega)
      omega
    have h_eq : padicValNat p (den n) = padicValNat p (num n) := by
      rw [padicValNat_den n p, padicValNat_num n p]
      have h_rw : (∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * p ^ i)) =
                   ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1), k * (n / (k * p ^ i)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
      have h_sum_comm_eq : (∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * p ^ i)) =
                           ∑ i ∈ Finset.Ico 1 (n + 1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ i)) := by
        rw [h_rw, Finset.sum_comm]
      rw [h_sum_comm_eq]
      apply Finset.sum_congr rfl
      intro i hi
      have hq_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
      exact sum_div_eq_sq_global n p i hq_ge_2 (Finset.mem_Ico.mp hi).1 (h_all_le2 i hi)
    omega
  · intro h_le
    rw [padicValNat_den n p, padicValNat_num n p]
    have h_rw : (∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * p ^ i)) =
                 ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1), k * (n / (k * p ^ i)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    have h_sum_comm_eq : (∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / (k * p ^ i)) =
                         ∑ i ∈ Finset.Ico 1 (n + 1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ i)) := by
      rw [h_rw, Finset.sum_comm]
    rw [h_sum_comm_eq]
    have h_le_each : ∀ i ∈ Finset.Ico 1 (n + 1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ i)) ≤ (n / p ^ i) ^ 2 := by
      intro i hi
      have hq_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
      exact sum_div_le_sq_global n p i hq_ge_2 (Finset.mem_Ico.mp hi).1
    have h_strict : ∃ i ∈ Finset.Ico 1 (n + 1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ i)) < (n / p ^ i) ^ 2 := by
      use 1
      constructor
      · rw [Finset.mem_Ico]; omega
      · have hq_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
        have h_ge3 : 3 ≤ n / p ^ 1 := by
          rw [pow_one]
          have hp_pos : 0 < p := by omega
          rw [Nat.le_div_iff_mul_le hp_pos]
          have : 3 * p = p * 3 := mul_comm 3 p
          rw [this]
          rwa [Nat.le_div_iff_mul_le (by decide)] at h_le
        exact sum_div_lt_sq_global n p 1 hq_ge_2 (by omega) h_ge3
    have h_final_lt := Finset.sum_lt_sum h_le_each h_strict
    exact Nat.sub_ne_zero_of_lt h_final_lt
