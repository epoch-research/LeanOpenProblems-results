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


def num (n : ℕ) : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
def den (n : ℕ) : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma num_pos (n : ℕ) : 0 < num n := by
  unfold num
  apply prod_pos
  intro j hj
  apply prod_pos
  intro k hk
  rw [mem_Icc] at hj hk
  have hj0 : 0 < j := hj.1
  exact Nat.gcd_pos_of_pos_left k hj0

lemma den_pos (n : ℕ) : 0 < den n := by
  unfold den
  apply prod_pos
  intro k hk
  positivity

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,

lemma den_factorization (n p : ℕ) (_ : p.Prime) :
    (den n).factorization p = ∑ k ∈ Icc 1 n, k * (factorial (n / k)).factorization p := by
  unfold den
  rw [factorization_prod_apply]
  · simp [factorization_pow]
  · intro k hk
    positivity


lemma num_factorization (n p : ℕ) (_ : p.Prime) :
    (num n).factorization p = ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (Nat.gcd j k).factorization p := by
  unfold num
  rw [factorization_prod_apply]
  · refine sum_congr rfl fun j hj => ?_
    rw [factorization_prod_apply]
    intro k hk
    rw [mem_Icc] at hj hk
    exact Nat.gcd_ne_zero_left (_root_.ne_of_gt hj.1)
  · intro j hj
    have h_pos : 0 < (Icc 1 n).prod (fun k => Nat.gcd j k) := by
      apply prod_pos
      intro k hk
      rw [mem_Icc] at hj hk
      exact Nat.gcd_pos_of_pos_left k hj.1
    exact h_pos.ne'


lemma sum_mul_div_le (M : ℕ) : ∑ k ∈ Icc 1 M, k * (M / k) ≤ M ^ 2 := by
  have h1 : ∀ k ∈ Icc 1 M, k * (M / k) ≤ M := by
    intro k _
    exact Nat.mul_div_le M k
  have h2 : ∑ k ∈ Icc 1 M, k * (M / k) ≤ ∑ k ∈ Icc 1 M, M := sum_le_sum h1
  rw [sum_const, card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h2
  rw [sq]
  exact h2

lemma div_div_comm (n k p : ℕ) : (n / k) / p = (n / p) / k := by
  by_cases hk : k = 0
  · subst hk; simp
  · by_cases hp : p = 0
    · subst hp; simp
    · rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]



theorem den_dvd_num (n : ℕ) : den n ∣ num n := by
  by_cases hn : n = 0
  · subst hn; simp [den, num]
  · have hden : den n ≠ 0 := (den_pos n).ne'
    have hnum : num n ≠ 0 := (num_pos n).ne'
    rw [← factorization_prime_le_iff_dvd hden hnum]
    intro p hp
    let b := log p n + 1
    have h_log : log p n < b := lt_add_one (log p n)
    rw [den_factorization n p hp, num_factorization n p hp]
    have h_factorial : ∀ k ∈ Icc 1 n, (factorial (n / k)).factorization p = ∑ i ∈ Ico 1 b, (n / k) / p ^ i := by
      intro k hk
      rw [mem_Icc] at hk
      have h_le : n / k ≤ n := Nat.div_le_self n k
      have h_log_le : log p (n / k) ≤ log p n := Nat.log_mono_right h_le
      have h_lt : log p (n / k) < b := h_log_le.trans_lt h_log
      exact factorization_factorial hp h_lt
    have h_den_eq : ∑ k ∈ Icc 1 n, k * (factorial (n / k)).factorization p =
                     ∑ k ∈ Icc 1 n, k * ∑ i ∈ Ico 1 b, (n / k) / p ^ i := by
      refine sum_congr rfl fun k hk => congr_arg (fun x => k * x) (h_factorial k hk)
    rw [h_den_eq]
    have h_den_swap : ∑ k ∈ Icc 1 n, k * ∑ i ∈ Ico 1 b, (n / k) / p ^ i =
                      ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 n, k * ((n / k) / p ^ i) := by
      simp_rw [mul_sum]
      refine (sum_congr rfl fun k hk => rfl).trans sum_comm
    rw [h_den_swap]
    have h_lt_b : ∀ j ∈ Icc 1 n, j.factorization p < b := by
      intro j hj
      rw [mem_Icc] at hj
      by_contra! h_ge
      have hj0 : j ≠ 0 := by omega
      have hpb : p ^ b ∣ j := (hp.pow_dvd_iff_le_factorization hj0).mpr h_ge
      have h_le : p ^ b ≤ j := Nat.le_of_dvd hj.1 hpb
      have hj_lt : j < p ^ b := by
        calc j ≤ n := hj.2
             _ < p ^ (log p n).succ := Nat.lt_pow_succ_log_self hp.one_lt n
      omega
    have h_sum_min : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 n, min (j.factorization p) (k.factorization p) =
                     ∑ i ∈ Ico 1 b, if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0 := by
      intro j hj k hk
      rw [mem_Icc] at hj hk
      have hj0 : j ≠ 0 := by omega
      have hk0 : k ≠ 0 := by omega
      have h_iff : ∀ i, (p ^ i ∣ j ∧ p ^ i ∣ k) ↔ i ≤ min (j.factorization p) (k.factorization p) := by
        intro i
        rw [hp.pow_dvd_iff_le_factorization hj0, hp.pow_dvd_iff_le_factorization hk0, le_min_iff]
      simp_rw [h_iff]
      generalize h_M : min (j.factorization p) (k.factorization p) = M
      have h_lt : M < b := by
        rw [← h_M]
        have hj_lt : j.factorization p < b := by
          have hj_mem : j ∈ Icc 1 n := by rw [mem_Icc]; exact ⟨by omega, by omega⟩
          exact h_lt_b j hj_mem
        exact (min_le_left _ _).trans_lt hj_lt
      have h_sum_split : ∑ i ∈ Ico 1 b, (if i ≤ M then 1 else 0) =
                         ∑ i ∈ Ico 1 (M + 1), (if i ≤ M then 1 else 0) + ∑ i ∈ Ico (M + 1) b, (if i ≤ M then 1 else 0) := by
        rw [sum_Ico_consecutive]
        · exact Nat.le_add_left 1 M
        · exact Nat.succ_le_of_lt h_lt
      have h_sum1 : ∑ i ∈ Ico 1 (M + 1), (if i ≤ M then 1 else 0) = M := by
        have h_eq : ∀ i ∈ Ico 1 (M + 1), (if i ≤ M then 1 else 0) = 1 := by
          intro i hi
          rw [mem_Ico] at hi
          have : i ≤ M := by omega
          simp [this]
        rw [sum_congr rfl h_eq, sum_const, card_Ico, nsmul_eq_mul, mul_one]
        exact Nat.add_sub_cancel M 1
      have h_sum2 : ∑ i ∈ Ico (M + 1) b, (if i ≤ M then 1 else 0) = 0 := by
        have h_eq : ∀ i ∈ Ico (M + 1) b, (if i ≤ M then 1 else 0) = 0 := by
          intro i hi
          rw [mem_Ico] at hi
          have : ¬ (i ≤ M) := by omega
          simp [this]
        rw [sum_congr rfl h_eq, sum_const_zero]
      rw [h_sum_split, h_sum1, h_sum2, add_zero]
    have h_gcd_eq : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 n, (Nat.gcd j k).factorization p = min (j.factorization p) (k.factorization p) := by
      intro j hj k hk
      rw [mem_Icc] at hj hk
      have hj0 : j ≠ 0 := by omega
      have hk0 : k ≠ 0 := by omega
      rw [factorization_gcd hj0 hk0, Finsupp.inf_apply]
    have h_Ioc_eq : Ioc 0 n = Icc 1 n := by
      ext x
      simp [mem_Ioc, mem_Icc]
      omega
    have h_sum_boole : ∀ i, ∑ j ∈ Icc 1 n, (if p ^ i ∣ j then 1 else 0) = n / p ^ i := by
      intro i
      rw [sum_boole]
      rw [← h_Ioc_eq]
      exact Ioc_filter_dvd_card_eq_div n (p ^ i)
    have h_if_mul : ∀ j k i, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) = (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0) := by
      intro j k i
      by_cases hj : p ^ i ∣ j <;> by_cases hk : p ^ i ∣ k <;> simp [hj, hk]
    have h_num_prod : ∀ i, ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) =
                           (∑ j ∈ Icc 1 n, if p ^ i ∣ j then 1 else 0) ^ 2 := by
      intro i
      simp_rw [h_if_mul]
      simp_rw [← mul_sum, ← sum_mul]
      rw [sq]
    have h_num_eq : (num n).factorization p = ∑ i ∈ Ico 1 b, (n / p ^ i) ^ 2 := by
      rw [num_factorization n p hp]
      have h_gcd_congr : ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (Nat.gcd j k).factorization p =
                         ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, ∑ i ∈ Ico 1 b, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) := by
        refine sum_congr rfl fun j hj => sum_congr rfl fun k hk => by
          rw [h_gcd_eq j hj k hk, h_sum_min j hj k hk]
      rw [h_gcd_congr]
      have h_swap1 : ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, ∑ i ∈ Ico 1 b, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) =
                     ∑ j ∈ Icc 1 n, ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 n, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) := by
        refine sum_congr rfl fun j hj => sum_comm
      have h_swap2 : ∑ j ∈ Icc 1 n, ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 n, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) =
                     ∑ i ∈ Ico 1 b, ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) := sum_comm
      rw [h_swap1, h_swap2]
      have h_inner : ∀ i, ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (if (p ^ i ∣ j ∧ p ^ i ∣ k) then 1 else 0) = (n / p ^ i) ^ 2 := by
        intro i
        rw [h_num_prod i, h_sum_boole i]
      refine sum_congr rfl fun i hi => h_inner i
    rw [← num_factorization n p hp]
    rw [h_num_eq]
    have h_term_le : ∀ i ∈ Ico 1 b, ∑ k ∈ Icc 1 n, k * ((n / k) / p ^ i) ≤ (n / p ^ i) ^ 2 := by
      intro i hi
      have h_div_comm : ∀ k ∈ Icc 1 n, (n / k) / p ^ i = (n / p ^ i) / k := by
        intro k hk
        exact div_div_comm n k (p ^ i)
      have h_rw : ∑ k ∈ Icc 1 n, k * ((n / k) / p ^ i) = ∑ k ∈ Icc 1 n, k * ((n / p ^ i) / k) := by
        apply sum_congr rfl
        intro k hk
        rw [h_div_comm k hk]
      rw [h_rw]
      generalize hM_eq : n / p ^ i = M
      by_cases hM : M = 0
      · subst hM
        have h_zero : ∀ k ∈ Icc 1 n, k * (0 / k) = 0 := by
          intro k hk
          rw [Nat.zero_div, mul_zero]
        rw [sum_congr rfl h_zero, sum_const_zero]
        simp
      · have hMn : M ≤ n := by
          rw [← hM_eq]
          exact Nat.div_le_self n (p ^ i)
        have h_sum_split : ∑ k ∈ Ico 1 (n + 1), k * (M / k) =
                           ∑ k ∈ Ico 1 (M + 1), k * (M / k) + ∑ k ∈ Ico (M + 1) (n + 1), k * (M / k) := by
          rw [sum_Ico_consecutive]
          · omega
          · omega
        have h_Icc_n : Icc 1 n = Ico 1 (n + 1) := (Ico_succ_right_eq_Icc 1 n).symm
        have h_Icc_M : Icc 1 M = Ico 1 (M + 1) := (Ico_succ_right_eq_Icc 1 M).symm
        have h_split_rw : ∑ k ∈ Icc 1 n, k * (M / k) = ∑ k ∈ Icc 1 M, k * (M / k) + ∑ k ∈ Ico (M + 1) (n + 1), k * (M / k) := by
          rw [h_Icc_n, h_sum_split, ← h_Icc_M]
        rw [h_split_rw]
        have h_zero : ∀ k ∈ Ico (M + 1) (n + 1), k * (M / k) = 0 := by
          intro k hk
          rw [mem_Ico] at hk
          have : M / k = 0 := Nat.div_eq_of_lt hk.1
          rw [this, mul_zero]
        rw [sum_congr rfl h_zero, sum_const_zero, add_zero]
        exact sum_mul_div_le M
    have h_final_le : ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 n, k * ((n / k) / p ^ i) ≤ ∑ i ∈ Ico 1 b, (n / p ^ i) ^ 2 := by
      apply sum_le_sum
      intro i hi
      exact h_term_le i hi
    exact h_final_le


lemma den_step_eq (m p : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m + 1) :
    (den (m + 1)).factorization p = (den m).factorization p := by
  by_cases hm0 : m = 0
  · subst hm0; simp [den]
  · let b := log p (m + 1) + 1
    have h_log : log p (m + 1) < b := lt_add_one (log p (m + 1))
    rw [den_factorization (m + 1) p hp, den_factorization m p hp]
    have h_Icc_succ : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      have h_le : 1 ≤ m + 1 := by omega
      exact Ico_succ_right_eq_insert_Ico h_le
    rw [h_Icc_succ]
    have h_notMem : m + 1 ∉ Icc 1 m := by
      rw [mem_Icc]
      omega
    rw [sum_insert h_notMem]
    have h_term_zero : (m + 1) * (factorial ((m + 1) / (m + 1))).factorization p = 0 := by
      have : (m + 1) / (m + 1) = 1 := Nat.div_self (by omega)
      rw [this]
      simp [factorization_one]
    rw [h_term_zero, zero_add]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    have h_lt1 : log p ((m + 1) / k) < b := by
      have h_div_le : (m + 1) / k ≤ m + 1 := Nat.div_le_self (m + 1) k
      have h_log_le : log p ((m + 1) / k) ≤ log p (m + 1) := Nat.log_mono_right h_div_le
      exact h_log_le.trans_lt h_log
    have h_lt2 : log p (m / k) < b := by
      have h_div_le : m / k ≤ m + 1 := (Nat.div_le_self m k).trans (by omega)
      have h_log_le : log p (m / k) ≤ log p (m + 1) := Nat.log_mono_right h_div_le
      exact h_log_le.trans_lt h_log
    rw [factorization_factorial hp h_lt1, factorization_factorial hp h_lt2]
    have h_div_eq : ∀ i ∈ Ico 1 b, ((m + 1) / k) / p ^ i = (m / k) / p ^ i := by
      intro i hi
      rw [mem_Ico] at hi
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      apply Nat.succ_div_of_not_dvd
      by_contra h_dvd
      have hp_dvd_mul : p ∣ k * p ^ i := by
        have : p ∣ p ^ i := dvd_pow_self p (by omega)
        exact dvd_mul_of_dvd_right this k
      have hp_dvd : p ∣ m + 1 := dvd_trans hp_dvd_mul h_dvd
      exact hm hp_dvd
    have h_sum_eq : ∑ i ∈ Ico 1 b, ((m + 1) / k) / p ^ i = ∑ i ∈ Ico 1 b, (m / k) / p ^ i := sum_congr rfl h_div_eq
    rw [h_sum_eq]

lemma num_step_eq (m p : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m + 1) :
    (num (m + 1)).factorization p = (num m).factorization p := by
  rw [num_factorization (m + 1) p hp, num_factorization m p hp]
  have h_Icc_succ : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
    have h_le : 1 ≤ m + 1 := by omega
    exact Ico_succ_right_eq_insert_Ico h_le
  rw [h_Icc_succ]
  have h_notMem : m + 1 ∉ Icc 1 m := by
    rw [mem_Icc]
    omega
  nth_rw 1 [sum_insert h_notMem]
  have h_inner : ∀ j ∈ Icc 1 m, ∑ k ∈ insert (m + 1) (Icc 1 m), (Nat.gcd j k).factorization p =
                                ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization p := by
    intro j hj
    rw [sum_insert h_notMem]
    have h_zero : (Nat.gcd j (m + 1)).factorization p = 0 := by
      apply factorization_eq_zero_of_not_dvd
      by_contra h_dvd
      have hdvd1 : Nat.gcd j (m + 1) ∣ m + 1 := Nat.gcd_dvd_right j (m + 1)
      have hp_dvd : p ∣ m + 1 := dvd_trans h_dvd hdvd1
      exact hm hp_dvd
    rw [h_zero, zero_add]
  have h_inner_sum : ∑ j ∈ Icc 1 m, ∑ k ∈ insert (m + 1) (Icc 1 m), (Nat.gcd j k).factorization p =
                     ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization p := sum_congr rfl h_inner
  rw [h_inner_sum]
  have h_first : ∑ k ∈ insert (m + 1) (Icc 1 m), (Nat.gcd (m + 1) k).factorization p = 0 := by
    rw [sum_insert h_notMem]
    have h_zero1 : (Nat.gcd (m + 1) (m + 1)).factorization p = 0 := by
      rw [Nat.gcd_self]
      apply factorization_eq_zero_of_not_dvd hm
    have h_zero2 : ∀ k ∈ Icc 1 m, (Nat.gcd (m + 1) k).factorization p = 0 := by
      intro k hk
      apply factorization_eq_zero_of_not_dvd
      by_contra h_dvd
      have hdvd1 : Nat.gcd (m + 1) k ∣ m + 1 := Nat.gcd_dvd_left (m + 1) k
      have hp_dvd : p ∣ m + 1 := dvd_trans h_dvd hdvd1
      exact hm hp_dvd
    rw [h_zero1, sum_congr rfl h_zero2, sum_const_zero, add_zero]
  rw [h_first, zero_add]

lemma a_step_eq (m p : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m + 1) :
    (a (m + 1)).factorization p = (a m).factorization p := by
  have h_a : ∀ x, (a x).factorization p = (num x).factorization p - (den x).factorization p := by
    intro x
    unfold a
    change (num x / den x).factorization p = (num x).factorization p - (den x).factorization p
    rw [factorization_div (den_dvd_num x), Finsupp.tsub_apply]
  rw [h_a (m + 1), h_a m]
  rw [num_step_eq m p hp hm, den_step_eq m p hp hm]

-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  have _ := hn
  generalize hk_eq : k = K
  have h_K : K < p := by rw [← hk_eq]; exact hk
  clear hk hk_eq k
  induction K with
  | zero =>
    rw [add_zero]
  | succ K ih =>
    have h_lt : K < p := by omega
    have h_eq : (a (n * p)).factorization p = (a (n * p + K)).factorization p := ih h_lt
    rw [h_eq]
    rw [← add_assoc]
    rw [a_step_eq (n * p + K) p hp]
    intro hdvd
    have hp_dvd_mul : p ∣ n * p := dvd_mul_left p n
    have hdvd_add : p ∣ n * p + (K + 1) := hdvd
    have hdvd_k : p ∣ K + 1 := (Nat.dvd_add_right hp_dvd_mul).mp hdvd_add
    have h_le : p ≤ K + 1 := Nat.le_of_dvd (by omega) hdvd_k
    omega


