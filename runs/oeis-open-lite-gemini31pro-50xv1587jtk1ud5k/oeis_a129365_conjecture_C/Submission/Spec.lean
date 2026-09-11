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

def num (m : ℕ) : ℕ := (Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k
def den (m : ℕ) : ℕ := (Icc 1 m).prod fun k => (m / k).factorial ^ k

lemma a_eq_num_div_den (m : ℕ) : a m = num m / den m := rfl

lemma count_multiples (m d : ℕ) :
    (∑ j ∈ Icc 1 m, if d ∣ j then (1 : ℕ) else 0) = m / d := by
  if hd : d = 0 then
    subst hd
    simp
  else
    have hd_pos : d > 0 := Nat.pos_of_ne_zero hd
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_Icc_succ_top (by omega)]
      rw [ih]
      by_cases hd_dvd : d ∣ (m + 1)
      · rw [if_pos hd_dvd]
        exact (Nat.succ_div_of_dvd hd_dvd).symm
      · rw [if_neg hd_dvd]
        rw [add_zero]
        exact (Nat.succ_div_of_not_dvd hd_dvd).symm

lemma sum_and_eq_mul (m d : ℕ) :
    (∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, if d ∣ j ∧ d ∣ k then (1 : ℕ) else 0) =
    (m / d) ^ 2 := by
  have H : ∀ j ∈ Icc 1 m, (∑ k ∈ Icc 1 m, if d ∣ j ∧ d ∣ k then (1 : ℕ) else 0) =
      if d ∣ j then m / d else 0 := by
    intro j hj
    if hdj : d ∣ j then
      rw [if_pos hdj]
      have : ∀ k ∈ Icc 1 m, (if d ∣ j ∧ d ∣ k then (1 : ℕ) else 0) = if d ∣ k then 1 else 0 := by
        intro k hk
        simp [hdj]
      rw [sum_congr rfl this]
      exact count_multiples m d
    else
      rw [if_neg hdj]
      have : ∀ k ∈ Icc 1 m, (if d ∣ j ∧ d ∣ k then (1 : ℕ) else 0) = 0 := by
        intro k hk
        simp [hdj]
      rw [sum_congr rfl this, sum_const_zero]
  rw [sum_congr rfl H]
  have H2 : ∀ j ∈ Icc 1 m, (if d ∣ j then m / d else 0) = (if d ∣ j then (1 : ℕ) else 0) * (m / d) := by
    intro j hj
    split_ifs <;> simp
  rw [sum_congr rfl H2, ← sum_mul]
  rw [count_multiples, sq]

lemma fac_eq_sum_Icc (a_val q m : ℕ) (ha : a_val ≠ 0) (hq : q.Prime) (ham : a_val ≤ m) :
    a_val.factorization q = ∑ i ∈ Icc 1 m, if q ^ i ∣ a_val then 1 else 0 := by
  let e := a_val.factorization q
  have h_le : e ≤ m := by
    calc e ≤ q ^ e := le_of_lt (Nat.lt_pow_self hq.one_lt)
         _ ≤ a_val := by
           have hdvd : q ^ e ∣ a_val := (hq.pow_dvd_iff_le_factorization ha).mpr (le_refl e)
           exact Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hdvd
         _ ≤ m := ham
  have H : Icc 1 m = Icc 1 e ∪ Icc (e + 1) m := by
    ext x
    simp only [mem_union, mem_Icc]
    omega
  have H_disj : Disjoint (Icc 1 e) (Icc (e + 1) m) := by
    rw [disjoint_iff_ne]
    intro x hx y hy
    rw [mem_Icc] at hx hy
    omega
  rw [H, sum_union H_disj]
  have sum1 : (∑ i ∈ Icc 1 e, if q ^ i ∣ a_val then 1 else 0) = e := by
    have : ∀ i ∈ Icc 1 e, (if q ^ i ∣ a_val then 1 else 0) = 1 := by
      intro i hi
      rw [mem_Icc] at hi
      rw [if_pos]
      exact (hq.pow_dvd_iff_le_factorization ha).mpr hi.2
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul, mul_one]
  have sum2 : (∑ i ∈ Icc (e + 1) m, if q ^ i ∣ a_val then 1 else 0) = 0 := by
    have : ∀ i ∈ Icc (e + 1) m, (if q ^ i ∣ a_val then 1 else 0) = 0 := by
      intro i hi
      rw [mem_Icc] at hi
      rw [if_neg]
      intro hdvd
      have := (hq.pow_dvd_iff_le_factorization ha).mp hdvd
      omega
    rw [sum_congr rfl this, sum_const_zero]
  rw [sum1, sum2, add_zero]

lemma num_factorization (m q : ℕ) :
    (num m).factorization q = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization q := by
  have h1 : ∀ j ∈ Icc 1 m, (Icc 1 m).prod (fun k => Nat.gcd j k) ≠ 0 := by
    intro j hj
    apply prod_ne_zero_iff.mpr
    intro k hk
    have : j ≠ 0 := by
      rw [mem_Icc] at hj
      omega
    exact Nat.gcd_ne_zero_left this
  have h2 : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := by
    intro j hj k hk
    have : j ≠ 0 := by
      rw [mem_Icc] at hj
      omega
    exact Nat.gcd_ne_zero_left this
  unfold num
  rw [Nat.factorization_prod h1]
  simp_rw [Finsupp.finset_sum_apply]
  apply sum_congr rfl
  intro j hj
  rw [Nat.factorization_prod (h2 j hj)]
  simp_rw [Finsupp.finset_sum_apply]

lemma den_factorization (m q : ℕ) :
    (den m).factorization q = ∑ k ∈ Icc 1 m, k * (m / k).factorial.factorization q := by
  have h1 : ∀ k ∈ Icc 1 m, (m / k).factorial ^ k ≠ 0 := by
    intro k hk
    apply pow_ne_zero
    exact factorial_ne_zero _
  unfold den
  rw [Nat.factorization_prod h1]
  simp_rw [Finsupp.finset_sum_apply]
  apply sum_congr rfl
  intro k hk
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

lemma gcd_fac_eq_sum_Icc (j k q m : ℕ) (hj : j ∈ Icc 1 m) (hq : q.Prime) :
    (Nat.gcd j k).factorization q = ∑ i ∈ Icc 1 m, if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
  have hj0 : j ≠ 0 := by
    rw [mem_Icc] at hj
    omega
  have hgcd0 : Nat.gcd j k ≠ 0 := Nat.gcd_ne_zero_left hj0
  have hgcdm : Nat.gcd j k ≤ m := by
    calc Nat.gcd j k ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) (Nat.gcd_dvd_left j k)
         _ ≤ m := by
           rw [mem_Icc] at hj
           exact hj.2
  rw [fac_eq_sum_Icc _ q m hgcd0 hq hgcdm]
  apply sum_congr rfl
  intro i hi
  have : q ^ i ∣ Nat.gcd j k ↔ q ^ i ∣ j ∧ q ^ i ∣ k := Nat.dvd_gcd_iff
  if h : q ^ i ∣ Nat.gcd j k then
    rw [if_pos h, if_pos (this.mp h)]
  else
    rw [if_neg h, if_neg (this.not.mp h)]

lemma V1_eq (m q : ℕ) (hq : q.Prime) :
    (∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization q) =
    ∑ i ∈ Icc 1 m, (m / q ^ i) ^ 2 := by
  have H : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, (Nat.gcd j k).factorization q =
      ∑ i ∈ Icc 1 m, if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
    intro j hj k hk
    exact gcd_fac_eq_sum_Icc j k q m hj hq
  have sum_eq : (∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization q) =
      ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, ∑ i ∈ Icc 1 m, if q ^ i ∣ j ∧ q ^ i ∣ k then (1 : ℕ) else 0 := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro k hk
    exact H j hj k hk
  rw [sum_eq]
  have h_swap : (∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, ∑ i ∈ Icc 1 m, if q ^ i ∣ j ∧ q ^ i ∣ k then (1 : ℕ) else 0) =
      ∑ i ∈ Icc 1 m, ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, if q ^ i ∣ j ∧ q ^ i ∣ k then (1 : ℕ) else 0 := by
    have H1 : (∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, ∑ i ∈ Icc 1 m, if q ^ i ∣ j ∧ q ^ i ∣ k then (1 : ℕ) else 0) =
           ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, ∑ k ∈ Icc 1 m, if q ^ i ∣ j ∧ q ^ i ∣ k then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro j hj
      exact sum_comm
    rw [H1]
    exact sum_comm
  rw [h_swap]
  apply sum_congr rfl
  intro i hi
  exact sum_and_eq_mul m (q ^ i)

lemma Ico_eq_Icc (m : ℕ) : Ico 1 (m + 1) = Icc 1 m := by
  ext x
  simp only [mem_Ico, mem_Icc]
  omega

lemma V2_eq (m q : ℕ) (hq : q.Prime) :
    (∑ k ∈ Icc 1 m, k * (m / k).factorial.factorization q) =
    ∑ i ∈ Icc 1 m, ∑ k ∈ Icc 1 m, k * (m / (k * q ^ i)) := by
  have H : ∀ k ∈ Icc 1 m, (m / k).factorial.factorization q = ∑ i ∈ Icc 1 m, (m / k) / q ^ i := by
    intro k hk
    have : (m / k).factorial.factorization q = ∑ i ∈ Ico 1 (m + 1), (m / k) / q ^ i := by
      apply Nat.factorization_factorial hq
      have : m / k ≤ m := Nat.div_le_self m k
      have : log q (m / k) ≤ m / k := Nat.log_le_self q (m / k)
      omega
    rw [this, Ico_eq_Icc]
  have H2 : (∑ k ∈ Icc 1 m, k * (m / k).factorial.factorization q) =
      ∑ k ∈ Icc 1 m, ∑ i ∈ Icc 1 m, k * ((m / k) / q ^ i) := by
    apply sum_congr rfl
    intro k hk
    rw [H k hk, mul_sum]
  rw [H2, sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro k hk
  have : (m / k) / q ^ i = m / (k * q ^ i) := by
    rw [Nat.div_div_eq_div_mul]
  rw [this]

lemma sum_k_mul_div_le (N m : ℕ) : (∑ k ∈ Icc 1 m, k * (N / k)) ≤ N ^ 2 := by
  calc
    (∑ k ∈ Icc 1 m, k * (N / k))
      ≤ ∑ k ∈ Icc 1 m, if k ≤ N then N else 0 := by
        apply sum_le_sum
        intro k hk
        split_ifs with h
        · exact Nat.mul_div_le N k
        · rw [Nat.div_eq_of_lt (not_le.mp h), mul_zero]
    _ = ∑ k ∈ (Icc 1 m).filter (· ≤ N), N := by
        rw [sum_filter]
    _ ≤ ∑ k ∈ Icc 1 N, N := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro x hx
          rw [mem_filter, mem_Icc] at hx
          rw [mem_Icc]
          exact ⟨hx.1.1, hx.2⟩
        · intro _ _ _
          exact Nat.zero_le _
    _ = N * N := by
        simp [add_tsub_cancel_right]
    _ = N ^ 2 := by rw [sq]

lemma V2_le_V1 (m q : ℕ) (hq : q.Prime) :
    (∑ k ∈ Icc 1 m, k * (m / k).factorial.factorization q) ≤
    (∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization q) := by
  rw [V1_eq m q hq, V2_eq m q hq]
  apply sum_le_sum
  intro i hi
  have : ∀ k ∈ Icc 1 m, k * (m / (k * q ^ i)) = k * ((m / q ^ i) / k) := by
    intro k hk
    rw [mul_comm k (q^i), ← Nat.div_div_eq_div_mul]
  rw [sum_congr rfl this]
  exact sum_k_mul_div_le (m / q ^ i) m

lemma den_dvd_num (m : ℕ) : den m ∣ num m := by
  have Hnum : num m ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j hj
    apply prod_ne_zero_iff.mpr
    intro k hk
    have : j ≠ 0 := by
      rw [mem_Icc] at hj
      omega
    exact Nat.gcd_ne_zero_left this
  have Hden : den m ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro k hk
    apply pow_ne_zero
    exact factorial_ne_zero _
  apply (Nat.factorization_le_iff_dvd Hden Hnum).mp
  intro q
  if hq : q.Prime then
    rw [num_factorization m q, den_factorization m q]
    exact V2_le_V1 m q hq
  else
    have Hnum0 : (num m).factorization q = 0 := Nat.factorization_eq_zero_of_not_prime _ hq
    have Hden0 : (den m).factorization q = 0 := Nat.factorization_eq_zero_of_not_prime _ hq
    rw [Hnum0, Hden0]

lemma a_fac_eq (m p : ℕ) :
    (a m).factorization p = (num m).factorization p - (den m).factorization p := by
  have hdvd : den m ∣ num m := den_dvd_num m
  rw [a_eq_num_div_den, Nat.factorization_div hdvd]
  rfl

lemma div_eq_of_not_dvd {M p i : ℕ} (hi : 1 ≤ i) (h : ¬ p ∣ M) (hM : 0 < M) :
    M / p ^ i = (M - 1) / p ^ i := by
  have hdvd : ¬ (p ^ i ∣ M) := by
    intro h_dvd
    have h1 : p ^ 1 ∣ p ^ i := Nat.pow_dvd_pow p hi
    rw [pow_one] at h1
    exact h (Nat.dvd_trans h1 h_dvd)
  by_contra h_ne
  have h_ne2 : (M - 1) / p ^ i ≠ M / p ^ i := ne_comm.mp h_ne
  have hM_eq : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have hdvd2 : ¬ (p ^ i ∣ (M - 1) + 1) := by
    rw [hM_eq]
    exact hdvd
  have H := Nat.succ_div_of_not_dvd hdvd2
  rw [hM_eq] at H
  exact h_ne2 H.symm

lemma V1_eq_of_not_dvd {M p : ℕ} (hp : p.Prime) (h : ¬ p ∣ M) (hM : 0 < M) :
    (∑ i ∈ Icc 1 M, (M / p ^ i) ^ 2) = (∑ i ∈ Icc 1 (M - 1), ((M - 1) / p ^ i) ^ 2) := by
  have H : ∀ i ∈ Icc 1 M, M / p ^ i = (M - 1) / p ^ i := by
    intro i hi
    rw [mem_Icc] at hi
    exact div_eq_of_not_dvd hi.1 h hM
  have h_eq : (∑ i ∈ Icc 1 M, (M / p ^ i) ^ 2) = ∑ i ∈ Icc 1 M, ((M - 1) / p ^ i) ^ 2 := by
    apply sum_congr rfl
    intro i hi
    rw [H i hi]
  rw [h_eq]
  have H_M : ((M - 1) / p ^ M) ^ 2 = 0 := by
    have : M - 1 < p ^ M := by
      calc M - 1 ≤ M := Nat.sub_le M 1
           _ < p ^ M := Nat.lt_pow_self hp.one_lt
    rw [Nat.div_eq_of_lt this, zero_pow]
    omega
  have H_succ : M = (M - 1) + 1 := (Nat.sub_add_cancel hM).symm
  have : (∑ i ∈ Icc 1 M, ((M - 1) / p ^ i) ^ 2) = ∑ i ∈ Icc 1 ((M - 1) + 1), ((M - 1) / p ^ i) ^ 2 := by
    congr 1
    congr 1
  rw [this, sum_Icc_succ_top (by omega)]
  have h_term : ((M - 1) / p ^ (M - 1 + 1)) ^ 2 = 0 := by
    rw [← H_succ, H_M]
  rw [h_term, add_zero]

lemma div_mul_eq_of_not_dvd {M p i k : ℕ} (hi : 1 ≤ i) (h : ¬ p ∣ M) (hM : 0 < M) :
    M / (k * p ^ i) = (M - 1) / (k * p ^ i) := by
  if hk0 : k = 0 then
    subst hk0
    simp
  else
    have hdvd : ¬ (k * p ^ i ∣ M) := by
      intro h_dvd
      have h1 : p ^ i ∣ k * p ^ i := dvd_mul_left (p ^ i) k
      have h2 : p ^ i ∣ M := Nat.dvd_trans h1 h_dvd
      have h3 : p ^ 1 ∣ p ^ i := Nat.pow_dvd_pow p hi
      rw [pow_one] at h3
      have h4 : p ∣ M := Nat.dvd_trans h3 h2
      exact h h4
    by_contra h_ne
    have h_ne2 : (M - 1) / (k * p ^ i) ≠ M / (k * p ^ i) := ne_comm.mp h_ne
    have hM_eq : M - 1 + 1 = M := Nat.sub_add_cancel hM
    have hdvd2 : ¬ (k * p ^ i ∣ (M - 1) + 1) := by
      rw [hM_eq]
      exact hdvd
    have H := Nat.succ_div_of_not_dvd hdvd2
    rw [hM_eq] at H
    exact h_ne2 H.symm

lemma V2_eq_of_not_dvd_bounds (M p : ℕ) (hp : p.Prime) (hM : 0 < M) :
    (∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 M, k * ((M - 1) / (k * p ^ i))) =
    (∑ i ∈ Icc 1 (M - 1), ∑ k ∈ Icc 1 (M - 1), k * ((M - 1) / (k * p ^ i))) := by
  have H_succ : M = (M - 1) + 1 := (Nat.sub_add_cancel hM).symm
  have H_eq1 : (∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 M, k * ((M - 1) / (k * p ^ i))) =
      ∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 ((M - 1) + 1), k * ((M - 1) / (k * p ^ i)) := by
    congr 2
    ext i
    congr 1
    congr 1
  rw [H_eq1]
  have H_inner : ∀ i ∈ Icc 1 M, (∑ k ∈ Icc 1 ((M - 1) + 1), k * ((M - 1) / (k * p ^ i))) =
      ∑ k ∈ Icc 1 (M - 1), k * ((M - 1) / (k * p ^ i)) := by
    intro i hi
    rw [sum_Icc_succ_top (by omega)]
    have : ((M - 1) / (M * p ^ i)) = 0 := by
      apply Nat.div_eq_of_lt
      calc M - 1 < M := by omega
           _ ≤ M * p ^ i := Nat.le_mul_of_pos_right _ (pos_iff_ne_zero.mpr (pow_ne_zero i hp.ne_zero))
    rw [← H_succ, this, mul_zero, add_zero]
  have H_eq2 : (∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 ((M - 1) + 1), k * ((M - 1) / (k * p ^ i))) =
      ∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 (M - 1), k * ((M - 1) / (k * p ^ i)) := by
    apply sum_congr rfl H_inner
  rw [H_eq2]
  have H_eq3 : (∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 (M - 1), k * ((M - 1) / (k * p ^ i))) =
      ∑ i ∈ Icc 1 ((M - 1) + 1), ∑ k ∈ Icc 1 (M - 1), k * ((M - 1) / (k * p ^ i)) := by
    congr 1
    congr 1
  rw [H_eq3, sum_Icc_succ_top (by omega)]
  have H_outer : (∑ k ∈ Icc 1 (M - 1), k * ((M - 1) / (k * p ^ M))) = 0 := by
    apply sum_eq_zero
    intro k hk
    have : ((M - 1) / (k * p ^ M)) = 0 := by
      apply Nat.div_eq_of_lt
      calc M - 1 ≤ M := Nat.sub_le M 1
           _ < p ^ M := Nat.lt_pow_self hp.one_lt
           _ ≤ k * p ^ M := Nat.le_mul_of_pos_left _ (by
             rw [mem_Icc] at hk
             omega)
    rw [this, mul_zero]
  rw [← H_succ, H_outer, add_zero]

lemma V2_eq_of_not_dvd {M p : ℕ} (hp : p.Prime) (h : ¬ p ∣ M) (hM : 0 < M) :
    (∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 M, k * (M / (k * p ^ i))) =
    (∑ i ∈ Icc 1 (M - 1), ∑ k ∈ Icc 1 (M - 1), k * ((M - 1) / (k * p ^ i))) := by
  have H : ∀ i ∈ Icc 1 M, ∀ k ∈ Icc 1 M, M / (k * p ^ i) = (M - 1) / (k * p ^ i) := by
    intro i hi k hk
    rw [mem_Icc] at hi
    exact div_mul_eq_of_not_dvd hi.1 h hM
  have h_eq : (∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 M, k * (M / (k * p ^ i))) =
      ∑ i ∈ Icc 1 M, ∑ k ∈ Icc 1 M, k * ((M - 1) / (k * p ^ i)) := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro k hk
    rw [H i hi k hk]
  rw [h_eq]
  exact V2_eq_of_not_dvd_bounds M p hp hM

lemma a_fac_eq_of_not_dvd (M p : ℕ) (hp : p.Prime) (hM : 0 < M) (h : ¬ p ∣ M) :
    (a M).factorization p = (a (M - 1)).factorization p := by
  rw [a_fac_eq M p, a_fac_eq (M - 1) p]
  rw [num_factorization M p, den_factorization M p]
  rw [num_factorization (M - 1) p, den_factorization (M - 1) p]
  rw [V1_eq M p hp, V2_eq M p hp]
  rw [V1_eq (M - 1) p hp, V2_eq (M - 1) p hp]
  rw [V1_eq_of_not_dvd hp h hM]
  rw [V2_eq_of_not_dvd hp h hM]

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
    (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk_lt : k < p := by omega
    have h_not_dvd : ¬ p ∣ (n * p + k + 1) := by
      intro hdvd
      have hdvd2 : p ∣ (k + 1) := by
        have H_add : n * p + (k + 1) = n * p + k + 1 := by omega
        rw [← H_add] at hdvd
        have h_pn : p ∣ n * p := ⟨n, mul_comm n p⟩
        exact (Nat.dvd_add_right h_pn).mp hdvd
      have : p ≤ k + 1 := Nat.le_of_dvd (by omega) hdvd2
      omega
    have H := a_fac_eq_of_not_dvd (n * p + k + 1) p hp (by omega) h_not_dvd
    have h_sub : n * p + k + 1 - 1 = n * p + k := by omega
    rw [h_sub] at H
    have h_add : n * p + (k + 1) = n * p + k + 1 := by omega
    rw [h_add, H]
    exact ih hk_lt

theorem oeis_a129365_conjecture_C.disproof : ¬ (type_of% @oeis_a129365_conjecture_C) := sorry
