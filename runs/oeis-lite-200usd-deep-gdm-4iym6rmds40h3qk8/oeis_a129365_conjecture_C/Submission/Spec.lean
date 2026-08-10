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

lemma log_lt_self_add_one (p n : ℕ) (hp : p.Prime) : log p n < n + 1 := by
  by_cases hn : n = 0
  · subst hn
    rw [log_zero_right]
    exact zero_lt_one
  · have hp1 : 1 < p := hp.one_lt
    rw [log_lt_iff_lt_pow hp1 hn]
    have h_pow : n < 2 ^ (n + 1) := by
      have h1 : n < n + 1 := lt_add_one n
      have h2 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
      exact h1.trans h2
    apply h_pow.trans_le
    exact Nat.pow_le_pow_left hp.two_le (n + 1)

lemma factorization_eq_zero_of_not_dvd {p x : ℕ} (hp : p.Prime) (h : ¬ p ∣ x) : x.factorization p = 0 := by
  by_cases hx : x = 0
  · subst hx; simp
  · by_contra hc
    have h1 : p ∣ x := (hp.dvd_iff_one_le_factorization hx).mpr (Nat.one_le_iff_ne_zero.mpr hc)
    exact h h1

lemma not_dvd_of_mem_Ico (n p k x : ℕ) (hp : p.Prime) (hk : k < p) (hx : x ∈ Ico (n * p + 1) (n * p + k + 1)) : ¬ p ∣ x := by
  rw [mem_Ico] at hx
  intro hd
  rcases hd with ⟨d, rfl⟩
  have hp0 : 0 < p := hp.pos
  have h1 : n * p < d * p := by
    calc
      n * p < n * p + 1 := lt_add_one _
      _ ≤ p * d := hx.1
      _ = d * p := mul_comm _ _
  have h2 : d * p < (n + 1) * p := by
    calc
      d * p = p * d := mul_comm _ _
      _ < n * p + k + 1 := hx.2
      _ ≤ n * p + p := Nat.add_le_add_left hk _
      _ = (n + 1) * p := by ring
  have h1_lt : n < d := (mul_lt_mul_iff_left₀ hp0).mp h1
  have h2_lt : d < n + 1 := (mul_lt_mul_iff_left₀ hp0).mp h2
  omega

lemma div_div_comm (N m q : ℕ) : (N / m) / q = (N / q) / m := by
  by_cases hq : q = 0
  · subst hq; simp
  · by_cases hm : m = 0
    · subst hm; simp
    · rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul]

lemma den_inner_sum_eq (N p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i) :
    ∑ m ∈ Icc 1 N, m * ((N / m) / p ^ i) = ∑ m ∈ Icc 1 (N / p ^ i), m * ((N / p ^ i) / m) := by
  have _ := hi
  have hp_pow_pos : 0 < p ^ i := pow_pos hp.pos _
  have hp_pow : p ^ i ≠ 0 := hp_pow_pos.ne'
  have h_le : N / p ^ i ≤ N := Nat.div_le_self _ _
  have h_split : Icc 1 N = Icc 1 (N / p ^ i) ∪ Ico (N / p ^ i + 1) (N + 1) := by
    have h1 : Icc 1 N = Ico 1 (N + 1) := (Ico_succ_right_eq_Icc 1 N).symm
    have h2 : Icc 1 (N / p ^ i) = Ico 1 (N / p ^ i + 1) := (Ico_succ_right_eq_Icc 1 (N / p ^ i)).symm
    rw [h1, h2]
    have hab : 1 ≤ N / p ^ i + 1 := Nat.succ_pos _
    have hbc : N / p ^ i + 1 ≤ N + 1 := Nat.add_le_add_right h_le _
    rw [← Ico_union_Ico_eq_Ico hab hbc]
  have h_disjoint : Disjoint (Icc 1 (N / p ^ i)) (Ico (N / p ^ i + 1) (N + 1)) := by
    have h2 : Icc 1 (N / p ^ i) = Ico 1 (N / p ^ i + 1) := (Ico_succ_right_eq_Icc 1 (N / p ^ i)).symm
    rw [h2]
    exact Ico_disjoint_Ico_consecutive 1 (N / p ^ i + 1) (N + 1)
  rw [h_split, sum_union h_disjoint]
  have h_zero : ∑ x ∈ Ico (N / p ^ i + 1) (N + 1), x * ((N / x) / p ^ i) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_Ico] at hx
    have hx_gt : N / p ^ i < x := hx.1
    have h_div : (N / x) / p ^ i = 0 := by
      rw [Nat.div_div_eq_div_mul]
      have : N < x * p ^ i := (Nat.div_lt_iff_lt_mul hp_pow_pos).mp hx_gt
      exact Nat.div_eq_of_lt this
    rw [h_div, mul_zero]
  rw [h_zero, add_zero]
  apply sum_congr rfl
  intro x hx
  rw [div_div_comm]

def den (n : ℕ) : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma log_div_lt_self_add_one (p N m : ℕ) (hp : p.Prime) : log p (N / m) < N + 1 := by
  have h1 : N / m ≤ N := Nat.div_le_self _ _
  have h2 : log p (N / m) ≤ log p N := Nat.log_mono_right h1
  have h3 : log p N < N + 1 := log_lt_self_add_one p N hp
  exact h2.trans_lt h3

lemma div_pow_eq_div_pow (n p k i : ℕ) (hp : p.Prime) (hk : k < p) (hi : 1 ≤ i) :
    (n * p + k) / p ^ i = (n * p) / p ^ i := by
  have hi_nz : i ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hi_nz with ⟨j, rfl⟩
  rw [pow_succ, mul_comm (p ^ j) p]
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h_div : (n * p + k) / p = n := by
    rw [add_comm, Nat.add_mul_div_right _ _ hp.pos]
    rw [Nat.div_eq_of_lt hk, zero_add]
  have h_div2 : (n * p) / p = n := by
    rw [mul_comm]
    exact Nat.mul_div_cancel_left _ hp.pos
  rw [h_div, h_div2]

lemma den_factorization_eq_sum (p N : ℕ) (hp : p.Prime) :
    (den N).factorization p = ∑ i ∈ Ico 1 (N + 1), ∑ m ∈ Icc 1 (N / p ^ i), m * ((N / p ^ i) / m) := by
  dsimp [den]
  rw [factorization_prod_apply]
  · simp_rw [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h_rw : ∀ m ∈ Icc 1 N, (factorial (N / m)).factorization p = ∑ i ∈ Ico 1 (N + 1), (N / m) / p ^ i := by
      intro m hm
      exact factorization_factorial hp (log_div_lt_self_add_one p N m hp)
    have h_sum : ∑ m ∈ Icc 1 N, m * (factorial (N / m)).factorization p = ∑ m ∈ Icc 1 N, m * ∑ i ∈ Ico 1 (N + 1), (N / m) / p ^ i := by
      apply sum_congr rfl
      intro m hm
      rw [h_rw m hm]
    rw [h_sum]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [mem_Ico] at hi
    exact den_inner_sum_eq N p i hp hi.1
  · intro m hm
    apply pow_ne_zero
    exact factorial_ne_zero _

lemma helper_pow_gt (n p : ℕ) (hp : p.Prime) : n * p + p ≤ p ^ (n * p + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  by_cases hn : n = 0
  · subst hn
    simp
  · have h1 : n + 1 ≤ 2 ^ n := (Nat.lt_two_pow_self : n < 2 ^ n)
    have h2 : 2 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp2 _
    have h3 : n + 1 ≤ p ^ n := h1.trans h2
    have h4 : (n + 1) * p ≤ p ^ n * p := Nat.mul_le_mul_right p h3
    rw [← pow_succ] at h4
    have h5 : n * p + p = (n + 1) * p := by ring
    rw [h5]
    apply h4.trans
    apply Nat.pow_le_pow_right hp.pos
    have h_np : n + 1 ≤ n * p + 1 := by
      have : n * 1 ≤ n * p := Nat.mul_le_mul_left n (by omega)
      omega
    exact h_np

def num (n : ℕ) : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k

lemma num_factorization_eq (p n : ℕ) :
    (num n).factorization p = ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (Nat.gcd j k).factorization p := by
  dsimp [num]
  rw [factorization_prod_apply]
  · apply sum_congr rfl
    intro j hj
    rw [factorization_prod_apply]
    intro k hk
    rw [mem_Icc] at hj hk
    exact (Nat.gcd_pos_of_pos_left _ hj.1).ne'
  · intro j hj
    apply prod_ne_zero_iff.mpr
    intro k hk
    rw [mem_Icc] at hj hk
    exact (Nat.gcd_pos_of_pos_left _ hj.1).ne'

lemma factorization_gcd_eq_zero_of_zero_left {a b p : ℕ} (ha0 : a ≠ 0) (ha : a.factorization p = 0) :
    (Nat.gcd a b).factorization p = 0 := by
  by_cases hb0 : b = 0
  · subst hb0; simp [ha]
  · rw [factorization_gcd ha0 hb0]
    have : (a.factorization ⊓ b.factorization) p = min (a.factorization p) (b.factorization p) := rfl
    rw [this, ha]
    exact zero_min _

lemma disjoint_Icc_Ico (n p k : ℕ) : Disjoint (Icc 1 (n * p)) (Ico (n * p + 1) (n * p + k + 1)) := by
  have h2 : Icc 1 (n * p) = Ico 1 (n * p + 1) := (Ico_succ_right_eq_Icc 1 (n * p)).symm
  rw [h2]
  exact Ico_disjoint_Ico_consecutive 1 (n * p + 1) (n * p + k + 1)

lemma factorization_eq_zero_of_mem_Ico (n p k x : ℕ) (hp : p.Prime) (hk : k < p) (hx : x ∈ Ico (n * p + 1) (n * p + k + 1)) : x.factorization p = 0 := by
  exact factorization_eq_zero_of_not_dvd hp (not_dvd_of_mem_Ico n p k x hp hk hx)

lemma Icc_split_Ico (n p k : ℕ) : Icc 1 (n * p + k) = Icc 1 (n * p) ∪ Ico (n * p + 1) (n * p + k + 1) := by
  have h1 : Icc 1 (n * p + k) = Ico 1 (n * p + k + 1) := (Ico_succ_right_eq_Icc 1 (n * p + k)).symm
  have h2 : Icc 1 (n * p) = Ico 1 (n * p + 1) := (Ico_succ_right_eq_Icc 1 (n * p)).symm
  rw [h1, h2]
  have hab : 1 ≤ n * p + 1 := by omega
  have hbc : n * p + 1 ≤ n * p + k + 1 := by omega
  rw [← Ico_union_Ico_eq_Ico hab hbc]

lemma num_factorization_eq_of_k_lt (n p k : ℕ) (hp : p.Prime) (hk : k < p) :
    (num (n * p + k)).factorization p = (num (n * p)).factorization p := by
  rw [num_factorization_eq, num_factorization_eq]
  rw [Icc_split_Ico n p k]
  rw [sum_union (disjoint_Icc_Ico n p k)]
  have h_inner_zero : ∑ x ∈ Ico (n * p + 1) (n * p + k + 1), ∑ k_1 ∈ Icc 1 (n * p) ∪ Ico (n * p + 1) (n * p + k + 1), (Nat.gcd x k_1).factorization p = 0 := by
    apply sum_eq_zero
    intro x hx
    apply sum_eq_zero
    intro y hy
    have hx0 : x ≠ 0 := by
      rw [mem_Ico] at hx
      omega
    have hx_zero : x.factorization p = 0 := factorization_eq_zero_of_mem_Ico n p k x hp hk hx
    exact factorization_gcd_eq_zero_of_zero_left hx0 hx_zero
  rw [h_inner_zero, add_zero]
  apply sum_congr rfl
  intro x hx
  rw [sum_union (disjoint_Icc_Ico n p k)]
  have h_inner_zero2 : ∑ y ∈ Ico (n * p + 1) (n * p + k + 1), (Nat.gcd x y).factorization p = 0 := by
    apply sum_eq_zero
    intro y hy
    have hy_zero : y.factorization p = 0 := factorization_eq_zero_of_mem_Ico n p k y hp hk hy
    have hy0 : y ≠ 0 := by
      rw [mem_Ico] at hy
      omega
    rw [Nat.gcd_comm]
    exact factorization_gcd_eq_zero_of_zero_left hy0 hy_zero
  rw [h_inner_zero2, add_zero]

lemma den_factorization_eq_of_k_lt (n p k : ℕ) (hp : p.Prime) (hk : k < p) :
    (den (n * p + k)).factorization p = (den (n * p)).factorization p := by
  have hp0 : 0 < p := hp.pos
  rw [den_factorization_eq_sum p (n * p + k) hp, den_factorization_eq_sum p (n * p) hp]
  have hab : 1 ≤ n * p + 1 := by omega
  have hbc : n * p + 1 ≤ n * p + k + 1 := by omega
  have h_split : Ico 1 (n * p + k + 1) = Ico 1 (n * p + 1) ∪ Ico (n * p + 1) (n * p + k + 1) := by
    rw [← Ico_union_Ico_eq_Ico hab hbc]
  have h_disjoint : Disjoint (Ico 1 (n * p + 1)) (Ico (n * p + 1) (n * p + k + 1)) := by
    exact Ico_disjoint_Ico_consecutive 1 (n * p + 1) (n * p + k + 1)
  rw [h_split, sum_union h_disjoint]
  have h_zero : ∑ i ∈ Ico (n * p + 1) (n * p + k + 1), ∑ m ∈ Icc 1 ((n * p + k) / p ^ i), m * (((n * p + k) / p ^ i) / m) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [mem_Ico] at hi
    have h_pow_gt : n * p + k < p ^ i := by
      calc
        n * p + k < n * p + p := by omega
        _ ≤ p ^ (n * p + 1) := helper_pow_gt n p hp
        _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi.1
    have h_div : (n * p + k) / p ^ i = 0 := Nat.div_eq_of_lt h_pow_gt
    rw [h_div]
    simp
  rw [h_zero, add_zero]
  apply sum_congr rfl
  intro i hi
  rw [mem_Ico] at hi
  rw [div_pow_eq_div_pow n p k i hp hk hi.1]

lemma factorization_eq_sum_iff_dvd (q X N : ℕ) (hq : q.Prime) (hX : X ∈ Icc 1 N) :
    X.factorization q = ∑ i ∈ Ico 1 (N + 1), (if q ^ i ∣ X then 1 else 0) := by
  have hX0 : X ≠ 0 := by
    rw [mem_Icc] at hX
    omega
  have h_le : X.factorization q ≤ N := by
    have h1 : X.factorization q < X := factorization_lt q hX0
    have h2 : X ≤ N := by
      rw [mem_Icc] at hX
      exact hX.2
    omega
  have h_split : Ico 1 (N + 1) = Ico 1 (X.factorization q + 1) ∪ Ico (X.factorization q + 1) (N + 1) := by
    rw [← Ico_union_Ico_eq_Ico]
    · omega
    · omega
  rw [h_split, sum_union]
  · have h1 : ∑ x ∈ Ico 1 (X.factorization q + 1), (if q ^ x ∣ X then 1 else 0) = ∑ x ∈ Ico 1 (X.factorization q + 1), 1 := by
      apply sum_congr rfl
      intro x hx
      rw [mem_Ico] at hx
      have : q ^ x ∣ X := by
        rw [hq.pow_dvd_iff_le_factorization hX0]
        omega
      simp [this]
    have h2 : ∑ x ∈ Ico (X.factorization q + 1) (N + 1), (if q ^ x ∣ X then 1 else 0) = ∑ x ∈ Ico (X.factorization q + 1) (N + 1), 0 := by
      apply sum_congr rfl
      intro x hx
      rw [mem_Ico] at hx
      have : ¬ q ^ x ∣ X := by
        rw [hq.pow_dvd_iff_le_factorization hX0]
        omega
      simp [this]
    rw [h1, h2, sum_const, sum_const, nsmul_eq_mul, mul_one, nsmul_eq_mul, mul_zero, add_zero]
    simp
  · exact Ico_disjoint_Ico_consecutive 1 (X.factorization q + 1) (N + 1)

lemma div_add_if (N m : ℕ) (hm : 0 < m) :
    (N + 1) / m = N / m + (if m ∣ N + 1 then 1 else 0) := by
  by_cases h_dvd : m ∣ N + 1
  · simp [h_dvd]
    rcases h_dvd with ⟨q, hq⟩
    -- N + 1 = m * q
    have hq_pos : 0 < q := by
      by_contra hc
      have : q = 0 := by omega
      subst this
      omega
    have hq_comm : N + 1 = q * m := by
      rw [hq, mul_comm]
    have h_prod : (q - 1) * m + m = q * m := by
      rw [← Nat.succ_mul]
      have : (q - 1).succ = q := Nat.succ_pred hq_pos.ne'
      rw [this]
    have h_N : N = (m - 1) + (q - 1) * m := by
      omega
    have h_div_q : (N + 1) / m = q := by
      rw [hq_comm, Nat.mul_div_cancel _ hm]
    have h_div : N / m = q - 1 := by
      rw [h_N]
      rw [Nat.add_mul_div_right _ _ hm]
      have : m - 1 < m := by omega
      rw [Nat.div_eq_of_lt this, zero_add]
    omega
  · simp [h_dvd]
    -- N + 1 = m * q + r with 0 < r < m
    have h_div_mod := Nat.div_add_mod (N + 1) m
    have h_mod_lt := Nat.mod_lt (N + 1) hm
    have h_mod_ne_zero : (N + 1) % m ≠ 0 := by
      intro hc
      have : m ∣ N + 1 := Nat.dvd_of_mod_eq_zero hc
      exact h_dvd this
    have h_prod : m * ((N + 1) / m) = ((N + 1) / m) * m := mul_comm _ _
    have h_div_mod_comm : ((N + 1) / m) * m + (N + 1) % m = N + 1 := by
      omega
    have h_N : N = ((N + 1) % m - 1) + ((N + 1) / m) * m := by
      omega
    have h_lt : (N + 1) % m - 1 < m := by omega
    have h_div_RHS : N / m = (N + 1) / m := by
      nth_rw 1 [h_N]
      rw [Nat.add_mul_div_right _ _ hm]
      rw [Nat.div_eq_of_lt h_lt, zero_add]
    rw [h_div_RHS]

lemma sum_div_count (N m : ℕ) (hm : 0 < m) :
    ∑ j ∈ Icc 1 N, (if m ∣ j then 1 else 0) = N / m := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    have h_insert : Icc 1 (N + 1) = insert (N + 1) (Icc 1 N) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    have h_not_mem : N + 1 ∉ Icc 1 N := by
      rw [mem_Icc]
      omega
    rw [h_insert, sum_insert h_not_mem]
    rw [ih, add_comm]
    rw [div_add_if N m hm]

lemma num_factorization_eq_sum_pow (q N : ℕ) (hq : q.Prime) :
    (num N).factorization q = ∑ i ∈ Ico 1 (N + 1), (N / q ^ i) ^ 2 := by
  rw [num_factorization_eq]
  have h_rw : ∀ j ∈ Icc 1 N, ∀ k ∈ Icc 1 N,
      (Nat.gcd j k).factorization q = ∑ i ∈ Ico 1 (N + 1), (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) := by
    intro j hj k hk
    have h_gcd : Nat.gcd j k ∈ Icc 1 N := by
      rw [mem_Icc] at hj hk ⊢
      have h1 : 0 < j := hj.1
      have h2 : Nat.gcd j k ∣ j := Nat.gcd_dvd_left j k
      have h3 : Nat.gcd j k ≤ j := Nat.le_of_dvd h1 h2
      have h4 : Nat.gcd j k ≠ 0 := by
        intro hc
        rw [Nat.gcd_eq_zero_iff] at hc
        omega
      omega
    rw [factorization_eq_sum_iff_dvd q (Nat.gcd j k) N hq h_gcd]
    apply sum_congr rfl
    intro i hi
    simp only [dvd_gcd_iff]
  have h_eq : ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (Nat.gcd j k).factorization q =
              ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, ∑ i ∈ Ico 1 (N + 1), (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro k hk
    rw [h_rw j hj k hk]
  rw [h_eq]
  have h_comm1 : (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, ∑ i ∈ Ico 1 (N + 1), (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0)) =
                 (∑ j ∈ Icc 1 N, ∑ i ∈ Ico 1 (N + 1), ∑ k ∈ Icc 1 N, (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0)) := by
    apply sum_congr rfl
    intro j hj
    rw [sum_comm]
  rw [h_comm1]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have h_prod : ∀ j ∈ Icc 1 N, ∀ k ∈ Icc 1 N,
      (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0) = (if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0) := by
    intro j hj k hk
    by_cases hj_dvd : q ^ i ∣ j <;> by_cases hk_dvd : q ^ i ∣ k <;> simp [hj_dvd, hk_dvd]
  have h_eq2 : (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0)) =
               (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0)) := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro k hk
    rw [h_prod j hj k hk]
  rw [h_eq2]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  have hqi : 0 < q ^ i := pow_pos hq.pos _
  rw [sum_div_count N (q ^ i) hqi]
  ring

lemma m_mul_div_le (m M : ℕ) : m * (M / m) ≤ M := by
  rw [mul_comm]
  exact Nat.div_mul_le_self M m

lemma sum_m_div_le (M : ℕ) : ∑ m ∈ Icc 1 M, m * (M / m) ≤ M ^ 2 := by
  by_cases hM : M = 0
  · subst hM; simp
  · have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have h1 : ∑ m ∈ Icc 1 M, m * (M / m) ≤ ∑ m ∈ Icc 1 M, M := by
      apply sum_le_sum
      intro m hm
      exact m_mul_div_le m M
    have h2 : ∑ m ∈ Icc 1 M, M = M ^ 2 := by
      rw [sum_const, card_Icc]
      have : M + 1 - 1 = M := by omega
      rw [this]
      rw [nsmul_eq_mul, sq]
      rfl
    omega

lemma den_ne_zero (N : ℕ) : den N ≠ 0 := by
  dsimp [den]
  apply prod_ne_zero_iff.mpr
  intro k hk
  apply pow_ne_zero
  exact factorial_ne_zero _

lemma num_ne_zero (N : ℕ) : num N ≠ 0 := by
  dsimp [num]
  apply prod_ne_zero_iff.mpr
  intro j hj
  apply prod_ne_zero_iff.mpr
  intro k hk
  rw [mem_Icc] at hj hk
  exact (Nat.gcd_pos_of_pos_left _ hj.1).ne'

lemma den_dvd_num (N : ℕ) : den N ∣ num N := by
  by_cases hN : N = 0
  · subst hN
    simp [den, num]
  · have h_den_nz : den N ≠ 0 := den_ne_zero N
    have h_num_nz : num N ≠ 0 := num_ne_zero N
    rw [← factorization_prime_le_iff_dvd h_den_nz h_num_nz]
    intro q hq
    rw [den_factorization_eq_sum q N hq, num_factorization_eq_sum_pow q N hq]
    apply sum_le_sum
    intro i hi
    exact sum_m_div_le (N / q ^ i)


-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  have _ := hn
  have ha_eq (N : ℕ) : a N = num N / den N := rfl
  rw [ha_eq (n * p), ha_eq (n * p + k)]
  rw [factorization_div (den_dvd_num (n * p))]
  rw [factorization_div (den_dvd_num (n * p + k))]
  rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
  have h_num : (num (n * p + k)).factorization p = (num (n * p)).factorization p :=
    num_factorization_eq_of_k_lt n p k hp hk
  have h_den : (den (n * p + k)).factorization p = (den (n * p)).factorization p :=
    den_factorization_eq_of_k_lt n p k hp hk
  rw [h_num, h_den]
