import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k
  numerator / denominator

def b (n : ℕ) : ℕ := n / 2

def A (m : ℕ) : ℕ := (Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k
def B (m : ℕ) : ℕ := (Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k

lemma a_eq_A_div_B (m : ℕ) : a m = A m / B m := by rfl

lemma fac_gcd (j k q : ℕ) (hj : j ≠ 0) (hk : k ≠ 0) :
    (Nat.gcd j k).factorization q = min (j.factorization q) (k.factorization q) := by
  rw [Nat.factorization_gcd hj hk]
  rfl

lemma vq_A (m q : ℕ) :
    (A m).factorization q = (Icc 1 m).sum fun j => (Icc 1 m).sum fun k => min (j.factorization q) (k.factorization q) := by
  have h_ne : ∀ j ∈ Icc 1 m, (Icc 1 m).prod (fun k => Nat.gcd j k) ≠ 0 := by
    intro j hj
    apply prod_ne_zero_iff.mpr
    intro k hk
    have hj_ne : j ≠ 0 := by have := mem_Icc.mp hj; omega
    exact Nat.gcd_ne_zero_left hj_ne
  rw [A, Nat.factorization_prod h_ne]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  apply sum_congr rfl
  intro j hj
  have hj_ne : j ≠ 0 := by have := mem_Icc.mp hj; omega
  have h_ne2 : ∀ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := by
    intro k hk
    exact Nat.gcd_ne_zero_left hj_ne
  rw [Nat.factorization_prod h_ne2]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  apply sum_congr rfl
  intro k hk
  have hk_ne : k ≠ 0 := by have := mem_Icc.mp hk; omega
  exact fac_gcd j k q hj_ne hk_ne

lemma val_eq_sum (x b : ℕ) (h : x < b) :
    x = (Ico 1 b).sum (fun i => if i ≤ x then 1 else 0) := by
  have : (Ico 1 b) = (Icc 1 x) ∪ (Ico (x + 1) b) := by
    ext i
    simp only [mem_union, mem_Ico, mem_Icc]
    omega
  rw [this, sum_union]
  · have h1 : (Icc 1 x).sum (fun i => if i ≤ x then 1 else 0) = x := by
      have h_eq : ∀ i ∈ Icc 1 x, (if i ≤ x then 1 else 0) = 1 := by
        intro i hi
        rw [if_pos (mem_Icc.mp hi).right]
      rw [sum_congr rfl h_eq, sum_const, card_Icc, smul_eq_mul, mul_one]
      omega
    have h2 : (Ico (x + 1) b).sum (fun i => if i ≤ x then 1 else 0) = 0 := by
      have h_eq : ∀ i ∈ Ico (x + 1) b, (if i ≤ x then 1 else 0) = 0 := by
        intro i hi
        rw [if_neg (by have := (mem_Ico.mp hi).left; omega)]
      rw [sum_congr rfl h_eq, sum_const_zero]
    rw [h1, h2, add_zero]
  · rw [disjoint_iff_ne]
    intro i hi j hj
    have : i ≤ x := (mem_Icc.mp hi).right
    have : x + 1 ≤ j := (mem_Ico.mp hj).left
    omega

lemma min_eq_sum (x y b : ℕ) (h : min x y < b) :
    min x y = (Ico 1 b).sum (fun i => (if i ≤ x then 1 else 0) * (if i ≤ y then 1 else 0)) := by
  rw [val_eq_sum (min x y) b h]
  apply sum_congr rfl
  intro i _
  have h1 : i ≤ min x y ↔ i ≤ x ∧ i ≤ y := le_min_iff
  by_cases hle : i ≤ min x y
  · have hx : i ≤ x := (h1.mp hle).left
    have hy : i ≤ y := (h1.mp hle).right
    rw [if_pos hle, if_pos hx, if_pos hy, mul_one]
  · rw [if_neg hle]
    by_cases hx : i ≤ x
    · have hy : ¬ (i ≤ y) := by
        intro hy
        exact hle (h1.mpr ⟨hx, hy⟩)
      rw [if_pos hx, if_neg hy, mul_zero]
    · rw [if_neg hx, zero_mul]

lemma fac_le (j q : ℕ) (hq : q.Prime) (hj : j ≠ 0) : j.factorization q < j + 1 := by
  have h1 : q ^ j.factorization q ∣ j := by rw [hq.pow_dvd_iff_le_factorization hj]
  have h2 : q ^ j.factorization q ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) h1
  have h3 : j.factorization q < q ^ j.factorization q := Nat.lt_pow_self hq.one_lt
  omega

lemma min_fac_eq_sum (j k m q : ℕ) (hq : q.Prime) (hj : j ∈ Icc 1 m) (hk : k ∈ Icc 1 m) :
    min (j.factorization q) (k.factorization q) = (Ico 1 (m + 1)).sum fun i => (if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0) := by
  have hj_pos : j ≠ 0 := by have := mem_Icc.mp hj; omega
  have hk_pos : k ≠ 0 := by have := mem_Icc.mp hk; omega
  have h1 : j.factorization q < m + 1 := by
    have h_le := fac_le j q hq hj_pos
    have h_m : j ≤ m := (mem_Icc.mp hj).right
    omega
  have h_min : min (j.factorization q) (k.factorization q) < m + 1 := by omega
  rw [min_eq_sum _ _ _ h_min]
  apply sum_congr rfl
  intro i hi
  have hj_dvd : i ≤ j.factorization q ↔ q ^ i ∣ j := (hq.pow_dvd_iff_le_factorization hj_pos).symm
  have hk_dvd : i ≤ k.factorization q ↔ q ^ i ∣ k := (hq.pow_dvd_iff_le_factorization hk_pos).symm
  by_cases h_j_dvd : q ^ i ∣ j
  · rw [if_pos h_j_dvd, if_pos (hj_dvd.mpr h_j_dvd)]
    by_cases h_k_dvd : q ^ i ∣ k
    · rw [if_pos h_k_dvd, if_pos (hk_dvd.mpr h_k_dvd)]
    · rw [if_neg h_k_dvd, if_neg (mt hk_dvd.mp h_k_dvd)]
  · rw [if_neg h_j_dvd, if_neg (mt hj_dvd.mp h_j_dvd), zero_mul, zero_mul]

lemma vq_A_swap (m : ℕ) (F : ℕ → ℕ → ℕ → ℕ) :
    ((Icc 1 m).sum fun j => (Icc 1 m).sum fun k => (Ico 1 (m + 1)).sum fun i => F i j k) =
    (Ico 1 (m + 1)).sum fun i => ((Icc 1 m).sum fun j => (Icc 1 m).sum fun k => F i j k) := by
  have h1 : ((Icc 1 m).sum fun j => (Icc 1 m).sum fun k => (Ico 1 (m + 1)).sum fun i => F i j k) =
            ((Icc 1 m).sum fun j => (Ico 1 (m + 1)).sum fun i => (Icc 1 m).sum fun k => F i j k) := by
    apply sum_congr rfl
    intro j hj
    rw [sum_comm]
  rw [h1, sum_comm]

lemma sum_mul_sum_eq (m : ℕ) (f g : ℕ → ℕ) :
    ((Icc 1 m).sum fun j => (Icc 1 m).sum fun k => f j * g k) =
    ((Icc 1 m).sum fun j => f j) * ((Icc 1 m).sum fun k => g k) := by
  rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]

lemma count_dvd_eq_div_Ico (m d : ℕ) :
    (Ico 1 (m + 1)).sum (fun j => if d ∣ j then 1 else 0) = m / d := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_Ico_succ_top (Nat.succ_pos m), ih, Nat.succ_div, add_comm]

lemma count_dvd_eq_div (m d : ℕ) :
    (Icc 1 m).sum (fun j => if d ∣ j then 1 else 0) = m / d := by
  have h : (Icc 1 m).sum (fun j => if d ∣ j then 1 else 0) = (Ico 1 (m + 1)).sum (fun j => if d ∣ j then 1 else 0) := by
    apply sum_congr
    · ext x; simp
    · intro x hx; rfl
  rw [h, count_dvd_eq_div_Ico]

lemma sq_eq (x : ℕ) : x * x = x ^ 2 := by ring

lemma vq_A_val (m q : ℕ) (hq : q.Prime) :
    (A m).factorization q = (Ico 1 (m + 1)).sum fun i => (m / q ^ i) ^ 2 := by
  rw [vq_A m q]
  have h_min : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, min (j.factorization q) (k.factorization q) = (Ico 1 (m + 1)).sum fun i => (if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0) := by
    intro j hj k hk
    exact min_fac_eq_sum j k m q hq hj hk
  have h_sum_inner : ((Icc 1 m).sum fun j => (Icc 1 m).sum fun k => min (j.factorization q) (k.factorization q)) =
                     ((Icc 1 m).sum fun j => (Icc 1 m).sum fun k => (Ico 1 (m + 1)).sum fun i => (if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0)) := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro k hk
    exact h_min j hj k hk
  rw [h_sum_inner, vq_A_swap]
  apply sum_congr rfl
  intro i hi
  rw [sum_mul_sum_eq, count_dvd_eq_div, sq_eq]

lemma log_bound (m p : ℕ) (hp : 1 < p) (hm : m ≠ 0) :
    Nat.log p m < m + 1 := by
  rw [Nat.log_lt_iff_lt_pow hp hm]
  have h1 : m < p ^ m := Nat.lt_pow_self hp
  calc m < p ^ m := h1
  _ ≤ p ^ m * p := by nlinarith
  _ = p ^ (m + 1) := by ring

lemma vq_B (m q : ℕ) (hq : q.Prime) :
    (B m).factorization q = (Icc 1 m).sum fun k => k * (Ico 1 (m + 1)).sum fun i => (m / k) / q ^ i := by
  by_cases hm : m = 0
  · subst hm; simp [B]
  have h_ne : ∀ k ∈ Icc 1 m, (Nat.factorial (m / k)) ^ k ≠ 0 := by
    intro k hk
    apply pow_ne_zero
    exact Nat.factorial_ne_zero (m / k)
  rw [B, Nat.factorization_prod h_ne, Finsupp.coe_finset_sum, sum_apply]
  apply sum_congr rfl
  intro k hk
  rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have h_log : Nat.log q (m / k) < m + 1 := by
    have h1 : m / k ≤ m := Nat.div_le_self m k
    have h2 : Nat.log q (m / k) ≤ Nat.log q m := Nat.log_mono_right h1
    have h3 : Nat.log q m < m + 1 := log_bound m q hq.one_lt hm
    omega
  rw [Nat.factorization_factorial hq h_log]

lemma sum_k_floor_le_sq (N : ℕ) : ∑ k ∈ Icc 1 N, k * (N / k) ≤ N ^ 2 := by
  have h : ∀ k ∈ Icc 1 N, k * (N / k) ≤ N := fun k _ => Nat.mul_div_le N k
  calc
    ∑ k ∈ Icc 1 N, k * (N / k) ≤ ∑ k ∈ Icc 1 N, N := sum_le_sum h
    _ = (Icc 1 N).card * N := by simp
    _ = N * N := by simp [Nat.card_Icc]
    _ = N ^ 2 := by ring

lemma sum_m_eq_sum_N (m N : ℕ) (hN : N ≤ m) :
    ((Icc 1 m).sum fun k => k * (N / k)) = ((Icc 1 N).sum fun k => k * (N / k)) := by
  have : (Icc 1 m) = (Icc 1 N) ∪ (Ico (N + 1) (m + 1)) := by
    ext x
    simp only [mem_union, mem_Ico, mem_Icc]
    omega
  rw [this, sum_union]
  · have h_zero : (Ico (N + 1) (m + 1)).sum (fun k => k * (N / k)) = 0 := by
      have : ∀ k ∈ Ico (N + 1) (m + 1), k * (N / k) = 0 := by
        intro k hk
        have hk_gt : N < k := by have := (mem_Ico.mp hk).left; omega
        rw [Nat.div_eq_of_lt hk_gt, mul_zero]
      rw [sum_congr rfl this, sum_const_zero]
    rw [h_zero, add_zero]
  · rw [disjoint_iff_ne]
    intro x hx y hy
    have : x ≤ N := (mem_Icc.mp hx).right
    have : N + 1 ≤ y := (mem_Ico.mp hy).left
    omega

lemma div_div_eq_div_div (m k q i : ℕ) :
    (m / k) / q ^ i = (m / q ^ i) / k := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]

lemma vq_B_le_vq_A_term (m q i : ℕ) :
    ((Icc 1 m).sum fun k => k * ((m / k) / q ^ i)) ≤ (m / q ^ i) ^ 2 := by
  have h_eq : ((Icc 1 m).sum fun k => k * ((m / k) / q ^ i)) = ((Icc 1 m).sum fun k => k * ((m / q ^ i) / k)) := by
    apply sum_congr rfl
    intro k hk
    rw [div_div_eq_div_div]
  rw [h_eq]
  set N := m / q ^ i
  have hN : N ≤ m := Nat.div_le_self m (q ^ i)
  rw [sum_m_eq_sum_N m N hN]
  exact sum_k_floor_le_sq N

lemma vq_B_le_vq_A_helper (m q : ℕ) :
    ((Ico 1 (m + 1)).sum fun i => (Icc 1 m).sum fun k => k * ((m / k) / q ^ i)) ≤
    ((Ico 1 (m + 1)).sum fun i => (m / q ^ i) ^ 2) := by
  apply sum_le_sum
  intro i hi
  exact vq_B_le_vq_A_term m q i

lemma sum_swap_B (m q : ℕ) :
    ((Icc 1 m).sum fun k => k * ((Ico 1 (m + 1)).sum fun i => (m / k) / q ^ i)) =
    ((Ico 1 (m + 1)).sum fun i => (Icc 1 m).sum fun k => k * ((m / k) / q ^ i)) := by
  have h1 : ((Icc 1 m).sum fun k => k * ((Ico 1 (m + 1)).sum fun i => (m / k) / q ^ i)) =
            ((Icc 1 m).sum fun k => (Ico 1 (m + 1)).sum fun i => k * ((m / k) / q ^ i)) := by
    apply sum_congr rfl
    intro k hk
    rw [mul_sum]
  rw [h1, sum_comm]

lemma div_eq_of_mod (n p x i : ℕ) (hx : x < p) (hi : 1 ≤ i) (hp : 0 < p) :
    (n * p + x) / p ^ i = (n * p) / p ^ i := by
  have : p ^ i = p * p ^ (i - 1) := by
    calc p ^ i = p ^ (1 + (i - 1)) := by congr 1; omega
    _ = p ^ 1 * p ^ (i - 1) := by rw [pow_add]
    _ = p * p ^ (i - 1) := by rw [pow_one]
  rw [this, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h1 : (n * p + x) / p = n := by
    have hcomm : n * p + x = x + n * p := add_comm _ _
    rw [hcomm, Nat.add_mul_div_right x n hp]
    have hx0 : x / p = 0 := Nat.div_eq_of_lt hx
    omega
  have h2 : (n * p) / p = n := Nat.mul_div_cancel n hp
  rw [h1, h2]

lemma term_B_eq (n p x i k : ℕ) (hx : x < p) (hi : 1 ≤ i) (hp : 0 < p) :
    ((n * p + x) / k) / p ^ i = ((n * p) / k) / p ^ i := by
  rw [div_div_eq_div_div, div_div_eq_div_div]
  rw [div_eq_of_mod n p x i hx hi hp]

lemma sum_B_extend_k (m1 m2 p i : ℕ) (h_le : m1 ≤ m2) :
    ((Icc 1 m1).sum fun k => k * (((m1) / k) / p ^ i)) =
    ((Icc 1 m2).sum fun k => k * (((m1) / k) / p ^ i)) := by
  have : (Icc 1 m2) = (Icc 1 m1) ∪ (Ico (m1 + 1) (m2 + 1)) := by
    ext k
    simp only [mem_union, mem_Ico, mem_Icc]
    omega
  rw [this, sum_union]
  · have h_zero : (Ico (m1 + 1) (m2 + 1)).sum (fun k => k * (((m1) / k) / p ^ i)) = 0 := by
      have h_eq : ∀ k ∈ Ico (m1 + 1) (m2 + 1), k * (((m1) / k) / p ^ i) = 0 := by
        intro k hk
        have hk_gt : m1 < k := by have := (mem_Ico.mp hk).left; omega
        have hdiv : m1 / k = 0 := Nat.div_eq_of_lt hk_gt
        rw [hdiv, Nat.zero_div, mul_zero]
      rw [sum_congr rfl h_eq, sum_const_zero]
    rw [h_zero, add_zero]
  · rw [disjoint_iff_ne]
    intro k hk j hj
    have : k ≤ m1 := (mem_Icc.mp hk).right
    have : m1 + 1 ≤ j := (mem_Ico.mp hj).left
    omega

lemma div_zero_of_ge (m p i : ℕ) (hp : 2 ≤ p) (hi : m < i) :
    m / p ^ i = 0 := by
  have h1 : i ≤ 2 ^ i := by
    have : i < 2 ^ i := Nat.lt_pow_self (by omega)
    omega
  have h2 : 2 ^ i ≤ p ^ i := Nat.pow_le_pow_left hp i
  have : m < p ^ i := by omega
  exact Nat.div_eq_of_lt this

lemma sum_B_extend_i (m1 m2 p : ℕ) (h_le : m1 ≤ m2) (hp : 2 ≤ p) :
    ((Ico 1 (m1 + 1)).sum fun i => (Icc 1 m1).sum fun k => k * ((m1 / k) / p ^ i)) =
    ((Ico 1 (m2 + 1)).sum fun i => (Icc 1 m1).sum fun k => k * ((m1 / k) / p ^ i)) := by
  have : (Ico 1 (m2 + 1)) = (Ico 1 (m1 + 1)) ∪ (Ico (m1 + 1) (m2 + 1)) := by
    ext i
    simp only [mem_union, mem_Ico]
    omega
  rw [this, sum_union]
  · have h_zero : (Ico (m1 + 1) (m2 + 1)).sum (fun i => (Icc 1 m1).sum fun k => k * ((m1 / k) / p ^ i)) = 0 := by
      have h_eq : ∀ i ∈ Ico (m1 + 1) (m2 + 1), ((Icc 1 m1).sum fun k => k * ((m1 / k) / p ^ i)) = 0 := by
        intro i hi
        have hi_gt : m1 < i := by have := (mem_Ico.mp hi).left; omega
        have h_inner : ∀ k ∈ Icc 1 m1, k * ((m1 / k) / p ^ i) = 0 := by
          intro k hk
          have hdiv : m1 / p ^ i = 0 := div_zero_of_ge m1 p i hp hi_gt
          rw [div_div_eq_div_div, hdiv, Nat.zero_div, mul_zero]
        rw [sum_congr rfl h_inner, sum_const_zero]
      rw [sum_congr rfl h_eq, sum_const_zero]
    rw [h_zero, add_zero]
  · rw [disjoint_iff_ne]
    intro i hi j hj
    have : i ≤ m1 := by have := (mem_Ico.mp hi).right; omega
    have : m1 + 1 ≤ j := (mem_Ico.mp hj).left
    omega

lemma sum_B_m2_eq_sum_B_m1 (n p x : ℕ) (hx : x < p) (hp : 2 ≤ p) :
    ((Ico 1 (n * p + x + 1)).sum fun i => (Icc 1 (n * p + x)).sum fun k => k * (((n * p + x) / k) / p ^ i)) =
    ((Ico 1 (n * p + 1)).sum fun i => (Icc 1 (n * p)).sum fun k => k * (((n * p) / k) / p ^ i)) := by
  have h_le : n * p ≤ n * p + x := by omega
  have h_pos : 0 < p := by omega
  rw [sum_B_extend_i (n * p) (n * p + x) p h_le hp]
  apply sum_congr rfl
  intro i hi
  have hi_pos : 1 ≤ i := (mem_Ico.mp hi).left
  have h_inner : ((Icc 1 (n * p + x)).sum fun k => k * (((n * p + x) / k) / p ^ i)) =
                 ((Icc 1 (n * p + x)).sum fun k => k * (((n * p) / k) / p ^ i)) := by
    apply sum_congr rfl
    intro k hk
    rw [term_B_eq n p x i k hx hi_pos h_pos]
  rw [h_inner, ← sum_B_extend_k (n * p) (n * p + x) p i h_le]

lemma sum_extend (m1 m2 p : ℕ) (h_le : m1 ≤ m2) (hp : 2 ≤ p) :
    ((Ico 1 (m1 + 1)).sum fun i => (m1 / p ^ i) ^ 2) =
    ((Ico 1 (m2 + 1)).sum fun i => (m1 / p ^ i) ^ 2) := by
  have : (Ico 1 (m2 + 1)) = (Ico 1 (m1 + 1)) ∪ (Ico (m1 + 1) (m2 + 1)) := by
    ext i
    simp only [mem_union, mem_Ico]
    omega
  rw [this, sum_union]
  · have h_zero : (Ico (m1 + 1) (m2 + 1)).sum (fun i => (m1 / p ^ i) ^ 2) = 0 := by
      have h_eq : ∀ i ∈ Ico (m1 + 1) (m2 + 1), (m1 / p ^ i) ^ 2 = 0 := by
        intro i hi
        have hi_gt : m1 < i := by have := (mem_Ico.mp hi).left; omega
        rw [div_zero_of_ge m1 p i hp hi_gt, zero_pow (by decide)]
      rw [sum_congr rfl h_eq, sum_const_zero]
    rw [h_zero, add_zero]
  · rw [disjoint_iff_ne]
    intro i hi j hj
    have : i ≤ m1 := by have := (mem_Ico.mp hi).right; omega
    have : m1 + 1 ≤ j := (mem_Ico.mp hj).left
    omega

lemma sum_m2_eq_sum_m1 (n p x : ℕ) (hx : x < p) (hp : 2 ≤ p) :
    ((Ico 1 (n * p + x + 1)).sum fun i => ((n * p + x) / p ^ i) ^ 2) =
    ((Ico 1 (n * p + x + 1)).sum fun i => ((n * p) / p ^ i) ^ 2) := by
  apply sum_congr rfl
  intro i hi
  have h_pos : 0 < p := by omega
  have hi_pos : 1 ≤ i := (mem_Ico.mp hi).left
  rw [div_eq_of_mod n p x i hx hi_pos h_pos]

lemma vq_A_eq (n p x : ℕ) (hx : x < p) (hp : p.Prime) :
    (A (n * p + x)).factorization p = (A (n * p)).factorization p := by
  rw [vq_A_val (n * p + x) p hp, vq_A_val (n * p) p hp]
  have h_pos : 2 ≤ p := hp.two_le
  have h_le : n * p ≤ n * p + x := by omega
  rw [sum_extend (n * p) (n * p + x) p h_le h_pos]
  rw [sum_m2_eq_sum_m1 n p x hx h_pos]

lemma vq_B_eq (n p x : ℕ) (hx : x < p) (hp : p.Prime) :
    (B (n * p + x)).factorization p = (B (n * p)).factorization p := by
  rw [vq_B (n * p + x) p hp, vq_B (n * p) p hp]
  have h_pos : 2 ≤ p := hp.two_le
  rw [sum_swap_B, sum_swap_B]
  exact sum_B_m2_eq_sum_B_m1 n p x hx h_pos

lemma A_pos (m : ℕ) : A m ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro j hj
  apply prod_ne_zero_iff.mpr
  intro k hk
  have h1 : j ≠ 0 := by have := mem_Icc.mp hj; omega
  exact Nat.gcd_ne_zero_left h1

lemma B_pos (m : ℕ) : B m ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro k hk
  apply pow_ne_zero
  exact Nat.factorial_ne_zero (m / k)

lemma vq_le (m q : ℕ) (hq : q.Prime) : (B m).factorization q ≤ (A m).factorization q := by
  rw [vq_A_val m q hq, vq_B m q hq, sum_swap_B m q]
  exact vq_B_le_vq_A_helper m q

lemma B_dvd_A (m : ℕ) : B m ∣ A m := by
  rw [← Nat.factorization_le_iff_dvd (B_pos m) (A_pos m)]
  intro q
  by_cases hq : q.Prime
  · exact vq_le m q hq
  · have h1 : (B m).factorization q = 0 := Nat.factorization_eq_zero_of_not_prime (B m) hq
    rw [h1]
    exact Nat.zero_le ((A m).factorization q)

lemma fac_div (m q : ℕ) (h_dvd : B m ∣ A m) :
    (a m).factorization q = (A m).factorization q - (B m).factorization q := by
  rw [a_eq_A_div_B, Nat.factorization_div h_dvd]
  rfl

theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  rw [fac_div (n * p) p (B_dvd_A (n * p))]
  rw [fac_div (n * p + k) p (B_dvd_A (n * p + k))]
  rw [vq_A_eq n p k hk hp, vq_B_eq n p k hk hp]

theorem oeis_a129365_conjecture_C.disproof : ¬ (type_of% @oeis_a129365_conjecture_C) := sorry
