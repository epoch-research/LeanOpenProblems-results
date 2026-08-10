import FormalConjectures.Util.ProblemImports

open Nat

/--
A180017: Difference of sums of digits of $n$ in ternary and in binary.
$$a(n) = \left(\sum \text{digits}_3(n)\right) - \left(\sum \text{digits}_2(n)\right)$$
-/
def a (n : ℕ) : ℤ :=
  Int.ofNat (Nat.digits 3 n |>.sum) - Int.ofNat (Nat.digits 2 n |>.sum)


theorem pow_succ_sub_one (b k : ℕ) (hb : 2 ≤ b) :
    b ^ (k + 1) - 1 = b * (b ^ k - 1) + (b - 1) := by
  rw [pow_succ, mul_comm (b ^ k) b]
  have h1 : b * (b ^ k - 1) = b * b ^ k - b := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  rw [h1]
  have h2 : b ≤ b * b ^ k := by
    have : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
    nth_rewrite 1 [← mul_one b]
    exact Nat.mul_le_mul_left b this
  omega

theorem digits_pow_sub_one (b k : ℕ) (hb : 2 ≤ b) :
    digits b (b ^ k - 1) = List.replicate k (b - 1) := by
  induction k with
  | zero =>
    simp [digits_zero]
  | succ k ih =>
    have hb1 : 1 < b := by omega
    have h_ne : b ^ (k + 1) - 1 ≠ 0 := by
      have h_pow_ge : 2 ≤ b ^ (k + 1) := by
        rw [pow_succ, mul_comm (b ^ k) b]
        have : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
        have h_mul : b ≤ b * b ^ k := by
          nth_rewrite 1 [← mul_one b]
          exact Nat.mul_le_mul_left b this
        omega
      omega
    rw [digits_eq_cons_digits_div hb1 h_ne]
    have h_eq : b ^ (k + 1) - 1 = (b - 1) + b * (b ^ k - 1) := by
      rw [pow_succ_sub_one b k hb]
      omega
    have h_mod : (b ^ (k + 1) - 1) % b = b - 1 := by
      rw [h_eq]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have h_div : (b ^ (k + 1) - 1) / b = b ^ k - 1 := by
      rw [h_eq]
      rw [Nat.add_mul_div_left _ _ (by omega)]
      have : (b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
      rw [this, zero_add]
    rw [h_mod, h_div, ih]
    rfl

theorem sum_replicate (k x : ℕ) : (List.replicate k x).sum = x * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.sum_cons, ih]
    ring

theorem sum_digits_pow_three_sub_one (k : ℕ) :
    (digits 3 (3 ^ k - 1)).sum = 2 * k := by
  rw [digits_pow_sub_one 3 k (by decide)]
  rw [sum_replicate]

theorem sum_le_length_of_le_one (L : List ℕ) (h : ∀ x ∈ L, x ≤ 1) : L.sum ≤ L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons, List.length_cons]
    have h_x : x ≤ 1 := h x (by simp)
    have h_xs : ∀ y ∈ xs, y ≤ 1 := fun y hy => h y (by simp [hy])
    have ih_xs : xs.sum ≤ xs.length := ih h_xs
    omega

theorem digits_two_le_one (n : ℕ) (x : ℕ) (h : x ∈ digits 2 n) : x ≤ 1 := by
  have h_lt : x < 2 := digits_lt_base (by decide) h
  omega

theorem sum_digits_two_le_length (n : ℕ) : (digits 2 n).sum ≤ (digits 2 n).length := by
  apply sum_le_length_of_le_one
  exact digits_two_le_one n

theorem digits_two_length_le_of_pow_le (k M : ℕ) (h : 3 ^ k ≤ 2 ^ M) :
    (digits 2 (3 ^ k - 1)).length ≤ M := by
  rw [digits_length_le_iff (by decide)]
  have : 3 ^ k - 1 < 3 ^ k := by
    have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by omega)
    omega
  omega

theorem pow_three_five_le_pow_two_eight (j : ℕ) : 3 ^ (5 * j) ≤ 2 ^ (8 * j) := by
  rw [pow_mul, pow_mul]
  have : (3 ^ 5) ≤ (2 ^ 8) := by decide
  exact Nat.pow_le_pow_left this j

theorem a_unbounded_above (j : ℕ) : a (3 ^ (5 * j) - 1) ≥ 2 * j := by
  unfold a
  have h3 : (digits 3 (3 ^ (5 * j) - 1)).sum = 10 * j := by
    rw [sum_digits_pow_three_sub_one (5 * j)]
    ring
  have h2 : (digits 2 (3 ^ (5 * j) - 1)).sum ≤ 8 * j := by
    have h_le : (digits 2 (3 ^ (5 * j) - 1)).length ≤ 8 * j := by
      apply digits_two_length_le_of_pow_le (5 * j) (8 * j)
      exact pow_three_five_le_pow_two_eight j
    have h_sum_le : (digits 2 (3 ^ (5 * j) - 1)).sum ≤ (digits 2 (3 ^ (5 * j) - 1)).length := by
      exact sum_digits_two_le_length _
    omega
  have h_ofNat (x : ℕ) : Int.ofNat x = (x : ℤ) := rfl
  simp only [h_ofNat]
  rw [h3]
  omega


theorem sum_digits_mul_pow (b k m : ℕ) (hb : 1 < b) (hm : 0 < m) :
    (digits b (m * b ^ k)).sum = (digits b m).sum := by
  rw [mul_comm, digits_base_pow_mul hb hm]
  simp

theorem sum_digits_add_pow_mul (b n k m : ℕ) (hb : 1 < b) (hm : 0 < m) (hk : (digits b n).length ≤ k) :
    (digits b (n + b ^ k * m)).sum = (digits b n).sum + (digits b m).sum := by
  have h_eq : k = (digits b n).length + (k - (digits b n).length) := by omega
  nth_rewrite 1 [h_eq]
  rw [← digits_append_zeroes_append_digits hb hm]
  simp

theorem a_add_block_six (n L : ℕ) (hL2 : (digits 2 n).length ≤ L) (hL3 : (digits 3 n).length ≤ L) :
    a (n + 6 ^ L) = a n + a (6 ^ L) := by
  have h3 : 1 < 3 := by decide
  have h2 : 1 < 2 := by decide
  have h_2_mul_pos : 0 < 2 ^ L := by positivity
  have h_3_mul_pos : 0 < 3 ^ L := by positivity
  unfold a
  have h_6_eq3 : 6 ^ L = 3 ^ L * 2 ^ L := by rw [show (6 : ℕ) = 3 * 2 by decide, mul_pow]
  have h_6_eq2 : 6 ^ L = 2 ^ L * 3 ^ L := by rw [show (6 : ℕ) = 2 * 3 by decide, mul_pow]
  have h_base3 : (digits 3 (n + 6 ^ L)).sum = (digits 3 n).sum + (digits 3 (2 ^ L)).sum := by
    rw [h_6_eq3]
    rw [sum_digits_add_pow_mul 3 n L (2 ^ L) h3 h_2_mul_pos hL3]
  have h_base2 : (digits 2 (n + 6 ^ L)).sum = (digits 2 n).sum + (digits 2 (3 ^ L)).sum := by
    rw [h_6_eq2]
    rw [sum_digits_add_pow_mul 2 n L (3 ^ L) h2 h_3_mul_pos hL2]
  rw [h_base3, h_base2]
  have h_6_base3 : (digits 3 (6 ^ L)).sum = (digits 3 (2 ^ L)).sum := by
    rw [h_6_eq3, mul_comm (3^L) (2^L)]
    rw [sum_digits_mul_pow 3 L (2 ^ L) h3 h_2_mul_pos]
  have h_6_base2 : (digits 2 (6 ^ L)).sum = (digits 2 (3 ^ L)).sum := by
    rw [h_6_eq2, mul_comm (2^L) (3^L)]
    rw [sum_digits_mul_pow 2 L (3 ^ L) h2 h_3_mul_pos]
  have h_ofNat (x : ℕ) : Int.ofNat x = (x : ℤ) := rfl
  simp only [h_ofNat]
  rw [h_6_base3, h_6_base2]
  simp only [Nat.cast_add]
  ring

theorem a_prod_pow (k m : ℕ) : a (3 ^ k * 2 ^ m) = (digits 3 (2 ^ m)).sum - (digits 2 (3 ^ k)).sum := by
  unfold a
  have h3 : 1 < 3 := by decide
  have h2 : 1 < 2 := by decide
  have h2m : 0 < 2 ^ m := by positivity
  have h3k : 0 < 3 ^ k := by positivity
  have h_base3 : (digits 3 (3 ^ k * 2 ^ m)).sum = (digits 3 (2 ^ m)).sum := by
    rw [mul_comm]
    rw [sum_digits_mul_pow 3 k (2 ^ m) h3 h2m]
  have h_base2 : (digits 2 (3 ^ k * 2 ^ m)).sum = (digits 2 (3 ^ k)).sum := by
    rw [sum_digits_mul_pow 2 m (3 ^ k) h2 h3k]
  have h_ofNat (x : ℕ) : Int.ofNat x = (x : ℤ) := rfl
  simp only [h_ofNat]
  rw [h_base3, h_base2]


theorem a_add_block (n L M : ℕ) (hL : (digits 3 n).length ≤ L) (hM : (digits 2 n).length ≤ M) :
    a (n + 3 ^ L * 2 ^ M) = a n + a (3 ^ L * 2 ^ M) := by
  have h3 : 1 < 3 := by decide
  have h2 : 1 < 2 := by decide
  have h_2_mul_pos : 0 < 2 ^ M := by positivity
  have h_3_mul_pos : 0 < 3 ^ L := by positivity
  unfold a
  have h_base3 : (digits 3 (n + 3 ^ L * 2 ^ M)).sum = (digits 3 n).sum + (digits 3 (2 ^ M)).sum := by
    rw [sum_digits_add_pow_mul 3 n L (2 ^ M) h3 h_2_mul_pos hL]
  have h_base2 : (digits 2 (n + 3 ^ L * 2 ^ M)).sum = (digits 2 n).sum + (digits 2 (3 ^ L)).sum := by
    rw [mul_comm (3^L) (2^M)]
    rw [sum_digits_add_pow_mul 2 n M (3 ^ L) h2 h_3_mul_pos hM]
  rw [h_base3, h_base2]
  have h_block_base3 : (digits 3 (3 ^ L * 2 ^ M)).sum = (digits 3 (2 ^ M)).sum := by
    rw [mul_comm (3^L) (2^M)]
    rw [sum_digits_mul_pow 3 L (2 ^ M) h3 h_2_mul_pos]
  have h_block_base2 : (digits 2 (3 ^ L * 2 ^ M)).sum = (digits 2 (3 ^ L)).sum := by
    rw [sum_digits_mul_pow 2 M (3 ^ L) h2 h_3_mul_pos]
  have h_ofNat (x : ℕ) : Int.ofNat x = (x : ℤ) := rfl
  simp only [h_ofNat]
  rw [h_block_base3, h_block_base2]
  simp only [Nat.cast_add]
  ring

theorem a_pow_mul_sub_one (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    a (3 ^ k * 2 ^ m - 1) = (2 * k : ℤ) - (m : ℤ) + ((digits 3 (2 ^ m - 1)).sum : ℤ) - ((digits 2 (3 ^ k - 1)).sum : ℤ) := by
  unfold a
  have h3 : 1 < 3 := by decide
  have h2 : 1 < 2 := by decide
  have h_3k : 1 < 3 ^ k := by
    have : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  have h_2m : 1 < 2 ^ m := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
    omega
  have h_3k_sub_one_pos : 0 < 3 ^ k - 1 := by omega
  have h_2m_sub_one_pos : 0 < 2 ^ m - 1 := by omega
  have h_len3 : (digits 3 (3 ^ k - 1)).length ≤ k := by
    rw [digits_pow_sub_one 3 k (by decide)]
    rw [List.length_replicate]
  have h_len2 : (digits 2 (2 ^ m - 1)).length ≤ m := by
    rw [digits_pow_sub_one 2 m (by decide)]
    rw [List.length_replicate]
  have h_eq3 : 3 ^ k * 2 ^ m - 1 = (3 ^ k - 1) + 3 ^ k * (2 ^ m - 1) := by
    have h_pow : 1 ≤ 2 ^ m := by omega
    have h_le : 3 ^ k ≤ 3 ^ k * 2 ^ m := by
      nth_rewrite 1 [← mul_one (3 ^ k)]
      exact Nat.mul_le_mul_left (3 ^ k) h_pow
    have h_mul : 3 ^ k * 2 ^ m = 3 ^ k * (2 ^ m - 1) + 3 ^ k := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      omega
    omega
  have h_eq2 : 3 ^ k * 2 ^ m - 1 = (2 ^ m - 1) + 2 ^ m * (3 ^ k - 1) := by
    rw [mul_comm (3^k) (2^m)]
    have h_mul : 2 ^ m * 3 ^ k = 2 ^ m * (3 ^ k - 1) + 2 ^ m := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have : 1 ≤ 3 ^ k := by omega
      have : 2 ^ m ≤ 2 ^ m * 3 ^ k := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    omega
  have h_base3 : (digits 3 (3 ^ k * 2 ^ m - 1)).sum = 2 * k + (digits 3 (2 ^ m - 1)).sum := by
    rw [h_eq3]
    rw [sum_digits_add_pow_mul 3 (3 ^ k - 1) k (2 ^ m - 1) h3 h_2m_sub_one_pos h_len3]
    rw [sum_digits_pow_three_sub_one]
  have h_base2 : (digits 2 (3 ^ k * 2 ^ m - 1)).sum = m + (digits 2 (3 ^ k - 1)).sum := by
    rw [h_eq2]
    rw [sum_digits_add_pow_mul 2 (2 ^ m - 1) m (3 ^ k - 1) h2 h_3k_sub_one_pos h_len2]
    rw [digits_pow_sub_one 2 m (by decide)]
    rw [sum_replicate, show 2 - 1 = 1 by decide, one_mul]
  have h_ofNat (x : ℕ) : Int.ofNat x = (x : ℤ) := rfl
  simp only [h_ofNat, h_base3, h_base2]
  push_cast
  ring


theorem a_six : a 6 = 0 := by
  unfold a
  have h2 : digits 2 6 = [0, 1, 1] := by
    have hb : 1 < 2 := by decide
    rw [digits_eq_cons_digits_div hb (by decide)]
    rw [show 6 % 2 = 0 by rfl, show 6 / 2 = 3 by rfl]
    congr 1
    rw [digits_eq_cons_digits_div hb (by decide)]
    rw [show 3 % 2 = 1 by rfl, show 3 / 2 = 1 by rfl]
    congr 1
    rw [digits_eq_cons_digits_div hb (by decide)]
    rw [show 1 % 2 = 1 by rfl, show 1 / 2 = 0 by rfl]
    congr 1
    rw [digits_zero]
  have h3 : digits 3 6 = [0, 2] := by
    have hb : 1 < 3 := by decide
    rw [digits_eq_cons_digits_div hb (by decide)]
    rw [show 6 % 3 = 0 by rfl, show 6 / 3 = 2 by rfl]
    congr 1
    rw [digits_eq_cons_digits_div hb (by decide)]
    rw [show 2 % 3 = 2 by rfl, show 2 / 3 = 0 by rfl]
    congr 1
    rw [digits_zero]
  rw [h2, h3]
  rfl

lemma a_block_zero : a (3^12 * 2^11) = 0 := by decide


/--
%C A180017 This sequence is positive on average, since 1/log(3) > 1/log(4). Do all integers appear infinitely often? - _Charles R Greathouse IV_, Feb 07 2013
The conjecture asks if for every integer $z$, the set of natural numbers $n$ such that $a(n) = z$ is infinite.
-/

lemma a_infinite_of_exists_of_shift (z : ℤ) (h_exists : ∃ n, a n = z) (h_shift : ∀ n, ∃ n' > n, a n' = a n) :
    ∀ N : ℕ, ∃ n > N, a n = z := by
  intro N
  induction N with
  | zero =>
    rcases h_exists with ⟨n0, hn0⟩
    by_cases h : n0 > 0
    · exact ⟨n0, h, hn0⟩
    · have : n0 = 0 := by omega
      subst this
      rcases h_shift 0 with ⟨n', hn', han'⟩
      exact ⟨n', hn', by rw [han', hn0]⟩
  | succ N ih =>
    rcases ih with ⟨n, hn, han⟩
    have h_cases : n > N + 1 ∨ n = N + 1 := by omega
    rcases h_cases with h1 | h2
    · exact ⟨n, h1, han⟩
    · rcases h_shift n with ⟨n', hn', han'⟩
      have : n' > N + 1 := by omega
      exact ⟨n', this, by rw [han', han]⟩

theorem oeis_180017_conjecture_0 :
  ∀ z : ℤ, Set.Infinite { n : ℕ | a n = z } := by
  intro z
  apply Set.infinite_of_forall_exists_gt
  intro N
  sorry





