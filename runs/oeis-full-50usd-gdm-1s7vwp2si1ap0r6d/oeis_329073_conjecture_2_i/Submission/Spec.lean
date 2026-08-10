import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
T_k(b, c) is the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i$$
where $k \in \mathbb{N}$ and $b, c \in \mathbb{Z}$.
-/
def T_coeff (k : ℕ) (b c : ℤ) : ℤ :=
  (range (k / 2 + 1)).sum fun i : ℕ =>
    let choose_term : ℤ := (k.choose i).cast * ((k - i).choose i).cast
    let b_pow : ℤ := b ^ (k - 2 * i)
    let c_pow : ℤ := c ^ i
    choose_term * b_pow * c_pow

/--
A329073: $a(n) = (1/n)*\sum_{k=0}^{n-1} (40k+13)*(-1)^k*50^{n-1-k}*T_k(4,1)*T_k(1,-1)^2$,
where $T_k(b,c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2+b*x+c)^k$.
The sequence is conjectured to consist of integers, so we use integer division.
-/
def A329073 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | N@(_ + 1) => -- N is n+1, so $N \ge 1$.
    let N_int : ℤ := N.cast
    let sum_val : ℤ := (range N).sum fun k : ℕ =>
      let k_int : ℤ := k.cast
      let coeff_a : ℤ := T_coeff k 4 1
      let coeff_b : ℤ := T_coeff k 1 (-1)

      let term_1 := (40 * k_int + 13)
      let term_2 := (-1 : ℤ) ^ k
      let term_3_exp : ℕ := N - 1 - k
      let term_3 := (50 : ℤ) ^ term_3_exp

      term_1 * term_2 * term_3 * coeff_a * (coeff_b ^ 2)

    sum_val / N_int

/--
b(n) is the sequence related to A329073 defined as:
b(n) := (1/n)*Sum_{k=0..n-1} (40k+27)*(-6)^(n-1-k)*T_k(4,1)*T_k(1,-1)^2
It is conjectured to be an integer.
-/
def A329073_b (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | N@(_ + 1) => -- N is n+1, so $N \ge 1$.
    let N_int : ℤ := N.cast
    let sum_val : ℤ := (range N).sum fun k : ℕ =>
      let k_int : ℤ := k.cast
      let coeff_a : ℤ := T_coeff k 4 1
      let coeff_b : ℤ := T_coeff k 1 (-1)

      let term_1 := (40 * k_int + 27)
      let term_3_exp : ℕ := N - 1 - k
      let term_3 := ((-6) : ℤ) ^ term_3_exp

      term_1 * term_3 * coeff_a * (coeff_b ^ 2)

    sum_val / N_int

lemma choose_two_mul_even (i : ℕ) (hi : 1 ≤ i) : (2 * i).choose i = 2 * (2 * i - 1).choose i := by
  have h1 : 2 * i = 2 * i - 1 + 1 := by omega
  have h2 : i = i - 1 + 1 := by omega
  nth_rw 1 [h1]
  nth_rw 2 [h2]
  rw [Nat.choose_succ_succ]
  have h_symm : (2 * i - 1).choose (i - 1) = (2 * i - 1).choose i := by
    rw [← Nat.choose_symm_of_eq_add]
    omega
  have h3 : (i - 1).succ = i := by omega
  rw [h3, h_symm]
  ring

lemma member_range_double_le (k i : ℕ) (hi : i ∈ range (k / 2 + 1)) : 2 * i ≤ k := by
  rw [mem_range] at hi
  have h1 : i ≤ k / 2 := by omega
  have h2 : 2 * i ≤ 2 * (k / 2) := by omega
  have h3 : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
  omega

lemma T_coeff_even (k : ℕ) (hk : 1 ≤ k) : 2 ∣ T_coeff k 4 1 := by
  dsimp [T_coeff]
  apply Finset.dvd_sum
  intro i hi
  have h1 : (1 : ℤ) ^ i = 1 := by ring
  rw [h1, mul_one]
  by_cases h_case : k - 2 * i = 0
  · have hk_eq : k = 2 * i := by
      have h_le : 2 * i ≤ k := member_range_double_le k i hi
      omega
    have hi_pos : 1 ≤ i := by
      have h_le : 2 * i ≤ k := member_range_double_le k i hi
      omega
    rw [hk_eq]
    have h_sub : 2 * i - 2 * i = 0 := by omega
    rw [h_sub, pow_zero, mul_one]
    have h_choose : ((2 * i).choose i : ℤ) = 2 * ((2 * i - 1).choose i : ℤ) := by
      norm_cast
      exact choose_two_mul_even i hi_pos
    rw [h_choose]
    use ((2 * i - 1).choose i : ℤ) * ((2 * i - i).choose i : ℤ)
    ring
  · have hk_gt : 1 ≤ k - 2 * i := by omega
    generalize hm : k - 2 * i - 1 = m
    have h_eq : k - 2 * i = m + 1 := by omega
    have h_pow : (4 : ℤ) ^ (k - 2 * i) = 2 * (2 * 4 ^ m) := by
      rw [h_eq, pow_succ]
      ring
    rw [h_pow, ← hm]
    use ((k.choose i : ℤ) * ((k - i).choose i : ℤ)) * (2 * 4 ^ (k - 2 * i - 1))
    ring

lemma pow_sub_succ_six (n k : ℕ) (hk : k < n) :
  ((-6 : ℤ) ^ (n - k)) = -6 * (-6 : ℤ) ^ (n - 1 - k) := by
  have h1 : n - k = (n - 1 - k) + 1 := by omega
  rw [h1, pow_succ]
  ring

def S_sum (n : ℕ) : ℤ :=
  (range n).sum fun k : ℕ =>
    let k_int : ℤ := k.cast
    let coeff_a : ℤ := T_coeff k 4 1
    let coeff_b : ℤ := T_coeff k 1 (-1)
    let term_1 := (40 * k_int + 27)
    let term_3_exp : ℕ := n - 1 - k
    let term_3 := ((-6) : ℤ) ^ term_3_exp
    term_1 * term_3 * coeff_a * (coeff_b ^ 2)

lemma S_sum_recurrence (n : ℕ) :
  S_sum (n + 1) = -6 * S_sum n + (40 * (n : ℤ) + 27) * T_coeff n 4 1 * (T_coeff n 1 (-1) ^ 2) := by
  dsimp [S_sum]
  rw [sum_range_succ]
  have h_sum : (range n).sum (fun k => (40 * (k : ℤ) + 27) * ((-6 : ℤ) ^ (n - k)) * T_coeff k 4 1 * T_coeff k 1 (-1) ^ 2) =
               -6 * (range n).sum (fun k => (40 * (k : ℤ) + 27) * ((-6 : ℤ) ^ (n - 1 - k)) * T_coeff k 4 1 * T_coeff k 1 (-1) ^ 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hk_lt : k < n := hk
    have h_pow : ((-6 : ℤ) ^ (n - k)) = -6 * ((-6 : ℤ) ^ (n - 1 - k)) := by
      exact pow_sub_succ_six n k hk_lt
    rw [h_pow]
    ring
  rw [h_sum]
  have h_last : n - n = 0 := by omega
  rw [h_last, pow_zero, mul_one]

lemma S_sum_even (n : ℕ) (hn : 3 ≤ n) : 2 ∣ S_sum n := by
  dsimp [S_sum]
  apply Finset.dvd_sum
  intro k hk
  rw [mem_range] at hk
  by_cases hk_zero : k = 0
  · rw [hk_zero]
    have h_eq : n - 1 - 0 = n - 1 := by omega
    have hn1 : 2 ≤ n - 1 := by omega
    have h_six : 2 ∣ (-6 : ℤ) ^ (n - 1) := by
      have h_eq2 : n - 1 = (n - 2) + 1 := by omega
      rw [h_eq2, pow_succ]
      use -3 * (-6 : ℤ) ^ (n - 2)
      ring
    rcases h_six with ⟨q, hq⟩
    use 27 * q * T_coeff 0 4 1 * (T_coeff 0 1 (-1) ^ 2)
    rw [h_eq, hq]
    ring
  · have hk_pos : 1 ≤ k := by omega
    have h_coeff : 2 ∣ T_coeff k 4 1 := T_coeff_even k hk_pos
    rcases h_coeff with ⟨q, hq⟩
    use (40 * (k : ℤ) + 27) * (-6 : ℤ) ^ (n - 1 - k) * q * (T_coeff k 1 (-1) ^ 2)
    rw [hq]
    ring

-- Remaining placeholder theorems for A329073 omitted for brevity, as requested.

/--
A329073 Conjecture 2: (i) For any n > 0, the number b(n):=(1/n)*Sum_{k=0..n-1} (40k+27)*(-6)^(n-1-k)*T_k(4,1)*T_k(1,-1)^2 is an integer. Moreover, b(n) is odd if and only if n is a power of two.
-/
theorem oeis_329073_conjecture_2_i :
  ∀ (n : ℕ), 0 < n →
  (A329073_b n = A329073_b n) ∧ -- The definition of A329073_b uses integer division, implying the first part of the conjecture is an integrality statement on the quotient, which is implicitly handled by the `ℤ` return type. We should state the divisibility explicitly to make it a statement about $\mathbb{Z}$-valued functions, but since the sequence is defined using integer division and we are formalizing the conjecture about the existence of an integer value, we should focus on the property of the quotient being an integer. In combinatorics contexts, stating a rational number is an integer often means the numerator is divisible by the denominator.
  -- Let's rephrase the first part of the conjecture "b(n) is an integer" as the fact that the division is exact.
  -- b(n) is always an integer if its definition is $(1/n) * \text{Sum} \dots \in \mathbb{Z}$.
  -- The expression `sum_val / N_int` is $\lfloor \frac{\text{sum}}{n} \rfloor$.
  -- The conjecture is that $\text{sum}$ is divisible by $n$.
  ((n.cast : ℤ) ∣ ( (range n).sum fun k : ℕ =>
    let k_int : ℤ := k.cast
    let coeff_a : ℤ := T_coeff k 4 1
    let coeff_b : ℤ := T_coeff k 1 (-1)
    let term_1 := (40 * k_int + 27)
    let term_3_exp : ℕ := n - 1 - k
    let term_3 := ((-6) : ℤ) ^ term_3_exp
    term_1 * term_3 * coeff_a * (coeff_b ^ 2) )) ∧
  -- Moreover b(n) is odd if and only if n is a power of two.
  (A329073_b n % 2 = 1 ↔ Nat.isPowerOfTwo n)
  := by
    intro n hn
    rcases n with _ | _ | _ | n
    · contradiction
    · refine ⟨rfl, ?_, ?_⟩
      · decide
      · have h_lhs : A329073_b 1 % 2 = 1 := by decide
        have h_rhs : Nat.isPowerOfTwo 1 := ⟨0, by decide⟩
        exact ⟨fun _ => h_rhs, fun _ => h_lhs⟩
    · refine ⟨rfl, ?_, ?_⟩
      · decide
      · have h_lhs : A329073_b 2 % 2 = 1 := by decide
        have h_rhs : Nat.isPowerOfTwo 2 := ⟨1, by decide⟩
        exact ⟨fun _ => h_rhs, fun _ => h_lhs⟩
    · refine ⟨rfl, ?divisibility, ?parity⟩
      · sorry
      · sorry
