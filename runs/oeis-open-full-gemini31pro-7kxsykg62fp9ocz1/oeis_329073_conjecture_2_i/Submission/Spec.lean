import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

def T_coeff (k : ℕ) (b c : ℤ) : ℤ :=
  (range (k / 2 + 1)).sum fun i : ℕ =>
    let choose_term : ℤ := (k.choose i).cast * ((k - i).choose i).cast
    let b_pow : ℤ := b ^ (k - 2 * i)
    let c_pow : ℤ := c ^ i
    choose_term * b_pow * c_pow

def A329073 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | N@(_ + 1) =>
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

def A329073_b (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | N@(_ + 1) =>
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

theorem oeis_329073_conjecture_2_i :
  ∀ (n : ℕ), 0 < n →
  (A329073_b n = A329073_b n) ∧
  ((n.cast : ℤ) ∣ ( (range n).sum fun k : ℕ =>
    let k_int : ℤ := k.cast
    let coeff_a : ℤ := T_coeff k 4 1
    let coeff_b : ℤ := T_coeff k 1 (-1)
    let term_1 := (40 * k_int + 27)
    let term_3_exp : ℕ := n - 1 - k
    let term_3 := ((-6) : ℤ) ^ term_3_exp
    term_1 * term_3 * coeff_a * (coeff_b ^ 2) )) ∧
  (A329073_b n % 2 = 1 ↔ Nat.isPowerOfTwo n)
  := sorry

theorem oeis_329073_conjecture_2_i.disproof : ¬ (type_of% @oeis_329073_conjecture_2_i) := fun h =>
  let h_11 := h 11 (by decide)
  have _ : A329073_b 11 % 2 = 1 ↔ Nat.isPowerOfTwo 11 := h_11.2.2
  have _ : (-49013914467964 : ℤ) % 2 = 1 ↔ Nat.isPowerOfTwo 11 := by
    -- can I derive false?
    sorry
  sorry
