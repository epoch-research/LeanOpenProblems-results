import FormalConjectures.Util.ProblemImports
open Nat Finset
set_option maxRecDepth 200000

/--
The $k$-th prime number, $p_k$, with $p_1=2$. This is $\operatorname{prime}(k)$ from the OEIS description.
-/
noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/--
A237348: Number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $\mathrm{prime}(k) + 4$ and $\mathrm{prime}(\mathrm{prime}(m)) + 4$ are both prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sum is over $k$ such that $1 \le k \le n - 1$.
  -- This range ensures $k > 0$ and $m = n - k > 0$.
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 4)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 4)

    if cond1 ∧ cond2 then 1 else 0

/--
A generalization of A237348 to a general even number $2d$.
The number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/
noncomputable def a_generalized (n d : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 2 * d)

    if cond1 ∧ cond2 then 1 else 0


lemma prime_1 : prime_k_1indexed 1 = 2 := by unfold prime_k_1indexed; exact Nat.nth_prime_zero_eq_two
lemma prime_2 : prime_k_1indexed 2 = 3 := by unfold prime_k_1indexed; exact Nat.nth_prime_one_eq_three
lemma prime_3 : prime_k_1indexed 3 = 5 := by unfold prime_k_1indexed; exact Nat.nth_prime_two_eq_five
lemma prime_4 : prime_k_1indexed 4 = 7 := by unfold prime_k_1indexed; exact Nat.nth_prime_three_eq_seven
lemma prime_5 : prime_k_1indexed 5 = 11 := by unfold prime_k_1indexed; exact Nat.nth_prime_four_eq_eleven

lemma prime_6 : prime_k_1indexed 6 = 13 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 13 := by decide
  have h2 : Nat.count Nat.Prime 13 = 5 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_7 : prime_k_1indexed 7 = 17 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 17 := by decide
  have h2 : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_8 : prime_k_1indexed 8 = 19 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 19 := by decide
  have h2 : Nat.count Nat.Prime 19 = 7 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_9 : prime_k_1indexed 9 = 23 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 23 := by decide
  have h2 : Nat.count Nat.Prime 23 = 8 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_10 : prime_k_1indexed 10 = 29 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 29 := by decide
  have h2 : Nat.count Nat.Prime 29 = 9 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_11 : prime_k_1indexed 11 = 31 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 31 := by decide
  have h2 : Nat.count Nat.Prime 31 = 10 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_12 : prime_k_1indexed 12 = 37 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 37 := by decide
  have h2 : Nat.count Nat.Prime 37 = 11 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_13 : prime_k_1indexed 13 = 41 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 41 := by decide
  have h2 : Nat.count Nat.Prime 41 = 12 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_23 : prime_k_1indexed 23 = 83 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 83 := by decide
  have h2 : Nat.count Nat.Prime 83 = 22 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_31 : prime_k_1indexed 31 = 127 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 127 := by decide
  have h2 : Nat.count Nat.Prime 127 = 30 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_37 : prime_k_1indexed 37 = 157 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 157 := by decide
  have h2 : Nat.count Nat.Prime 157 = 36 := by decide
  rw [← Nat.nth_count h1]; rw [h2]


lemma prime_14 : prime_k_1indexed 14 = 43 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 43 := by decide
  have h2 : Nat.count Nat.Prime 43 = 13 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_29 : prime_k_1indexed 29 = 109 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 109 := by decide
  have h2 : Nat.count Nat.Prime 109 = 28 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

lemma prime_41 : prime_k_1indexed 41 = 179 := by
  unfold prime_k_1indexed
  have h1 : Nat.Prime 179 := by decide
  have h2 : Nat.count Nat.Prime 179 = 40 := by decide
  rw [← Nat.nth_count h1]; rw [h2]

theorem a_generalized_14_4_eq_zero : a_generalized 14 4 = 0 := by
  unfold a_generalized
  simp
  intro k hk_ge hk_lt h_cond1
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [prime_1] at h_cond1
    have h_sum : 2 + 8 = 10 := rfl
    have h_not : ¬ Nat.Prime 10 := by
      have h_mul : 10 = 2 * 5 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_2] at h_cond1
    rw [prime_12, prime_37]
    have h_sum : 157 + 8 = 165 := rfl
    have h_not : ¬ Nat.Prime 165 := by
      have h_mul : 165 = 5 * 33 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_3] at h_cond1
    rw [prime_11, prime_31]
    have h_sum : 127 + 8 = 135 := rfl
    have h_not : ¬ Nat.Prime 135 := by
      have h_mul : 135 = 5 * 27 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_4] at h_cond1
    have h_sum : 7 + 8 = 15 := rfl
    have h_not : ¬ Nat.Prime 15 := by
      have h_mul : 15 = 3 * 5 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_5] at h_cond1
    rw [prime_9, prime_23]
    have h_sum : 83 + 8 = 91 := rfl
    have h_not : ¬ Nat.Prime 91 := by
      have h_mul : 91 = 7 * 13 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_6] at h_cond1
    have h_sum : 13 + 8 = 21 := rfl
    have h_not : ¬ Nat.Prime 21 := by
      have h_mul : 21 = 3 * 7 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_7] at h_cond1
    have h_sum : 17 + 8 = 25 := rfl
    have h_not : ¬ Nat.Prime 25 := by
      have h_mul : 25 = 5 * 5 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_8] at h_cond1
    have h_sum : 19 + 8 = 27 := rfl
    have h_not : ¬ Nat.Prime 27 := by
      have h_mul : 27 = 3 * 9 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_9] at h_cond1
    rw [prime_5, prime_11]
    have h_not : ¬ Nat.Prime (31 + 8) := by
      have h_mul : 31 + 8 = 3 * 13 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    intro h_cond2; contradiction
  · rw [prime_10] at h_cond1
    rw [prime_4, prime_7]
    have h_not : ¬ Nat.Prime (17 + 8) := by
      have h_mul : 17 + 8 = 5 * 5 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    intro h_cond2; contradiction
  · rw [prime_11] at h_cond1
    have h_not : ¬ Nat.Prime (31 + 8) := by
      have h_mul : 31 + 8 = 3 * 13 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    contradiction
  · rw [prime_12] at h_cond1
    have h_not : ¬ Nat.Prime (37 + 8) := by
      have h_mul : 37 + 8 = 5 * 9 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    contradiction
  · rw [prime_13] at h_cond1
    have h_not : ¬ Nat.Prime (41 + 8) := by
      have h_mul : 41 + 8 = 7 * 7 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    contradiction

theorem a_generalized_15_4_eq_zero : a_generalized 15 4 = 0 := by
  unfold a_generalized
  simp
  intro k hk_ge hk_lt h_cond1
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [prime_1] at h_cond1
    have h_sum : 2 + 8 = 10 := rfl
    have h_not : ¬ Nat.Prime 10 := by
      have h_mul : 10 = 2 * 5 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_2] at h_cond1
    rw [prime_13, prime_41]
    have h_sum : 179 + 8 = 187 := rfl
    have h_not : ¬ Nat.Prime 187 := by
      have h_mul : 187 = 11 * 17 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_3] at h_cond1
    rw [prime_12, prime_37]
    have h_sum : 157 + 8 = 165 := rfl
    have h_not : ¬ Nat.Prime 165 := by
      have h_mul : 165 = 5 * 33 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_4] at h_cond1
    have h_sum : 7 + 8 = 15 := rfl
    have h_not : ¬ Nat.Prime 15 := by
      have h_mul : 15 = 3 * 5 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_5] at h_cond1
    rw [prime_10, prime_29]
    have h_sum : 109 + 8 = 117 := rfl
    have h_not : ¬ Nat.Prime 117 := by
      have h_mul : 117 = 9 * 13 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_6] at h_cond1
    have h_sum : 13 + 8 = 21 := rfl
    have h_not : ¬ Nat.Prime 21 := by
      have h_mul : 21 = 3 * 7 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_7] at h_cond1
    have h_sum : 17 + 8 = 25 := rfl
    have h_not : ¬ Nat.Prime 25 := by
      have h_mul : 25 = 5 * 5 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_8] at h_cond1
    have h_sum : 19 + 8 = 27 := rfl
    have h_not : ¬ Nat.Prime 27 := by
      have h_mul : 27 = 3 * 9 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum] at h_cond1
    contradiction
  · rw [prime_9] at h_cond1
    rw [prime_6, prime_13]
    have h_sum : 41 + 8 = 49 := rfl
    have h_not : ¬ Nat.Prime 49 := by
      have h_mul : 49 = 7 * 7 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_10] at h_cond1
    rw [prime_5, prime_11]
    have h_sum : 31 + 8 = 39 := rfl
    have h_not : ¬ Nat.Prime 39 := by
      have h_mul : 39 = 3 * 13 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    rw [h_sum]
    intro h_cond2; contradiction
  · rw [prime_11] at h_cond1
    have h_not : ¬ Nat.Prime (31 + 8) := by
      have h_mul : 31 + 8 = 3 * 13 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    contradiction
  · rw [prime_12] at h_cond1
    have h_not : ¬ Nat.Prime (37 + 8) := by
      have h_mul : 37 + 8 = 5 * 9 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    contradiction
  · rw [prime_13] at h_cond1
    have h_not : ¬ Nat.Prime (41 + 8) := by
      have h_mul : 41 + 8 = 7 * 7 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    contradiction
  · rw [prime_14] at h_cond1
    have h_not : ¬ Nat.Prime (43 + 8) := by
      have h_mul : 43 + 8 = 3 * 17 := rfl
      rw [h_mul]; apply Nat.not_prime_mul <;> decide
    contradiction


/--
OEIS A237348 Conjecture: For each $d = 1, 2, 3, \dots$ there is a positive integer $N(d)$
for which any integer $n > N(d)$ can be written as $k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/
theorem oeis_237348_conjecture_0.disproof :
  ¬ (∀ (d : ℕ), 1 ≤ d →
      ∃ (N : ℕ), 0 < N ∧
        ∀ (n : ℕ), N < n →
          0 < a_generalized n d) := by
  intro h
  have h4 := h 4 (by decide)
  rcases h4 with ⟨N, hN_gt, hN⟩
  have h14 : a_generalized 14 4 = 0 := a_generalized_14_4_eq_zero
  have h15 : a_generalized 15 4 = 0 := a_generalized_15_4_eq_zero
  have hN_cases : N < 14 ∨ N = 14 ∨ N ≥ 15 := by omega
  rcases hN_cases with hN_lt | hN_eq | hN_ge
  · have h14_gt : N < 14 := hN_lt
    have h14_pos := hN 14 h14_gt
    rw [h14] at h14_pos
    exact Nat.lt_irrefl 0 h14_pos
  · have h15_gt : N < 15 := by omega
    have h15_pos := hN 15 h15_gt
    rw [h15] at h15_pos
    exact Nat.lt_irrefl 0 h15_pos
  · sorry

