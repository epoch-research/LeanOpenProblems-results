import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308734: Number of ordered ways to write $n$ as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$,
where $a,b,c,d,x,y$ are nonnegative integers with $x \le y$.

Note: The provided definition uses a computationally convenient, but potentially insufficient, range `M` for the exponents $a, b, c, d$.
A mathematically precise definition would use unbounded natural numbers for $a, b, c, d, x, y$ and count the size of the resulting set.
We proceed with the definition as given in the prompt.
-/
def A308734 (n : ℕ) : ℕ :=
  -- We use a six-fold nested summation over a range $M$.
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0


lemma A308734_pos_of_exists (n : ℕ)
    (h : ∃ a ∈ range (Nat.sqrt n + 1), ∃ b ∈ range (Nat.sqrt n + 1),
      ∃ c ∈ range (Nat.sqrt n + 1), ∃ d ∈ range (Nat.sqrt n + 1),
      ∃ x ∈ range (Nat.sqrt n + 1), ∃ y ∈ range (Nat.sqrt n + 1),
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y) :
    A308734 n > 0 := by
  rcases h with ⟨a, ha, b, hb, c, hc, d, hd, x, hx, y, hy, hEq, hxy⟩
  unfold A308734
  set M := Nat.sqrt n + 1
  change 0 < Finset.sum (range M) fun a =>
    Finset.sum (range M) fun b =>
    Finset.sum (range M) fun c =>
    Finset.sum (range M) fun d =>
    Finset.sum (range M) fun x =>
    Finset.sum (range M) fun y =>
      (let term1 := (2^a * 3^b)^2
       let term2 := (2^c * 5^d)^2
       if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
  apply Finset.sum_pos'
  · intro a ha; positivity
  · refine ⟨a, by simpa [M] using ha, ?_⟩
    apply Finset.sum_pos'
    · intro b hb; positivity
    · refine ⟨b, by simpa [M] using hb, ?_⟩
      apply Finset.sum_pos'
      · intro c hc; positivity
      · refine ⟨c, by simpa [M] using hc, ?_⟩
        apply Finset.sum_pos'
        · intro d hd; positivity
        · refine ⟨d, by simpa [M] using hd, ?_⟩
          apply Finset.sum_pos'
          · intro x hx; positivity
          · refine ⟨x, by simpa [M] using hx, ?_⟩
            apply Finset.sum_pos'
            · intro y hy
              by_cases hif : (let term1 := (2^a * 3^b)^2
                let term2 := (2^c * 5^d)^2
                term1 + term2 + x^2 + y^2 = n ∧ x ≤ y)
              · simp [hif]
              · simp [hif]
            · refine ⟨y, by simpa [M] using hy, ?_⟩
              simp [hEq, hxy]


lemma exp_mem_range_sqrt_add_one_of_base_sq_le (n base e : ℕ)
    (hbase : e ≤ base) (hle : base ^ 2 ≤ n) :
    e ∈ range (Nat.sqrt n + 1) := by
  rw [Finset.mem_range]
  exact Nat.lt_succ_iff.mpr (hbase.trans ((Nat.le_sqrt').mpr hle))

lemma A308734_pos_of_exists_unbounded (n : ℕ)
    (h : ∃ a b c d x y : ℕ,
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y) :
    A308734 n > 0 := by
  rcases h with ⟨a, b, c, d, x, y, hEq, hxy⟩
  apply A308734_pos_of_exists
  refine ⟨a, ?_, b, ?_, c, ?_, d, ?_, x, ?_, y, ?_, hEq, hxy⟩
  · apply exp_mem_range_sqrt_add_one_of_base_sq_le n (2^a * 3^b) a
    · exact (le_of_lt a.lt_two_pow_self).trans
        (Nat.le_mul_of_pos_right (2^a) (by positivity : 0 < 3^b))
    · rw [← hEq]
      nlinarith [show (2^a * 3^b)^2 ≤
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 by omega]
  · apply exp_mem_range_sqrt_add_one_of_base_sq_le n (2^a * 3^b) b
    · exact ((le_of_lt b.lt_two_pow_self).trans
        (Nat.pow_le_pow_left (by norm_num : 2 ≤ 3) b)).trans
        (Nat.le_mul_of_pos_left (3^b) (by positivity : 0 < 2^a))
    · rw [← hEq]
      nlinarith [show (2^a * 3^b)^2 ≤
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 by omega]
  · apply exp_mem_range_sqrt_add_one_of_base_sq_le n (2^c * 5^d) c
    · exact (le_of_lt c.lt_two_pow_self).trans
        (Nat.le_mul_of_pos_right (2^c) (by positivity : 0 < 5^d))
    · rw [← hEq]
      nlinarith [show (2^c * 5^d)^2 ≤
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 by omega]
  · apply exp_mem_range_sqrt_add_one_of_base_sq_le n (2^c * 5^d) d
    · exact ((le_of_lt d.lt_two_pow_self).trans
        (Nat.pow_le_pow_left (by norm_num : 2 ≤ 5) d)).trans
        (Nat.le_mul_of_pos_left (5^d) (by positivity : 0 < 2^c))
    · rw [← hEq]
      nlinarith [show (2^c * 5^d)^2 ≤
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 by omega]
  · rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr ((Nat.le_sqrt').mpr (by
      rw [← hEq]
      nlinarith [show x^2 ≤
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 by omega]))
  · rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr ((Nat.le_sqrt').mpr (by
      rw [← hEq]
      nlinarith [show y^2 ≤
        (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 by omega]))


def A308734Rep (n : ℕ) : Prop :=
  ∃ a b c d x y : ℕ,
    (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y

lemma A308734Rep.mul_four {n : ℕ} (h : A308734Rep n) : A308734Rep (4 * n) := by
  rcases h with ⟨a, b, c, d, x, y, hEq, hxy⟩
  refine ⟨a + 1, b, c + 1, d, 2 * x, 2 * y, ?_, by omega⟩
  rw [← hEq]
  have h1 : (2 ^ (a + 1) * 3 ^ b) ^ 2 = 4 * (2 ^ a * 3 ^ b) ^ 2 := by
    ring_nf
  have h2 : (2 ^ (c + 1) * 5 ^ d) ^ 2 = 4 * (2 ^ c * 5 ^ d) ^ 2 := by
    ring_nf
  rw [h1, h2]
  ring

lemma A308734_pos_of_rep {n : ℕ} (h : A308734Rep n) : A308734 n > 0 :=
  A308734_pos_of_exists_unbounded n h


/--
Four-square Conjecture: a(n) > 0 for all n > 1.
This is much stronger than Lagrange's four-square theorem.
(OEIS A308734, Comment C2)
-/
theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  sorry
