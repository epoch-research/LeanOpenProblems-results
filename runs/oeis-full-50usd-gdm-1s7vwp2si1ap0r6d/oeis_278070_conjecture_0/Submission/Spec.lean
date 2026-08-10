import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A278070: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.
-/
def A278070 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)

/--
We conjecture that a(n+k) == a(n) (mod k) for all n and k.
If true, then for each k, the sequence a(n) taken modulo k is a periodic sequence and the period divides k.
For example, modulo 7 the sequence becomes [1, 2, 4, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2, ...], apparently a periodic sequence of period 7.
-/
def T (n k : ℕ) : ℕ :=
  (n.choose k) * ((n + k).pred.choose k) * (k.factorial)

lemma A278070_eq_sum_T (n : ℕ) : A278070 n = (Finset.range (n + 1)).sum (fun k => T n k) := rfl

theorem T_eq_choose_mul_ascFactorial (n k : ℕ) : T n k = n.choose k * n.ascFactorial k := by
  unfold T
  rw [mul_assoc]
  have h2 : n.ascFactorial k = ((n + k).pred.choose k) * k.factorial := by
    have hpred : (n + k).pred = n + k - 1 := rfl
    rw [hpred, mul_comm]
    exact ascFactorial_eq_factorial_mul_choose' n k
  rw [h2]

lemma ascFactorial_congr (n d k : ℕ) : Nat.ModEq d ((n + d).ascFactorial k) (n.ascFactorial k) := by
  induction k with
  | zero =>
    rw [ascFactorial_zero, ascFactorial_zero]
  | succ k ih =>
    rw [ascFactorial_succ, ascFactorial_succ]
    have h1 : Nat.ModEq d (n + d + k) (n + k) := by
      change (n + d + k) % d = (n + k) % d
      have h_eq : n + d + k = n + k + d := by omega
      rw [h_eq, Nat.add_mod_right]
    exact Nat.ModEq.mul h1 ih

lemma descFactorial_congr (n d k : ℕ) : Nat.ModEq d ((n + d).descFactorial k) (n.descFactorial k) := by
  induction k with
  | zero =>
    rw [descFactorial_zero, descFactorial_zero]
  | succ k ih =>
    rw [descFactorial_succ, descFactorial_succ]
    by_cases hnk : n < k
    · have h1 : n.descFactorial k = 0 := descFactorial_of_lt hnk
      have h2 : n - k = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [h1, h2, mul_zero]
      have h_ih : (n + d).descFactorial k % d = 0 := by
        rw [ih, h1]
        rfl
      change ((n + d - k) * (n + d).descFactorial k) % d = 0
      rw [Nat.mul_mod, h_ih, mul_zero, zero_mod]
    · have h_eq : n + d - k = n - k + d := by omega
      have h_congr : Nat.ModEq d (n + d - k) (n - k) := by
        change (n + d - k) % d = (n - k) % d
        rw [h_eq, Nat.add_mod_right]
      exact Nat.ModEq.mul h_congr ih

theorem T_congr (n d k : ℕ) : Nat.ModEq d (T (n + d) k) (T n k) := by
  rw [T_eq_choose_mul_ascFactorial, T_eq_choose_mul_ascFactorial]
  have h_step1 : Nat.ModEq d ((n + d).choose k * (n + d).ascFactorial k) ((n + d).choose k * n.ascFactorial k) := by
    exact Nat.ModEq.mul_left _ (ascFactorial_congr n d k)
  refine Nat.ModEq.trans h_step1 ?_
  have h_asc : n.ascFactorial k = k.factorial * (n + k - 1).choose k := ascFactorial_eq_factorial_mul_choose' n k
  rw [h_asc]
  have h_desc1 : (n + d).choose k * k.factorial = (n + d).descFactorial k := by
    rw [mul_comm, ← descFactorial_eq_factorial_mul_choose]
  have h_desc2 : n.choose k * k.factorial = n.descFactorial k := by
    rw [mul_comm, ← descFactorial_eq_factorial_mul_choose]
  have h_lhs : (n + d).choose k * (k.factorial * (n + k - 1).choose k) = (n + d).descFactorial k * (n + k - 1).choose k := by
    rw [← mul_assoc, h_desc1]
  have h_rhs : n.choose k * (k.factorial * (n + k - 1).choose k) = n.descFactorial k * (n + k - 1).choose k := by
    rw [← mul_assoc, h_desc2]
  rw [h_lhs, h_rhs]
  exact Nat.ModEq.mul_right _ (descFactorial_congr n d k)

lemma T_eq_zero_of_lt (n k : ℕ) (h : n < k) : T n k = 0 := by
  unfold T
  rw [Nat.choose_eq_zero_of_lt h]
  ring

lemma sum_T_range_eq (n d : ℕ) : (Finset.range (n + d + 1)).sum (fun k => T n k) = (Finset.range (n + 1)).sum (fun k => T n k) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have h_eq : n + d.succ + 1 = (n + d + 1) + 1 := by omega
    rw [h_eq, Finset.sum_range_succ]
    have h_zero : T n (n + d + 1) = 0 := T_eq_zero_of_lt n (n + d + 1) (by omega)
    rw [h_zero, add_zero]
    exact ih

lemma sum_modEq {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → ℕ) (d : ℕ) (h : ∀ x ∈ s, Nat.ModEq d (f x) (g x)) :
    Nat.ModEq d (s.sum f) (s.sum g) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    have h_ih : Nat.ModEq d (s.sum f) (s.sum g) := by
      apply ih
      intro x hx_mem
      apply h
      exact mem_insert_of_mem hx_mem
    have h_a : Nat.ModEq d (f a) (g a) := by
      apply h
      exact mem_insert_self _ _
    exact Nat.ModEq.add h_a h_ih

/--
We conjecture that a(n+k) == a(n) (mod k) for all n and k.
If true, then for each k, the sequence a(n) taken modulo k is a periodic sequence and the period divides k.
For example, modulo 7 the sequence becomes [1, 2, 4, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2, ...], apparently a periodic sequence of period 7.
-/
theorem oeis_278070_conjecture_0 : ∀ (n k : ℕ), Nat.ModEq k (A278070 (n + k)) (A278070 n) := by
  intro n k
  by_cases hd : k = 0
  · rw [hd, add_zero]
  rw [A278070_eq_sum_T, A278070_eq_sum_T]
  have h_sum_congr : Nat.ModEq k ((Finset.range (n + k + 1)).sum (fun j => T (n + k) j)) ((Finset.range (n + k + 1)).sum (fun j => T n j)) := by
    apply sum_modEq
    intro j _
    exact T_congr n k j
  refine Nat.ModEq.trans h_sum_congr ?_
  rw [sum_T_range_eq]
