import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A271099: Number of ordered ways to write $n$ as $u^3 + v^3 + 2x^3 + 2y^3 + 3z^3$,
where $u, v, x, y$ and $z$ are nonnegative integers with $u \le v$ and $x \le y$.
-/
def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)

  -- Sum over all 5-tuples of natural numbers in the range [0, n].
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

/--
The set of natural numbers $n$ for which $A271099(n) = 1$.
Conjecture: $A271099(n) = 1$ iff $n \in lone_count_set$.
-/
def A271099_lone_count_set : Finset ℕ :=
  {0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534}

/-!
## Strategy

We reduce the conjecture to a single "core" statement about all large `n`.

* For `n ≤ 534`, the value `A271099 n` is computed by `decide`/`native_decide`.
  Since any solution of `u^3 + v^3 + 2x^3 + 2y^3 + 3z^3 = n` with `n ≤ 534` has every
  variable `≤ 8` (because `9^3 = 729 > 534`), the quintuple sum over `range (n+1)`
  agrees with the quintuple sum over `range 9` (lemma `A271099_eq_Bspec`), which is
  cheap to evaluate.

* For `n > 534`, we need `A271099 n ≥ 2` (the analytic core `A271099_core`).  This
  gives both `A271099 n > 0` and `A271099 n ≠ 1`; and since every element of
  `A271099_lone_count_set` is `≤ 534`, also `n ∉ A271099_lone_count_set`.
-/

/-- The "small range" version of `A271099`, summing only over `range 9`. -/
private def Bspec (n : ℕ) : ℕ :=
  Finset.sum (range 9) fun u =>
  Finset.sum (range 9) fun v =>
  Finset.sum (range 9) fun x =>
  Finset.sum (range 9) fun y =>
  Finset.sum (range 9) fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then 1 else 0

/-- Replace the range `[0, n]` by `[0, 8]` for a summand that vanishes on indices `≥ 9`. -/
private lemma red (n : ℕ) (h8 : 9 ≤ n + 1) (f : ℕ → ℕ) (hf : ∀ k, 9 ≤ k → f k = 0) :
    (range (n + 1)).sum f = (range 9).sum f := by
  symm
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  · intro x hx hx'; rw [Finset.mem_range] at hx hx'; apply hf; omega

private lemma cube_big (k : ℕ) (hk : 9 ≤ k) : 729 ≤ k ^ 3 := by
  calc (729 : ℕ) = 9 ^ 3 := by norm_num
    _ ≤ k ^ 3 := Nat.pow_le_pow_left hk 3

/-- For `8 ≤ n ≤ 534`, the full count agrees with the small-range count. -/
private lemma A271099_eq_Bspec (n : ℕ) (hn : 8 ≤ n) (hn2 : n ≤ 534) :
    A271099 n = Bspec n := by
  unfold A271099 Bspec
  simp only []
  rw [red n (by omega)]
  · apply Finset.sum_congr rfl; intro u hu
    rw [red n (by omega)]
    · apply Finset.sum_congr rfl; intro v hv
      rw [red n (by omega)]
      · apply Finset.sum_congr rfl; intro x hx
        rw [red n (by omega)]
        · apply Finset.sum_congr rfl; intro y hy
          rw [red n (by omega)]
          intro z hz
          rw [if_neg]; rintro ⟨_, _, heq⟩; have := cube_big z hz; omega
        · intro y hy
          apply Finset.sum_eq_zero; intro z _
          rw [if_neg]; rintro ⟨_, _, heq⟩; have := cube_big y hy; omega
      · intro x hx
        apply Finset.sum_eq_zero; intro y _; apply Finset.sum_eq_zero; intro z _
        rw [if_neg]; rintro ⟨_, _, heq⟩; have := cube_big x hx; omega
    · intro v hv
      apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _
      apply Finset.sum_eq_zero; intro z _
      rw [if_neg]; rintro ⟨_, _, heq⟩; have := cube_big v hv; omega
  · intro u hu
    apply Finset.sum_eq_zero; intro v _; apply Finset.sum_eq_zero; intro x _
    apply Finset.sum_eq_zero; intro y _; apply Finset.sum_eq_zero; intro z _
    rw [if_neg]; rintro ⟨_, _, heq⟩; have := cube_big u hu; omega

/-- Finite verification for `n ≤ 7` (the range `[0, n]` is already small). -/
private lemma finA : ∀ n ∈ range 8,
    0 < A271099 n ∧ (A271099 n = 1 ↔ n ∈ A271099_lone_count_set) := by native_decide

/-- Finite verification for `8 ≤ n ≤ 534` (using the small-range count). -/
private lemma finB : ∀ n ∈ Finset.Icc 8 534,
    0 < Bspec n ∧ (Bspec n = 1 ↔ n ∈ A271099_lone_count_set) := by native_decide

/-- Combined finite verification for all `n ≤ 534`. -/
private lemma fin_all (n : ℕ) (hn : n ≤ 534) :
    0 < A271099 n ∧ (A271099 n = 1 ↔ n ∈ A271099_lone_count_set) := by
  rcases (by omega : n ≤ 7 ∨ 7 < n) with h | h
  · exact finA n (by simp only [Finset.mem_range]; omega)
  · have hb := finB n (by simp only [Finset.mem_Icc]; omega)
    rw [A271099_eq_Bspec n (by omega) hn]; exact hb

/-- The analytic core of Zhi-Wei Sun's conjecture A271099: every integer `n > 534` admits
at least two ordered representations as `u^3 + v^3 + 2x^3 + 2y^3 + 3z^3`.

This is a Waring-type statement for the 5-variable diagonal cubic form `(1,1,2,2,3)`. The
singular series is positive and the circle-method main term is `≍ n^{2/3} → ∞`, but the
form has only five cube variables, which is below the threshold (`s ≥ 7`, i.e. `G(3) ≤ 7`)
at which the circle method controls the error term pointwise; a pigeonhole reduction to
sums of four cubes plus `3z^3` would require the exceptional set of sums of four cubes to
be of size `o(n^{1/3})`, far beyond Davenport's bound.  It is an open problem.

It has been verified computationally for `534 < n ≤ 10^9` (every such `n` has at least two
representations; in fact the minimum number of representations grows like `n^{2/3}`). -/
private lemma A271099_core : ∀ n, 534 < n → 2 ≤ A271099 n := by
  sorry

/--
%C A271099 Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534.
-/
theorem oeis_a271099_conjecture_i :
  (∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ A271099_lone_count_set) :=
by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · -- Part (i): positivity.
    rcases (by omega : n ≤ 534 ∨ 534 < n) with h | h
    · exact (fin_all n h).1
    · have := A271099_core n h; omega
  · -- Part (ii): the lone-count characterisation.
    rcases (by omega : n ≤ 534 ∨ 534 < n) with h | h
    · exact (fin_all n h).2
    · have h2 := A271099_core n h
      have hns : n ∉ A271099_lone_count_set := by
        simp only [A271099_lone_count_set, Finset.mem_insert, Finset.mem_singleton]; omega
      constructor
      · intro he; omega
      · intro he; exact absurd he hns
