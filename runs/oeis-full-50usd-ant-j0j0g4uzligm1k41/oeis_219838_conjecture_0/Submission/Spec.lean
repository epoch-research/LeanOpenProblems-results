import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A219838: Number of ways to write $n$ as $x + y$ with $0 < x \le y$ and $(xy)^2 + xy + 1$ prime.
The constraints $x+y=n$, $0 < x \le y$ are equivalent to $1 \le x \le n/2$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 (n / 2)).sum fun x : ℕ =>
    let xy_prod := x * (n - x)
    if Nat.Prime (xy_prod ^ 2 + xy_prod + 1) then 1 else 0

/--
Key reduction: if there is a witness `x ∈ Icc 1 (n / 2)` for which
`(x * (n - x)) ^ 2 + x * (n - x) + 1` is prime, then `a n > 0`.
-/
theorem a_pos_of_witness (n x : ℕ) (hx : x ∈ Icc 1 (n / 2))
    (hp : Nat.Prime ((x * (n - x)) ^ 2 + x * (n - x) + 1)) : a n > 0 := by
  unfold a
  apply Finset.sum_pos'
  · intro i _; positivity
  · exact ⟨x, hx, by simp [hp]⟩

/-- Conversely, `a n > 0` provides an explicit witness `x ∈ Icc 1 (n / 2)`. -/
theorem exists_witness_of_a_pos (n : ℕ) (h : a n > 0) :
    ∃ x ∈ Icc 1 (n / 2), Nat.Prime ((x * (n - x)) ^ 2 + x * (n - x) + 1) := by
  unfold a at h
  by_contra hcon
  push_neg at hcon
  rw [Finset.sum_eq_zero] at h
  · exact absurd h (lt_irrefl 0)
  · intro x hx
    simp only
    rw [if_neg (hcon x hx)]

/-- Any witness `x ∈ Icc 1 (n / 2)` (with `n ≥ 2`) has product `x (n - x) ≥ n - 1`. -/
theorem witness_prod_ge (n x : ℕ) (hn : 2 ≤ n) (h1 : 1 ≤ x) (h2 : x ≤ n / 2) :
    n - 1 ≤ x * (n - x) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le h1
  have hm : 1 ≤ n - (1 + p) := by omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hm
  rw [hq]
  have hn2 : n - 1 = p + q + 1 := by omega
  rw [hn2]
  nlinarith [Nat.zero_le (p * q)]

/--
**Obstruction theorem.** The conjecture `∀ n > 1, a n > 0` *implies* that there are
infinitely many primes of the form `t² + t + 1`.  (Indeed every `n` provides a witness
`t = x (n - x) ≥ n - 1`, so these primes are unbounded.)  The infinitude of primes
`t² + t + 1` is the **open Bunyakovsky / Hardy–Littlewood Conjecture F** for the
polynomial `x² + x + 1`, which is unsolved (no irreducible polynomial of degree ≥ 2 is
known to take infinitely many prime values; Selberg's parity barrier obstructs sieve
methods).  Consequently, a complete proof of `oeis_219838_conjecture_0` below is
impossible with currently-available mathematics, since composing it with this theorem
would resolve that famous open problem.
-/
theorem conjecture_implies_open_problem
    (H : ∀ (n : ℕ), n > 1 → a n > 0) :
    {t : ℕ | Nat.Prime (t ^ 2 + t + 1)}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨x, hx, hp⟩ := exists_witness_of_a_pos (N + 2) (H (N + 2) (by omega))
  rw [Finset.mem_Icc] at hx
  refine ⟨x * (N + 2 - x), hp, ?_⟩
  have := witness_prod_ge (N + 2) x (by omega) hx.1 hx.2
  omega

/--
Provable sub-case: the witness `x = 1` (giving `t = n - 1` and value `n² - n + 1`)
works whenever `n² - n + 1` is prime. This covers a (heuristically positive-density)
set of `n`, but NOT all `n` (e.g. `n = 10` has `n²-n+1 = 91 = 7·13`, requiring `x = 3`).
-/
theorem oeis_219838_witness_one (n : ℕ) (hn : n > 1)
    (hp : Nat.Prime ((n - 1) ^ 2 + (n - 1) + 1)) : a n > 0 := by
  refine a_pos_of_witness n 1 ?_ ?_
  · rw [Finset.mem_Icc]
    exact ⟨le_refl 1, by omega⟩
  · have h1 : 1 * (n - 1) = n - 1 := by ring
    rw [h1]; exact hp

/--
Conjecture: a(n) > 0 for all n > 1.
-/
theorem oeis_219838_conjecture_0 : ∀ (n : ℕ), n > 1 → a n > 0 := by
  intro n hn
  -- By `a_pos_of_witness`, it suffices to find one `x ∈ Icc 1 (n / 2)`
  -- with `(x*(n-x))^2 + x*(n-x) + 1` prime.
  suffices h : ∃ x ∈ Icc 1 (n / 2), Nat.Prime ((x * (n - x)) ^ 2 + x * (n - x) + 1) by
    obtain ⟨x, hx, hp⟩ := h
    exact a_pos_of_witness n x hx hp
  sorry
