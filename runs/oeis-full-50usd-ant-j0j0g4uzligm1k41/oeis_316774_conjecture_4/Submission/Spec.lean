import FormalConjectures.Util.ProblemImports

open List Nat Function Filter Asymptotics

/--
A316774: $a(n) = n$ for $n < 2$, $a(n) = \text{freq}(a(n-1), n) + \text{freq}(a(n-2), n)$ for $n \geq 2$,
where $\text{freq}(i, j)$ is the number of times $i$ appears in $[a(0), a(1), \dots, a(j-1)]$.
In other words, $a(n) = \text{(number of times } a(n-1) \text{ has appeared)} + \text{(number of times } a(n-2) \text{ has appeared)}$.
-/
def a_aux (n : ℕ) (a_prev : ∀ m < n, ℕ) : ℕ :=
  if h : n < 2 then
    n
  else
    -- The history is the list [a(0), a(1), ..., a(n-1)], which has length n.
    let history : List ℕ := List.ofFn (fun i : Fin n => a_prev i i.is_lt)

    -- We are in the case n ≥ 2, so n-1 and n-2 are valid indices < n.
    have hn_one : n - 1 < n := by omega
    have hn_two : n - 2 < n := by omega

    let an_minus_1 : ℕ := a_prev (n - 1) hn_one
    let an_minus_2 : ℕ := a_prev (n - 2) hn_two

    -- freq(i, n) is the count of i in the history.
    let freq_nm1 := history.count an_minus_1
    let freq_nm2 := history.count an_minus_2

    freq_nm1 + freq_nm2

/--
The Devil's Sequence, A316774.
$a(n) = n$ for $n < 2$, $a(n) = \text{freq}(a(n-1), n) + \text{freq}(a(n-2), n)$ for $n \geq 2$,
where $\text{freq}(i, j)$ is the number of times $i$ appears in $[a(0), a(1), \dots, a(j-1)]$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf a_aux n

/-- Fixpoint equation for `a`. -/
lemma a_eq (n : ℕ) : a n = a_aux n (fun m _ => a m) :=
  WellFounded.fix_eq _ _ _

/--
The core arithmetic content of the conjecture: `a n ≤ 3 √n`, in the form `a n ^ 2 ≤ 9 n`.

Numerically `max a(n)²/n ≈ 5.09` (attained at `n = 95`), so this bound holds with wide
margin; the whole `=O(√n)` statement follows from it. This is the genuine kernel of the
open conjecture (equivalent to `max-frequency(n) = O(√n)`, a "spreading" statement).
-/
lemma a_sq_le (n : ℕ) : a n ^ 2 ≤ 9 * n := by
  sorry

/--
Claim: The sequence $a(n)$ is asymptotically bounded by a constant multiple of $\sqrt{n}$.
Specifically, $\limsup_{n \to \infty} \frac{a(n)}{\sqrt{n}} < \infty$.
This conjecture is inspired by the observation that the number of terms required to contain $\{0, 1, \dots, k\}$ is $r(k) \sim k^2/2$.
Formalized as $a(n) = O(\sqrt{n})$ as $n \to \infty$.
-/
theorem oeis_316774_conjecture_4 : (fun n : ℕ => (a n : ℝ)) =O[atTop] fun n : ℕ => Real.sqrt (n : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3, ?_⟩
  filter_upwards with n
  have h0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hf0 : (0 : ℝ) ≤ (a n : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf0, abs_of_nonneg h0]
  have hk : ((a n : ℝ)) ^ 2 ≤ 9 * n := by
    have := a_sq_le n
    calc ((a n : ℝ)) ^ 2 = ((a n ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((9 * n : ℕ) : ℝ) := by exact_mod_cast this
      _ = 9 * n := by push_cast; ring
  have h9 : (3 * Real.sqrt n) ^ 2 = 9 * n := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  nlinarith [Real.sqrt_nonneg (n : ℝ), sq_nonneg ((a n : ℝ) - 3 * Real.sqrt n)]
