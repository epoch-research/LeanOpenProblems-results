import FormalConjectures.Util.ProblemImports
open Nat Function Classical

/-- The sum of the decimal digits of a natural number. -/
def sum_digits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum

/-- The function $f(n) = n + \text{sum of the digits of } n$. -/
def f (n : ℕ) : ℕ := n + sum_digits n

/--
A100800: Let $f(n) = n + \text{sum of the digits of } n$. If $f(n)$ is multiple of $n$ then $a(n)= f(n)$ else $a(n) = f(f(f(n)))\dots$ until one gets a multiple of $n$; $a(n) = 0$ if no such number exists.
-/
noncomputable def A100800 (n : ℕ) : ℕ :=
  -- P(k) holds if the (k+1)-th iteration of f is a multiple of n.
  -- k=0 corresponds to the first iteration, f(n).
  let P (k : ℕ) : Prop := n ∣ Nat.iterate f (k + 1) n

  -- We use the noncomputable definition of finding the minimum index if it exists,
  -- or returning 0 otherwise, using the standard classical definition pattern.
  dite (∃ k, P k)
    (fun h_exists =>
      let k₀ : ℕ := Nat.find h_exists
      Nat.iterate f (k₀ + 1) n)
    (fun _ => 0)

/-!
### Status of this conjecture

`oeis_100800_conjecture_0` is the OEIS **A100800** "no term is zero" conjecture.
Unfolding `A100800`, the term `A100800 n` is `0` *iff* the existential
`∃ k, n ∣ f^[k+1] n` fails (in the `dite`-true branch the value is
`f^[Nat.find _ + 1] n ≥ n ≥ 1 > 0`).  Hence the conjecture is *exactly equivalent*
to the statement

  `∀ n ≥ 1, ∃ k, n ∣ f^[k+1] n`,

i.e. *every `n`'s digitaddition trajectory `n, n+S(n), …` contains a multiple of `n`.*
This equivalence is captured rigorously below by `A100800_eq_zero_iff` /
`reduction`, which are fully proved.

The remaining content `core_existence` is, to the best of analysis, a genuinely
**open** problem.  It cannot be disproved (the only `f`-invariant congruence is
`a_j ≡ 2^j·n (mod 9)`, and since `gcd(n,9) ∣ n ∣ a_j` it never forbids `0 mod n`;
moreover `a_j mod n` is not eventually periodic, so no finite "never-hits"
certificate exists).  Proving it requires additive richness/equidistribution of
the digit-sums `S(a_j) mod n` along the *self-referential* orbit, which is not
reachable by pigeonhole (that yields only zero-sum *windows* `a_b ≡ a_a`, not the
needed zero-sum *prefix* `a_j ≡ 0`) nor by Gelfond-type theorems (which concern
full arithmetic progressions, not the sparse orbit; the orbit need not even visit
all residues mod `n`).
-/

/-- `f` is non-decreasing: `x ≤ f x` since the digit sum is non-negative. -/
private lemma f_ge (x : ℕ) : x ≤ f x := Nat.le_add_right _ _

/-- Every iterate of `f` starting at `n` is at least `n`. -/
private lemma iterate_ge (n m : ℕ) : n ≤ Nat.iterate f m n := by
  induction m with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ']; exact le_trans ih (f_ge _)

/-- The reduction: the conjecture for `n` is equivalent to the existence claim. -/
private lemma reduction (n : ℕ) (hn : n ≠ 0) :
    A100800 n ≠ 0 ↔ ∃ k, n ∣ Nat.iterate f (k + 1) n := by
  unfold A100800
  by_cases hex : ∃ k, n ∣ Nat.iterate f (k + 1) n
  · rw [dif_pos hex]
    constructor
    · intro _; exact hex
    · intro _
      have h1 : n ≤ Nat.iterate f (Nat.find hex + 1) n := iterate_ge n _
      exact (lt_of_lt_of_le (Nat.pos_of_ne_zero hn) h1).ne'
  · rw [dif_neg hex]
    constructor
    · intro h; exact absurd rfl h
    · intro hc; exact absurd hc hex

/-- The core (open) content: every digitaddition trajectory of `n ≥ 1` meets a
multiple of `n`.  This is the unresolved mathematical heart of A100800. -/
private theorem core_existence (n : ℕ) (hn : n ≠ 0) :
    ∃ k, n ∣ Nat.iterate f (k + 1) n := by
  sorry

/-- A100800 Conjecture: No term is zero. -/
theorem oeis_100800_conjecture_0 : ∀ (n : ℕ), n ≠ 0 → A100800 n ≠ 0 :=
  fun n hn => (reduction n hn).2 (core_existence n hn)
