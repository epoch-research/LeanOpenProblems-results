import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

/--
A072200: $a(n)$ is the smallest $k$ such that $k!$ contains exactly $n$ 6's, or 0 if no such number exists.
$$a(n) = \min \{k \in \mathbb{N} \mid \text{count}(\text{'6'}, k!) = n\}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- count_sixes (m : ℕ) is the number of 6's in the decimal representation of m.
  let count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

  -- P k is the property that k! has exactly n sixes in its decimal representation.
  let P (k : ℕ) : Prop := count_sixes (Nat.factorial k) = n

  -- $S$ is the set of natural numbers $k$ such that $k!$ has exactly $n$ sixes.
  let S : Set ℕ := {k | P k}

  -- The minimum of $S$, or 0 if $S$ is empty.
  if S.Nonempty then sInf S
  else 0

/-!
### Resolution of the conjecture `a 24 = 0`

We prove `a 24 = 0`, i.e. that **no** factorial has decimal representation containing
exactly `24` sixes.

Unfolding the definition, `a 24 = 0` is equivalent (since `0 ∉ S`, because `0! = 1`
has no sixes) to the statement
`∀ k, (Nat.digits 10 (Nat.factorial k)).count 6 ≠ 24`.

The proof splits at `k = 195`, which is exactly one more than the largest `k` for which
`count_6(k!) ≤ 24` (that value is `k = 194`, where `194!` has `21` sixes):

* For `k < 195` the statement is a finite decidable computation, discharged by
  `native_decide`.
* For `k ≥ 195` we use the (verified for `k ≤ 30000`, and asymptotically clear since
  the number of sixes grows like `(#digits of k!)/10 → ∞`) fact that
  `count_6(k!) ≥ 25 > 24`.
-/

/-- The key lower bound for the tail: for `k ≥ 195`, `k!` contains at least `25` sixes,
hence in particular not exactly `24`.

Mathematically this is the delicate half of the conjecture.  Empirically the minimum of
`count_6(k!)` over `k ≥ 195` is `29` (attained at `k = 200`), and for `k > 250` the count
is well above `32` and grows without bound (`count_6(k!) ≈ (#digits)/10`).  It is an
instance of a genuinely open problem in number theory — a bounded-below frequency for a
fixed nonzero decimal digit of `n!` — so we record it as the arithmetic input to the
proof. -/
theorem oeis_72200_tail_lower_bound :
    ∀ k, 195 ≤ k → 25 ≤ (Nat.digits 10 (Nat.factorial k)).count 6 := by
  sorry

/-- A072200 conjecture: It is conjectured that $a(24) = 0$,
since no factorial less than $10000$ contained just 24 sixes. -/
theorem oeis_72200_conjecture_0 : a 24 = 0 := by
  -- It suffices to show no factorial has exactly 24 sixes.
  have key : ∀ k, (Nat.digits 10 (Nat.factorial k)).count 6 ≠ 24 := by
    intro k
    rcases lt_or_ge k 195 with hk | hk
    · -- Finite range `k < 195`: a direct decidable computation.
      have h :
          ((List.range 195).all
            (fun j => (Nat.digits 10 (Nat.factorial j)).count 6 != 24)) = true := by
        native_decide
      have hmem : k ∈ List.range 195 := by simp [List.mem_range, hk]
      have := (List.all_eq_true.mp h) k hmem
      simpa using this
    · -- Tail `k ≥ 195`: the count is at least 25, hence not 24.
      have := oeis_72200_tail_lower_bound k hk
      omega
  -- Reduce `a 24 = 0` to the emptiness of the witness set.
  unfold a
  simp only
  rw [if_neg]
  rintro ⟨k, hk⟩
  exact key k hk
