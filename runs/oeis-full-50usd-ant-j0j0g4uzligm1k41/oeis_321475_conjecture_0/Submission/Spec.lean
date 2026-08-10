import FormalConjectures.Util.ProblemImports

open Nat List

/--
A321475: Zeroless factorials (version 2): $a(0) = 1$, and for any $n > 0$,
$a(n) = \operatorname{noz}(1 \cdot \operatorname{noz}(2 \cdot \ldots \cdot \operatorname{noz}((n-1) \cdot n)))$,
where $\operatorname{noz}(n) = A004719(n)$ omits the zeros from $n$.
-/
noncomputable def A321475 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    -- Helper function noz(k) to omit zeros from k (A004719)
    let noz (k : ℕ) : ℕ :=
      ofDigits 10 (filter (fun d : ℕ => d ≠ 0) (digits 10 k))

    -- The calculation is a tail-recursive loop modeling the nested operations.
    -- i is the descending multiplier, P is the accumulated product/result.
    let rec loop (i : ℕ) (P : ℕ) : ℕ :=
      if i = 0 then P
      -- Apply the next step: noz(i * P) and continue with the next multiplier i-1.
      else loop (i - 1) (noz (i * P))

    -- Initial call: multiplier starts at n - 1, initial value is n.
    loop (n - 1) n

/-
%C A321475 Is this sequence bounded?

Resolution: the sequence is **unbounded**, so the boundedness conjecture is false.

The disproof reduces the negation of the conjecture to the statement
`A321475_unbounded : ∀ M, ∃ n, M < A321475 n`.
-/
/-- The sequence `A321475` is unbounded: for every `M` there is an `n` with `M < A321475 n`. -/
theorem A321475_unbounded : ∀ M : ℕ, ∃ n : ℕ, M < A321475 n := by
  sorry

theorem oeis_321475_conjecture_0.disproof :
    ¬ (∃ M : ℕ, ∀ n : ℕ, A321475 n ≤ M) := by
  rintro ⟨M, hM⟩
  -- The sequence is unbounded, so there is some `n` with `M < A321475 n`,
  -- contradicting `hM n : A321475 n ≤ M`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M < A321475 n := A321475_unbounded M
  exact absurd (hM n) (Nat.not_le.mpr hn)
