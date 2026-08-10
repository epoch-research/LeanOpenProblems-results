import FormalConjectures.Util.ProblemImports

open List Finset

/--
A359634: $a(0)=1$ and thereafter $a(n)$ is the length of the longest contiguous group of terms in the sequence thus far that add up to $n$; if no such group exists, set $a(n)=0$.
If a zero appears, it is not counted as a term in a contiguous grouping.
-/
noncomputable def a : ℕ → ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n IH =>
    if h0 : n = 0 then 1
    else
      let target : ℕ := n

      -- The previous terms a(k) for k < n are computed using the induction hypothesis IH.
      let a_prev (k : ℕ) (hk : k < n) : ℕ := IH k hk

      -- The list of previous terms [a(0), a(1), ..., a(n-1)]. Fin n ensures k.val < n.
      let prefix_list : List ℕ := List.ofFn (fun k : Fin n => a_prev k.val k.is_lt)

      -- Find the maximum length of a contiguous sublist that sums to target.
      -- We iterate over all possible start indices i and end indices j such that 0 ≤ i ≤ j < n.
      let max_contiguous_length : ℕ :=
        Finset.sup (Finset.range n) fun i => -- start index i
          Finset.sup (Finset.range n) fun j => -- end index j
            if h : i ≤ j then
              let sublist_len := j - i + 1
              let sublist := prefix_list.drop i |>.take sublist_len
              if sublist.sum = target then
                -- The length is the number of non-zero terms in the sublist
                sublist.countP (· ≠ 0)
              else 0
            else 0

      max_contiguous_length
  )

/--
Conjecture (OEIS A359634, C-line): A zero has not appeared in the sequence $a(n)$.
This is equivalent to $\forall n : \mathbb{N}, a(n) \neq 0$.
-/
theorem a_never_zero (n : ℕ) : a n ≠ 0 := by
  sorry
