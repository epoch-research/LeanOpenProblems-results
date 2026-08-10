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

/-- Unfolding lemma for the well-founded recursion defining `a`. -/
theorem a_unfold (n : ℕ) :
    a n =
    if n = 0 then 1
    else
      Finset.sup (Finset.range n) fun i =>
          Finset.sup (Finset.range n) fun j =>
            if i ≤ j then
              if ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j - i + 1)).sum = n then
                ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0)
              else 0
            else 0 := by
  conv_lhs => rw [a, WellFounded.fix_eq]
  simp only []
  split <;> rfl

/--
The combinatorial heart of the conjecture: for every `n ≥ 1` there exist indices
`0 ≤ i ≤ j < n` such that the contiguous block `a(i), …, a(j)` sums to `n`.

Equivalently (writing `S_k = a(0)+⋯+a(k-1)` for the prefix sums) every positive integer
`n` is a difference `S_{j+1} − S_i` of two prefix sums with `j+1 ≤ n`.  This is precisely
the content of the OEIS A359634 "no zero appears" conjecture, which remains open.
-/
theorem core (n : ℕ) (hn : 0 < n) :
    ∃ i ∈ Finset.range n, ∃ j ∈ Finset.range n, i ≤ j ∧
      ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j - i + 1)).sum = n := by
  sorry

/--
Conjecture (OEIS A359634, C-line): A zero has not appeared in the sequence $a(n)$.
This is equivalent to $\forall n : \mathbb{N}, a(n) \neq 0$.
-/
theorem a_never_zero (n : ℕ) : a n ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [a_unfold]; norm_num
  · rw [a_unfold, if_neg (by omega)]
    obtain ⟨i, hi, j, hj, hij, hsum⟩ := core n h
    have hpos : 0 < ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) := by
      have hex : ∃ x ∈ ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j - i + 1)), x ≠ 0 := by
        by_contra hc
        push_neg at hc
        have : ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j - i + 1)).sum = 0 :=
          List.sum_eq_zero hc
        omega
      obtain ⟨x, hx, hx0⟩ := hex
      rw [Nat.lt_iff_add_one_le, zero_add, Nat.one_le_iff_ne_zero, Ne, List.countP_eq_zero]
      push_neg
      exact ⟨x, hx, by simpa using hx0⟩
    have hinner : 0 < (Finset.range n).sup fun j' =>
        if i ≤ j' then
          if ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j' - i + 1)).sum = n then
            ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j' - i + 1)).countP (· ≠ 0)
          else 0
        else 0 := by
      apply lt_of_lt_of_le hpos
      have := Finset.le_sup (f := fun j' =>
        if i ≤ j' then
          if ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j' - i + 1)).sum = n then
            ((List.ofFn (fun k : Fin n => a k.val)).drop i |>.take (j' - i + 1)).countP (· ≠ 0)
          else 0
        else 0) hj
      simp only [] at this
      rw [if_pos hij, if_pos hsum] at this
      exact this
    intro hcontra
    have hle := Finset.le_sup (f := fun i' =>
        (Finset.range n).sup fun j' =>
          if i' ≤ j' then
            if ((List.ofFn (fun k : Fin n => a k.val)).drop i' |>.take (j' - i' + 1)).sum = n then
              ((List.ofFn (fun k : Fin n => a k.val)).drop i' |>.take (j' - i' + 1)).countP (· ≠ 0)
            else 0
          else 0) hi
    simp only [] at hle
    rw [hcontra] at hle
    omega
