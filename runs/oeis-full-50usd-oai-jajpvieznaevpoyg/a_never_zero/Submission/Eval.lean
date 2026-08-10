import FormalConjectures.Util.ProblemImports

open List Finset

noncomputable def a : ℕ → ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n IH =>
    if h0 : n = 0 then 1
    else
      let target : ℕ := n
      let a_prev (k : ℕ) (hk : k < n) : ℕ := IH k hk
      let prefix_list : List ℕ := List.ofFn (fun k : Fin n => a_prev k.val k.is_lt)
      let max_contiguous_length : ℕ :=
        Finset.sup (Finset.range n) fun i =>
          Finset.sup (Finset.range n) fun j =>
            if h : i ≤ j then
              let sublist_len := j - i + 1
              let sublist := prefix_list.drop i |>.take sublist_len
              if sublist.sum = target then
                sublist.countP (· ≠ 0)
              else 0
            else 0
      max_contiguous_length
  )

#reduce a 0
#reduce a 1
#reduce a 2
#reduce a 3
#reduce a 4
#reduce a 5
#reduce a 6
#reduce a 7
#reduce a 8
#reduce a 9
#reduce a 10
