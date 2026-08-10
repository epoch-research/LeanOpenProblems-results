import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000


open List Finset

/--
A359634: $a(0)=1$ and thereafter $a(n)$ is the length of the longest contiguous group of terms in the sequence thus far that add up to $n$; if no such group exists, set $a(n)=0$.
If a zero appears, it is not counted as a term in a contiguous grouping.
-/
noncomputable def a : ℕ → ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n IH =>
    if n = 0 then 1
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
            if i ≤ j then
              let sublist_len := j - i + 1
              let sublist := prefix_list.drop i |>.take sublist_len
              if sublist.sum = target then
                -- The length is the number of non-zero terms in the sublist
                sublist.countP (· ≠ 0)
              else 0
            else 0

      max_contiguous_length
  )

theorem a_eq (m : ℕ) : a m = if m = 0 then 1 else
      let target : ℕ := m
      let prefix_list : List ℕ := List.ofFn (fun k : Fin m => a k.val)
      let max_contiguous_length : ℕ :=
        Finset.sup (Finset.range m) fun i =>
          Finset.sup (Finset.range m) fun j =>
            if i ≤ j then
              let sublist_len := j - i + 1
              let sublist := prefix_list.drop i |>.take sublist_len
              if sublist.sum = target then
                sublist.countP (· ≠ 0)
              else 0
            else 0
      max_contiguous_length := by
  unfold a
  rw [WellFounded.fix_eq]

theorem a_zero : a 0 = 1 := by
  rw [a_eq 0]
  simp

theorem a_one : a 1 = 1 := by
  rw [a_eq 1]
  simp [a_zero]


theorem a_two : a 2 = 2 := by
  rw [a_eq 2]
  simp [a_zero, a_one]
  decide

theorem a_three : a 3 = 2 := by
  rw [a_eq 3]
  simp [a_zero, a_one, a_two]
  decide

theorem a_four : a 4 = 3 := by
  rw [a_eq 4]
  simp [a_zero, a_one, a_two, a_three]
  decide

theorem a_five : a 5 = 3 := by
  rw [a_eq 5]
  simp [a_zero, a_one, a_two, a_three, a_four]
  decide

theorem a_six : a 6 = 4 := by
  rw [a_eq 6]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five]
  decide

theorem a_seven : a 7 = 3 := by
  rw [a_eq 7]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six]
  decide

theorem a_eight : a 8 = 4 := by
  rw [a_eq 8]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven]
  decide

theorem a_nine : a 9 = 5 := by
  rw [a_eq 9]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight]
  decide

theorem a_ten : a 10 = 4 := by
  rw [a_eq 10]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine]
  decide

theorem a_eleven : a 11 = 5 := by
  rw [a_eq 11]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten]
  decide

theorem a_twelve : a 12 = 6 := by
  rw [a_eq 12]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven]
  decide

theorem a_thirteen : a 13 = 4 := by
  rw [a_eq 13]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve]
  decide

theorem a_fourteen : a 14 = 5 := by
  rw [a_eq 14]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen]
  decide

theorem a_fifteen : a 15 = 6 := by
  rw [a_eq 15]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen]
  decide

theorem a_sixteen : a 16 = 7 := by
  rw [a_eq 16]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen]
  decide

theorem a_seventeen : a 17 = 6 := by
  rw [a_eq 17]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen]
  decide

theorem a_eighteen : a 18 = 7 := by
  rw [a_eq 18]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen]
  decide

theorem a_nineteen : a 19 = 8 := by
  rw [a_eq 19]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen]
  decide

theorem a_twenty : a 20 = 5 := by
  rw [a_eq 20]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen]
  decide

theorem a_twenty_one : a 21 = 7 := by
  rw [a_eq 21]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty]
  decide

theorem a_twenty_two : a 22 = 8 := by
  rw [a_eq 22]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one]
  decide

theorem a_twenty_three : a 23 = 9 := by
  rw [a_eq 23]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two]
  decide

theorem a_twenty_four : a 24 = 7 := by
  rw [a_eq 24]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three]
  decide

theorem a_twenty_five : a 25 = 6 := by
  rw [a_eq 25]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four]
  decide

theorem a_twenty_six : a 26 = 8 := by
  rw [a_eq 26]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five]
  decide

theorem a_twenty_seven : a 27 = 9 := by
  rw [a_eq 27]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six]
  decide

theorem a_twenty_eight : a 28 = 10 := by
  rw [a_eq 28]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven]
  decide

theorem a_twenty_nine : a 29 = 6 := by
  rw [a_eq 29]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight]
  decide

theorem a_thirty : a 30 = 9 := by
  rw [a_eq 30]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine]
  decide
theorem a_thirty_one : a 31 = 10 := by
  rw [a_eq 31]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty]
  decide

theorem a_thirty_two : a 32 = 11 := by
  rw [a_eq 32]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one]
  decide

theorem a_thirty_three : a 33 = 9 := by
  rw [a_eq 33]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two]
  decide

theorem a_thirty_four : a 34 = 8 := by
  rw [a_eq 34]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three]
  decide

theorem a_thirty_five : a 35 = 10 := by
  rw [a_eq 35]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four]
  decide

theorem a_thirty_six : a 36 = 11 := by
  rw [a_eq 36]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five]
  decide

theorem a_thirty_seven : a 37 = 12 := by
  rw [a_eq 37]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six]
  decide

theorem a_thirty_eight : a 38 = 9 := by
  rw [a_eq 38]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six, a_thirty_seven]
  decide

theorem a_thirty_nine : a 39 = 10 := by
  rw [a_eq 39]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six, a_thirty_seven, a_thirty_eight]
  decide

theorem a_forty : a 40 = 9 := by
  rw [a_eq 40]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six, a_thirty_seven, a_thirty_eight, a_thirty_nine]
  decide


theorem a_forty_one : a 41 = 11 := by
  rw [a_eq 41]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six, a_thirty_seven, a_thirty_eight, a_thirty_nine, a_forty]
  decide

theorem a_forty_two : a 42 = 12 := by
  rw [a_eq 42]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six, a_thirty_seven, a_thirty_eight, a_thirty_nine, a_forty, a_forty_one]
  decide

theorem a_forty_three : a 43 = 13 := by
  rw [a_eq 43]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six, a_thirty_seven, a_thirty_eight, a_thirty_nine, a_forty, a_forty_one, a_forty_two]
  decide

theorem a_forty_four : a 44 = 7 := by
  rw [a_eq 44]
  simp [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten, a_eleven, a_twelve, a_thirteen, a_fourteen, a_fifteen, a_sixteen, a_seventeen, a_eighteen, a_nineteen, a_twenty, a_twenty_one, a_twenty_two, a_twenty_three, a_twenty_four, a_twenty_five, a_twenty_six, a_twenty_seven, a_twenty_eight, a_twenty_nine, a_thirty, a_thirty_one, a_thirty_two, a_thirty_three, a_thirty_four, a_thirty_five, a_thirty_six, a_thirty_seven, a_thirty_eight, a_thirty_nine, a_forty, a_forty_one, a_forty_two, a_forty_three]
  decide


































































/--
Conjecture (OEIS A359634, C-line): A zero has not appeared in the sequence $a(n)$.
This is equivalent to $\forall n : \mathbb{N}, a(n) \neq 0$.
-/

theorem a_never_zero (n : ℕ) : a n ≠ 0 := by
  induction' n using Nat.strong_induction_on with n IH
  by_cases hn45 : n < 45
  · interval_cases n
    · rw [a_zero]; omega
    · rw [a_one]; omega
    · rw [a_two]; omega
    · rw [a_three]; omega
    · rw [a_four]; omega
    · rw [a_five]; omega
    · rw [a_six]; omega
    · rw [a_seven]; omega
    · rw [a_eight]; omega
    · rw [a_nine]; omega
    · rw [a_ten]; omega
    · rw [a_eleven]; omega
    · rw [a_twelve]; omega
    · rw [a_thirteen]; omega
    · rw [a_fourteen]; omega
    · rw [a_fifteen]; omega
    · rw [a_sixteen]; omega
    · rw [a_seventeen]; omega
    · rw [a_eighteen]; omega
    · rw [a_nineteen]; omega
    · rw [a_twenty]; omega
    · rw [a_twenty_one]; omega
    · rw [a_twenty_two]; omega
    · rw [a_twenty_three]; omega
    · rw [a_twenty_four]; omega
    · rw [a_twenty_five]; omega
    · rw [a_twenty_six]; omega
    · rw [a_twenty_seven]; omega
    · rw [a_twenty_eight]; omega
    · rw [a_twenty_nine]; omega
    · rw [a_thirty]; omega
    · rw [a_thirty_one]; omega
    · rw [a_thirty_two]; omega
    · rw [a_thirty_three]; omega
    · rw [a_thirty_four]; omega
    · rw [a_thirty_five]; omega
    · rw [a_thirty_six]; omega
    · rw [a_thirty_seven]; omega
    · rw [a_thirty_eight]; omega
    · rw [a_thirty_nine]; omega
    · rw [a_forty]; omega
    · rw [a_forty_one]; omega
    · rw [a_forty_two]; omega
    · rw [a_forty_three]; omega
    · rw [a_forty_four]; omega
  · have h0 : ¬n = 0 := by omega
    rw [a]
    rw [WellFounded.fix_eq]
    rw [if_neg h0]
    by_contra! h_zero
    simp at h_zero
    have h_pos : ∀ x ∈ List.ofFn (fun k : Fin n => a k.val), x > 0 := by
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨k, rfl⟩ := hx
      have hk : k.val < n := k.is_lt
      have h_nz := IH k.val hk
      omega
    have h_sum : ∀ x y, x ≤ y → x < n → y < n → ((List.ofFn (fun k : Fin n => a k.val)).drop x |>.take (y - x + 1)).sum ≠ n := by
      intro x y hxy hx hy h_eq
      -- Unfold and simplify h_eq so it matches h_zero exactly
      unfold a at h_eq
      simp at h_eq
      have h_zero_xy := h_zero x hx y hy hxy h_eq
      set sublist := ((List.ofFn (fun k : Fin n => a k.val)).drop x |>.take (y - x + 1)) with h_sub'
      have h_sub := h_sub'
      unfold a at h_sub
      simp at h_sub
      have h_len : sublist.length = y - x + 1 := by
        rw [h_sub']
        rw [List.length_take]
        rw [List.length_drop]
        rw [List.length_ofFn]
        omega
      have h_len_pos : sublist.length > 0 := by
        rw [h_len]
        omega
      obtain ⟨z, hz⟩ : ∃ z, z ∈ sublist := by
        cases' h_sub_eq : sublist with z ts
        · have h_zero_len : sublist.length = 0 := by rw [h_sub_eq]; rfl
          omega
        · exact ⟨z, by simp⟩
      have hz_in : z ∈ List.ofFn (fun k : Fin n => a k.val) := by
        apply List.mem_of_mem_drop
        have hz' : z ∈ ((List.ofFn (fun k : Fin n => a k.val)).drop x |>.take (y - x + 1)) := by
          rwa [← h_sub']
        exact List.mem_of_mem_take hz'
      rw [h_sub] at hz
      have hz_zero := h_zero_xy z hz
      have hz_gt_0 := h_pos z hz_in
      omega

    let S (m : ℕ) : ℕ := ((List.ofFn (fun k : Fin n => a k.val)).take m).sum
    have S_zero : S 0 = 0 := by rfl
    have S_step (m : ℕ) (hm : m < n) : S (m + 1) = S m + a m := by
      dsimp [S]
      have hm_len : m < (List.ofFn (fun k : Fin n => a k.val)).length := by
        rw [List.length_ofFn]
        exact hm
      rw [List.sum_take_succ _ m hm_len]
      simp
    have S_sum (x y : ℕ) (hxy : x ≤ y) (hy : y < n) : S (y + 1) = S x + ((List.ofFn (fun k : Fin n => a k.val)).drop x |>.take (y - x + 1)).sum := by
      dsimp [S]
      have h_eq_add : y + 1 = x + (y - x + 1) := by omega
      nth_rw 1 [h_eq_add]
      rw [List.take_add]
      rw [List.sum_append]
    have h_S_diff : ∀ x y, x ≤ y → x < n → y < n → S (y + 1) - S x ≠ n := by
      intro x y hxy hx hy h_eq
      have h_sum_xy := h_sum x y hxy hx hy
      have h_sum_val := S_sum x y hxy hy
      omega
    have h_no_pair : ∀ i j, i < j → j ≤ n → S j - S i ≠ n := by
      intro i j hij hj
      have hxy : i ≤ j - 1 := by omega
      have hy : j - 1 < n := by omega
      have hx : i < n := by omega
      have h_diff := h_S_diff i (j - 1) hxy hx hy
      have h_eq_j : j - 1 + 1 = j := by omega
      rw [h_eq_j] at h_diff
      exact h_diff
    have S_ge (m : ℕ) (hm : m ≤ n) : S m ≥ m := by
      induction m with
      | zero =>
        rw [S_zero]
      | succ m ih =>
        have hm_lt : m < n := by omega
        have h_step := S_step m hm_lt
        have h_am_nz := IH m hm_lt
        have h_am_ge : a m ≥ 1 := by omega
        have h_ih := ih (by omega)
        omega

    have h_exists_S_ge : ∃ m, S m ≥ n := ⟨n, S_ge n (by omega)⟩
    let k := Nat.find h_exists_S_ge
    have hk_spec : S k ≥ n := Nat.find_spec h_exists_S_ge
    have hk_least : ∀ m < k, S m < n := by
      intro m hm
      have h_not := Nat.find_min h_exists_S_ge hm
      omega
    have hk_gt_zero : k > 0 := by
      by_contra! h_k
      have h_k_zero : k = 0 := by omega
      rw [h_k_zero] at hk_spec
      rw [S_zero] at hk_spec
      omega
    have hk_le_n : k ≤ n := by
      have h_n := Nat.find_min' h_exists_S_ge (S_ge n (by omega))
      exact h_n

    have h_sk_eq_n : S k ≠ n := by
      intro h_eq
      have h_diff : S k - S 0 = n := by rw [S_zero]; omega
      have h_not := h_no_pair 0 k hk_gt_zero hk_le_n
      omega

    have h_sk_gt_n : S k > n := by omega
    set d := S k - n with hd_def
    have hd_gt_zero : d > 0 := by omega
    have h_step_k := S_step (k - 1) (by omega)
    have h_least_k := hk_least (k - 1) (by omega)
    have h_eq_k : k - 1 + 1 = k := Nat.sub_add_cancel hk_gt_zero
    rw [h_eq_k] at h_step_k
    have hd_lt_ak : d < a (k - 1) := by omega

    have hk1_nz : k - 1 ≠ 0 := by
      intro hk1
      have hk_eq_1 : k = 1 := by omega
      have h_s1 : S 1 = 1 := by
        rw [S_step 0 (by omega)]
        rw [S_zero]
        rw [a_eq 0]
        simp
      have h_sk_eq : S k = S 1 := by rw [hk_eq_1]
      rw [h_sk_eq, h_s1] at h_sk_gt_n
      omega

    have h_ak_le : a (k - 1) ≤ k - 1 := by
      rw [a_eq (k - 1)]
      rw [if_neg hk1_nz]
      dsimp
      apply Finset.sup_le
      intro i hi
      apply Finset.sup_le
      intro j hj
      split_ifs with hij h_sum
      · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k - 1) => a k_1.val)).drop i |>.take (j - i + 1)))
        have h_len : ((List.ofFn (fun k_1 : Fin (k - 1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
        have hj_lt : j < k - 1 := by
          rw [Finset.mem_range] at hj
          exact hj
        omega
      · omega
      · omega

    have hd_lt_n : d < n := by omega

    -- Apply IH to d to get a contiguous segment summing to d
    have hd_nz := IH d hd_lt_n
    have hd_ge : a d ≥ 1 := by omega
    rw [a_eq d] at hd_ge
    have hd_nz_eq : d ≠ 0 := by omega
    rw [if_neg hd_nz_eq] at hd_ge
    dsimp at hd_ge

    -- Extract indices i_d, j_d such that the segment sums to d
    have h_sup_pos : Finset.sup (Finset.range d) (fun i => Finset.sup (Finset.range d) (fun j => if i ≤ j then if ((List.ofFn (fun k : Fin d => a k.val)).drop i |>.take (j - i + 1)).sum = d then ((List.ofFn (fun k : Fin d => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0)) ≥ 1 := by omega

    have h_exists_pair : ∃ i ∈ Finset.range d, ∃ j ∈ Finset.range d, i ≤ j ∧ ((List.ofFn (fun k : Fin d => a k.val)).drop i |>.take (j - i + 1)).sum = d := by
      by_contra! h_none
      have h_sup_zero : Finset.sup (Finset.range d) (fun i => Finset.sup (Finset.range d) (fun j => if i ≤ j then if ((List.ofFn (fun k : Fin d => a k.val)).drop i |>.take (j - i + 1)).sum = d then ((List.ofFn (fun k : Fin d => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0)) = 0 := by
        rw [Finset.sup_eq_zero]
        intro i hi
        rw [Finset.sup_eq_zero]
        intro j hj
        split_ifs with hij h_sum
        · exfalso
          exact h_none i hi j hj hij h_sum
        · rfl
        · rfl
      omega

    obtain ⟨i_d, hi_d, j_d, hj_d, hij_d, hd_sum_eq⟩ := h_exists_pair
    rw [Finset.mem_range] at hi_d hj_d

    -- Let's define the prefix sums S_d
    let S_d (m : ℕ) : ℕ := ((List.ofFn (fun k : Fin d => a k.val)).take m).sum
    have S_d_sum (x y : ℕ) (hxy : x ≤ y) (hy : y < d) : S_d (y + 1) = S_d x + ((List.ofFn (fun k : Fin d => a k.val)).drop x |>.take (y - x + 1)).sum := by
      dsimp [S_d]
      have h_eq_add : y + 1 = x + (y - x + 1) := by omega
      nth_rw 1 [h_eq_add]
      rw [List.take_add]
      rw [List.sum_append]

    have h_sub_eq_S_d : S_d (j_d + 1) - S_d i_d = d := by
      have h_sum_val := S_d_sum i_d j_d hij_d hj_d
      omega

    -- Since d < n, the prefix of length d is a prefix of length n
    have S_d_eq_S (m : ℕ) (hm : m ≤ d) : S_d m = S m := by
      dsimp [S_d, S]
      congr 1
      apply List.ext_get
      · rw [List.length_take, List.length_take, List.length_ofFn, List.length_ofFn]
        omega
      · intro i h1 h2
        simp

    have h_S_j_d : S_d (j_d + 1) = S (j_d + 1) := S_d_eq_S (j_d + 1) (by omega)
    have h_S_i_d : S_d i_d = S i_d := S_d_eq_S i_d (by omega)

    have h_S_diff_d : S (j_d + 1) - S i_d = d := by
      omega

    -- S (j_d + 1) - S i_d = d = S k - n
    -- So S k - S (j_d + 1) + S i_d = n
    -- Since S i_d ≤ S (j_d + 1)
    -- If i_d = 0, then S i_d = 0, so S k - S (j_d + 1) = n
    have h_S_mono : ∀ x y, y ≤ x → x ≤ n → S x + y ≥ S y + x := by
      intro x
      induction x with
      | zero =>
        intro y hy hx
        have : y = 0 := by omega
        subst this
        omega
      | succ m ih =>
        intro y hy hx
        by_cases hy_eq : y = m + 1
        · subst hy_eq
          omega
        · have hy_le : y ≤ m := by omega
          have h_ih := ih y hy_le (by omega)
          have h_step := S_step m (by omega)
          have h_am_nz := IH m (by omega)
          have h_am_ge : a m ≥ 1 := by omega
          omega

    by_cases hi_d_zero : i_d = 0
    · subst hi_d_zero
      rw [S_zero] at h_S_diff_d
      simp at h_S_diff_d
      -- S (j_d + 1) = d
      have h_eq_n : S k - S (j_d + 1) = n := by omega
      have h_no := h_no_pair (j_d + 1) k (by omega) hk_le_n
      exact h_no h_eq_n
    · have h_sum_ge : S k ≥ S (j_d + 1) + k := by
        have h_mono_k1 := h_S_mono (k-1) (j_d + 1) (by omega) (by omega)
        omega
      have h_sk_ge_j : S k ≥ S (j_d + 1) := by omega
      let m := S k - S (j_d + 1)
      have h_m_id : m + S i_d = n := by omega
      have h_m_lt_n : m < n := by
        have h_si1 : S 1 ≥ 1 := S_ge 1 (by omega)
        have h_si_ge : S i_d ≥ S 1 := by
          have h_mono := h_S_mono i_d 1 (by omega) (by omega)
          omega
        omega
      have h_m_ge_k : m ≥ k := by omega

      have h_le_all : ∀ y < n, y ≠ 0 → a y ≤ y := by
        intro y hy hy_nz
        rw [a_eq y]
        rw [if_neg hy_nz]
        dsimp
        apply Finset.sup_le
        intro i hi
        apply Finset.sup_le
        intro j hj
        split_ifs with hij h_sum
        · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin y => a k_1.val)).drop i |>.take (j - i + 1)))
          have h_len : ((List.ofFn (fun k_1 : Fin y => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
          have hj_lt : j < y := by
            rw [Finset.mem_range] at hj
            exact hj
          omega
        · omega
        · omega

      have h_ar_ne_one : ∀ r < n, r ≥ 2 → a r ≠ 1 := by
        intro r hr hr2 h_one
        have hr_nz_eq : r ≠ 0 := by omega
        have h_ge : a r ≥ 1 := by omega
        have h_exists : ∃ i ∈ Finset.range r, ∃ j ∈ Finset.range r, i ≤ j ∧ ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).sum = r := by
          by_contra! h_none
          rw [a_eq r] at h_ge
          rw [if_neg hr_nz_eq] at h_ge
          dsimp at h_ge
          change (Finset.sup (Finset.range r) (fun i => Finset.sup (Finset.range r) (fun j => if i ≤ j then if ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).sum = r then ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0))) ≥ 1 at h_ge
          have h_sup_zero : (Finset.sup (Finset.range r) (fun i => Finset.sup (Finset.range r) (fun j => if i ≤ j then if ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).sum = r then ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0))) = 0 := by
            rw [Finset.sup_eq_zero]
            intro i hi
            rw [Finset.sup_eq_zero]
            intro j hj
            split_ifs with hij h_sum
            · exfalso
              exact h_none i hi j hj hij h_sum
            · rfl
            · rfl
          omega
        obtain ⟨i, hi, j, hj, hij, h_sum_r⟩ := h_exists
        have hi_mem : i ∈ Finset.range r := hi
        have hj_mem : j ∈ Finset.range r := hj
        rw [Finset.mem_range] at hi hj
        have h_le_one : ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) ≤ 1 := by
          rw [a_eq r] at h_one
          rw [if_neg hr_nz_eq] at h_one
          dsimp at h_one
          change (Finset.sup (Finset.range r) (fun i => Finset.sup (Finset.range r) (fun j => if i ≤ j then if ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).sum = r then ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0))) = 1 at h_one
          have h_le := Finset.le_sup (f := fun i => Finset.sup (Finset.range r) (fun j => if i ≤ j then if ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).sum = r then ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0)) hi_mem
          have h_le' := Finset.le_sup (f := fun j => if i ≤ j then if ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).sum = r then ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0) hj_mem
          rw [h_one] at h_le
          dsimp only at h_le'
          split_ifs at h_le'
          · exact le_trans h_le' h_le
        have h_all_nz : ∀ x ∈ ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)), x ≠ 0 := by
          intro x hx
          have h_in_r : x ∈ List.ofFn (fun k : Fin r => a k.val) := by
            apply List.mem_of_mem_drop
            exact List.mem_of_mem_take hx
          rw [List.mem_ofFn] at h_in_r
          obtain ⟨k_r, rfl⟩ := h_in_r
          have h_in_n : a k_r.val ∈ List.ofFn (fun k : Fin n => a k.val) := by
            rw [List.mem_ofFn]
            exact ⟨⟨k_r.val, by omega⟩, rfl⟩
          have h_gt := h_pos (a k_r.val) h_in_n
          omega
        have h_sub_len : ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).length = j - i + 1 := by
          rw [List.length_take]
          rw [List.length_drop]
          rw [List.length_ofFn]
          omega
        have h_all_nz_dec : ∀ x ∈ ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)), (fun y => decide (y ≠ 0)) x = true := by
          intro x hx
          simp [h_all_nz x hx]
        have h_count_len : ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) = j - i + 1 := by
          have h_count_len_eq : ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) = ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)).length := List.countP_eq_length.mpr h_all_nz_dec
          rw [h_count_len_eq, h_sub_len]
        have hij_eq : j = i := by omega
        have h_drop_take_one : ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take 1) = [a i] := by
          apply List.ext_get
          · rw [List.length_take, List.length_drop, List.length_ofFn]
            have h_len_bound : 1 ≤ r - i := by omega
            rw [Nat.min_eq_left h_len_bound]
            rfl
          · intro m h1 h2
            simp at h1
            have hm : m = 0 := by omega
            subst hm
            simp
        have h_drop_take_one' : ((List.ofFn (fun k : Fin r => a k.val)).drop i |>.take (j - i + 1)) = [a i] := by
          rw [hij_eq]
          have h_eq : i - i + 1 = 1 := by omega
          rw [h_eq]
          exact h_drop_take_one
        rw [h_drop_take_one'] at h_sum_r
        simp at h_sum_r
        -- Now we have h_sum_r : a i = r.
        -- We want to prove contradiction since a i ≤ i < r.
        by_cases hi_zero : i = 0
        · subst hi_zero
          rw [a_zero] at h_sum_r
          omega
        · have h_le := h_le_all i (by omega) hi_zero
          omega

      have hd3 : d ≥ 3 := by
        by_contra! hd_lt_3
        revert hi_d hj_d hij_d hd_sum_eq
        interval_cases d
        · intro hi_d hj_d hij_d hd_sum_eq
          omega
        · intro hi_d hj_d hij_d hd_sum_eq
          have hi1 : i_d = 1 := by omega
          have hj1 : j_d = 1 := by omega
          rw [hi1, hj1] at hd_sum_eq
          have h_sum_val : ((List.ofFn (fun k : Fin 2 => a k.val)).drop 1 |>.take 1).sum = a 1 := rfl
          rw [h_sum_val, a_one] at hd_sum_eq
          omega
      have h_len_ge_2 : j_d - i_d + 1 ≥ 2 := by
        by_contra! h_len_lt_2
        have h_len_eq : j_d - i_d + 1 = 1 := by omega
        have h_sublist : ((List.ofFn (fun k : Fin d => a k.val)).drop i_d |>.take (j_d - i_d + 1)) = [a i_d] := by
          rw [h_len_eq]
          rw [take_one_drop_eq_of_lt_length]
          · simp
          · rw [List.length_ofFn]
            exact hi_d
        rw [h_sublist] at hd_sum_eq
        simp at hd_sum_eq
        have h_le := h_le_all i_d (by omega) hi_d_zero
        omega
      have hm_nz_eq : m ≠ 0 := by omega
      have h_sublist_eq : ((List.ofFn (fun k : Fin m => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)) = ((List.ofFn (fun k : Fin n => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)) := by
        apply List.ext_get
        · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
          omega
        · intro idx h1 h2
          simp
      have h_sum_m : ((List.ofFn (fun k : Fin m => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)).sum = m := by
        rw [h_sublist_eq]
        have h_sum_val := S_sum (j_d + 1) (k - 1) (by omega) (by omega)
        have h_eq_k : k - 1 + 1 = k := by omega
        rw [h_eq_k] at h_sum_val
        omega
      have h_count_m : ((List.ofFn (fun k : Fin m => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)).countP (· ≠ 0) = k - 1 - j_d := by
        rw [h_sublist_eq]
        have h_all_nz : ∀ x ∈ ((List.ofFn (fun k : Fin n => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)), x ≠ 0 := by
          intro x hx
          have hx_in : x ∈ List.ofFn (fun k : Fin n => a k.val) := by
            apply List.mem_of_mem_drop
            exact List.mem_of_mem_take hx
          have h_nz := h_pos x hx_in
          omega
        have h_count_eq : ((List.ofFn (fun k : Fin n => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)).countP (· ≠ 0) = ((List.ofFn (fun k : Fin n => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)).length := by
          apply List.countP_eq_length.mpr
          intro x hx
          simp [h_all_nz x hx]
        rw [h_count_eq]
        rw [List.length_take, List.length_drop, List.length_ofFn]
        omega
      have hm_ge : a m ≥ k - 1 - j_d := by
        rw [a_eq m]
        rw [if_neg hm_nz_eq]
        dsimp
        have h_jd1_mem : j_d + 1 ∈ Finset.range m := by
          rw [Finset.mem_range]
          omega
        have h_km1_mem : k - 1 ∈ Finset.range m := by
          rw [Finset.mem_range]
          omega
        have h_le_sup1 := Finset.le_sup (f := fun i => Finset.sup (Finset.range m) fun j => if i ≤ j then if ((List.ofFn (fun k : Fin m => a k.val)).drop i |>.take (j - i + 1)).sum = m then ((List.ofFn (fun k : Fin m => a k.val)).drop i |>.take (j - i + 1)).countP (· ≠ 0) else 0 else 0) h_jd1_mem
        have h_le_sup2 := Finset.le_sup (f := fun j => if j_d + 1 ≤ j then if ((List.ofFn (fun k : Fin m => a k.val)).drop (j_d + 1) |>.take (j - (j_d + 1) + 1)).sum = m then ((List.ofFn (fun k : Fin m => a k.val)).drop (j_d + 1) |>.take (j - (j_d + 1) + 1)).countP (· ≠ 0) else 0 else 0) h_km1_mem
        dsimp only at h_le_sup2
        have h_le_sub : j_d + 1 ≤ k - 1 := by omega
        split_ifs at h_le_sup2
        have h_val : ((List.ofFn (fun k : Fin m => a k.val)).drop (j_d + 1) |>.take (k - 1 - (j_d + 1) + 1)).countP (· ≠ 0) = k - 1 - j_d := h_count_m
        rw [h_val] at h_le_sup2
        have h_trans := le_trans h_le_sup2 h_le_sup1
        exact h_trans
      have h_sum_ge_2 : ∀ m ≤ n, m ≥ 1 → S m ≥ 2 * m - 2 := by
        intro m hm hm1
        induction m with
        | zero => omega
        | succ m ih =>
          by_cases hm0 : m = 0
          · subst hm0
            have h1 : S 1 = S 0 + a 0 := S_step 0 (by omega)
            rw [S_zero, a_zero] at h1
            omega
          · by_cases hm1_eq : m = 1
            · subst hm1_eq
              have h1 : S 1 = S 0 + a 0 := S_step 0 (by omega)
              have h2 : S 2 = S 1 + a 1 := S_step 1 (by omega)
              rw [S_zero, a_zero] at h1
              rw [h1, a_one] at h2
              rw [h2]
            · have hm2 : m ≥ 2 := by omega
              have hm_lt : m < n := by omega
              have h_step := S_step m hm_lt
              have h_am_nz := IH m hm_lt
              have h_am_ne_one := h_ar_ne_one m hm_lt hm2
              have h_am_ge : a m ≥ 2 := by omega
              have ih' := ih (by omega) (by omega)
              omega

      by_cases hk_jd : k - 1 - j_d = 1
      · have h_eq : j_d = k - 2 := by omega
        have h1 : k - 2 < d := by omega
        have h2 : d < k - 1 := by omega
        omega
      · have h_jd_le : j_d ≤ k - 3 := by omega
        have hk1_ge_13 : k-1 ≥ 13 := by
          by_contra! hk1_lt
          have h_Sk_le : S k ≤ S 12 + a (k-1) := by
            have h_mono := h_S_mono 12 (k-1) (by omega) (by omega)
            have h_step_eq := S_step (k-1) (by omega)
            omega
          have h_S12_val : S 12 = 37 := by
            have h0 := S_step 0 (by omega)
            have h1 := S_step 1 (by omega)
            have h2 := S_step 2 (by omega)
            have h3 := S_step 3 (by omega)
            have h4 := S_step 4 (by omega)
            have h5 := S_step 5 (by omega)
            have h6 := S_step 6 (by omega)
            have h7 := S_step 7 (by omega)
            have h8 := S_step 8 (by omega)
            have h9 := S_step 9 (by omega)
            have h10 := S_step 10 (by omega)
            have h11 := S_step 11 (by omega)
            rw [S_zero, a_zero] at h0
            rw [h0, a_one] at h1
            rw [h1, a_two] at h2
            rw [h2, a_three] at h3
            rw [h3, a_four] at h4
            rw [h4, a_five] at h5
            rw [h5, a_six] at h6
            rw [h6, a_seven] at h7
            rw [h7, a_eight] at h8
            rw [h8, a_nine] at h9
            rw [h9, a_ten] at h10
            rw [h10, a_eleven] at h11
            exact h11
          have h_ak1_le_7 : a (k-1) ≤ 7 := by
            generalize hk1_eq : k - 1 = k1
            have hk1_lt' : k1 < 13 := by omega
            rcases k1 with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
            · rw [a_zero]; decide
            · rw [a_one]; decide
            · rw [a_two]; decide
            · rw [a_three]; decide
            · rw [a_four]; decide
            · rw [a_five]; decide
            · rw [a_six]; decide
            · rw [a_seven]; decide
            · rw [a_eight]; decide
            · rw [a_nine]; decide
            · rw [a_ten]; decide
            · rw [a_eleven]; decide
            · have : n = 0 := by omega
              subst this
              rw [a_twelve]; decide
          omega

        have h_ak_le_k2 : a (k-1) ≤ k - 2 := by
          rw [a_eq (k-1)]
          have hk1_nz_eq : k - 1 ≠ 0 := by omega
          rw [if_neg hk1_nz_eq]
          dsimp
          apply Finset.sup_le
          intro i hi
          apply Finset.sup_le
          intro j hj
          have : k - 1 = k - 2 + 1 := by omega
          split_ifs with hij h_sum
          · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
            have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
            have hj_lt : j < k - 1 := by
              rw [Finset.mem_range] at hj
              exact hj
            by_cases h_max : j - i + 1 ≥ k - 1
            · have hk2 : k ≥ 13 := by omega
              have h_eq_i : i = 0 := by omega
              have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                apply List.ext_get
                · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                  omega
                · intro idx h1 h2
                  simp
              rw [h_sublist_eq] at h_sum
              have h_sum_val := S_sum i j hij (by omega)
              rw [h_sum] at h_sum_val
              subst h_eq_i
              rw [S_zero] at h_sum_val
              simp at h_sum_val
              have hj_ge : j + 1 ≥ k - 1 := by omega
              have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
              have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
              omega
            · omega
          · omega
          · omega

        have h_ak_le_k3 : a (k-1) ≤ k - 3 := by
          rw [a_eq (k-1)]
          have hk1_nz_eq : k - 1 ≠ 0 := by omega
          rw [if_neg hk1_nz_eq]
          dsimp
          apply Finset.sup_le
          intro i hi
          apply Finset.sup_le
          intro j hj
          have : k - 2 = k - 3 + 1 := by omega
          have : k - 1 = k - 3 + 2 := by omega
          split_ifs with hij h_sum
          · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
            have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
            have hj_lt : j < k - 1 := by
              rw [Finset.mem_range] at hj
              exact hj
            by_cases h_max : j - i + 1 ≥ k - 2
            · have hk2 : k ≥ 13 := by omega
              have h_eq_i : i < 2 := by omega
              have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                apply List.ext_get
                · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                  omega
                · intro idx h1 h2
                  simp
              rw [h_sublist_eq] at h_sum
              have h_sum_val := S_sum i j hij (by omega)
              rw [h_sum] at h_sum_val
              interval_cases i
              · rw [S_zero] at h_sum_val
                simp at h_sum_val
                have hj_ge : j + 1 ≥ k - 2 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                rw [h_S1] at h_sum_val
                have hj_ge : j + 1 ≥ k - 1 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                omega
            · omega
          · omega
          · omega

        have h_ak_le_k4 : a (k-1) ≤ k - 4 := by
          rw [a_eq (k-1)]
          have hk1_nz_eq : k - 1 ≠ 0 := by omega
          rw [if_neg hk1_nz_eq]
          dsimp
          apply Finset.sup_le
          intro i hi
          apply Finset.sup_le
          intro j hj
          have : k - 3 = k - 4 + 1 := by omega
          have : k - 2 = k - 4 + 2 := by omega
          have : k - 1 = k - 4 + 3 := by omega
          split_ifs with hij h_sum
          · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
            have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
            have hj_lt : j < k - 1 := by
              rw [Finset.mem_range] at hj
              exact hj
            by_cases h_max : j - i + 1 ≥ k - 3
            · have hk2 : k ≥ 13 := by omega
              have h_eq_i : i < 3 := by omega
              have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                apply List.ext_get
                · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                  omega
                · intro idx h1 h2
                  simp
              rw [h_sublist_eq] at h_sum
              have h_sum_val := S_sum i j hij (by omega)
              rw [h_sum] at h_sum_val
              interval_cases i
              · rw [S_zero] at h_sum_val
                simp at h_sum_val
                have hj_ge : j + 1 ≥ k - 3 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-3) (by omega) (by omega)
                have h_sum_ge_k3 : S (k-3) ≥ 2 * k - 8 := by have h := h_sum_ge_2 (k-3) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                rw [h_S1] at h_sum_val
                have hj_ge : j + 1 ≥ k - 2 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                rw [h_S2] at h_sum_val
                have hj_ge : j + 1 ≥ k - 1 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                omega
            · omega
          · omega
          · omega

        have h_ak_le_k5 : a (k-1) ≤ k - 5 := by
          rw [a_eq (k-1)]
          have hk1_nz_eq : k - 1 ≠ 0 := by omega
          rw [if_neg hk1_nz_eq]
          dsimp
          apply Finset.sup_le
          intro i hi
          apply Finset.sup_le
          intro j hj
          have : k - 4 = k - 5 + 1 := by omega
          have : k - 3 = k - 5 + 2 := by omega
          have : k - 2 = k - 5 + 3 := by omega
          have : k - 1 = k - 5 + 4 := by omega
          split_ifs with hij h_sum
          · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
            have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
            have hj_lt : j < k - 1 := by
              rw [Finset.mem_range] at hj
              exact hj
            by_cases h_max : j - i + 1 ≥ k - 4
            · have hk2 : k ≥ 13 := by omega
              have h_eq_i : i < 4 := by omega
              have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                apply List.ext_get
                · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                  omega
                · intro idx h1 h2
                  simp
              rw [h_sublist_eq] at h_sum
              have h_sum_val := S_sum i j hij (by omega)
              rw [h_sum] at h_sum_val
              interval_cases i
              · rw [S_zero] at h_sum_val
                simp at h_sum_val
                have hj_ge : j + 1 ≥ k - 4 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-4) (by omega) (by omega)
                have h_sum_ge_k4 : S (k-4) ≥ 2 * k - 10 := by have h := h_sum_ge_2 (k-4) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                rw [h_S1] at h_sum_val
                have hj_ge : j + 1 ≥ k - 3 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-3) (by omega) (by omega)
                have h_sum_ge_k3 : S (k-3) ≥ 2 * k - 8 := by have h := h_sum_ge_2 (k-3) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                rw [h_S2] at h_sum_val
                have hj_ge : j + 1 ≥ k - 2 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                have h_S3 : S 3 = 4 := by
                  rw [S_step 2 (by omega), h_S2, a_two]
                rw [h_S3] at h_sum_val
                have hj_ge : j + 1 ≥ k - 1 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                omega
            · omega
          · omega
          · omega

        have h_ak_le_k6 : a (k-1) ≤ k - 6 := by
          rw [a_eq (k-1)]
          have hk1_nz_eq : k - 1 ≠ 0 := by omega
          rw [if_neg hk1_nz_eq]
          dsimp
          apply Finset.sup_le
          intro i hi
          apply Finset.sup_le
          intro j hj
          have : k - 5 = k - 6 + 1 := by omega
          have : k - 4 = k - 6 + 2 := by omega
          have : k - 3 = k - 6 + 3 := by omega
          have : k - 2 = k - 6 + 4 := by omega
          have : k - 1 = k - 6 + 5 := by omega
          split_ifs with hij h_sum
          · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
            have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
            have hj_lt : j < k - 1 := by
              rw [Finset.mem_range] at hj
              exact hj
            by_cases h_max : j - i + 1 ≥ k - 5
            · have hk2 : k ≥ 13 := by omega
              have h_eq_i : i < 5 := by omega
              have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                apply List.ext_get
                · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                  omega
                · intro idx h1 h2
                  simp
              rw [h_sublist_eq] at h_sum
              have h_sum_val := S_sum i j hij (by omega)
              rw [h_sum] at h_sum_val
              interval_cases i
              · rw [S_zero] at h_sum_val
                simp at h_sum_val
                have hj_ge : j + 1 ≥ k - 5 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-5) (by omega) (by omega)
                have h_sum_ge_k5 : S (k-5) ≥ 2 * k - 12 := by have h := h_sum_ge_2 (k-5) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                rw [h_S1] at h_sum_val
                have hj_ge : j + 1 ≥ k - 4 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-4) (by omega) (by omega)
                have h_sum_ge_k4 : S (k-4) ≥ 2 * k - 10 := by have h := h_sum_ge_2 (k-4) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                rw [h_S2] at h_sum_val
                have hj_ge : j + 1 ≥ k - 3 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-3) (by omega) (by omega)
                have h_sum_ge_k3 : S (k-3) ≥ 2 * k - 8 := by have h := h_sum_ge_2 (k-3) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                have h_S3 : S 3 = 4 := by
                  rw [S_step 2 (by omega), h_S2, a_two]
                rw [h_S3] at h_sum_val
                have hj_ge : j + 1 ≥ k - 2 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                have h_S3 : S 3 = 4 := by
                  rw [S_step 2 (by omega), h_S2, a_two]
                have h_S4 : S 4 = 6 := by
                  rw [S_step 3 (by omega), h_S3, a_three]
                rw [h_S4] at h_sum_val
                have hj_ge : j + 1 ≥ k - 1 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                omega
            · omega
          · omega
          · omega

        have h_ak_le_k7 : a (k-1) ≤ k - 7 := by
          rw [a_eq (k-1)]
          have hk1_nz_eq : k - 1 ≠ 0 := by omega
          rw [if_neg hk1_nz_eq]
          dsimp
          apply Finset.sup_le
          intro i hi
          apply Finset.sup_le
          intro j hj
          have : k - 6 = k - 7 + 1 := by omega
          have : k - 5 = k - 7 + 2 := by omega
          have : k - 4 = k - 7 + 3 := by omega
          have : k - 3 = k - 7 + 4 := by omega
          have : k - 2 = k - 7 + 5 := by omega
          have : k - 1 = k - 7 + 6 := by omega
          split_ifs with hij h_sum
          · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
            have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
            have hj_lt : j < k - 1 := by
              rw [Finset.mem_range] at hj
              exact hj
            by_cases h_max : j - i + 1 ≥ k - 6
            · have hk2 : k ≥ 13 := by omega
              have h_eq_i : i < 6 := by omega
              have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                apply List.ext_get
                · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                  omega
                · intro idx h1 h2
                  simp
              rw [h_sublist_eq] at h_sum
              have h_sum_val := S_sum i j hij (by omega)
              rw [h_sum] at h_sum_val
              interval_cases i
              · rw [S_zero] at h_sum_val
                simp at h_sum_val
                have hj_ge : j + 1 ≥ k - 6 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-6) (by omega) (by omega)
                have h_sum_ge_k6 : S (k-6) ≥ 2 * k - 14 := by have h := h_sum_ge_2 (k-6) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                rw [h_S1] at h_sum_val
                have hj_ge : j + 1 ≥ k - 5 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-5) (by omega) (by omega)
                have h_sum_ge_k5 : S (k-5) ≥ 2 * k - 12 := by have h := h_sum_ge_2 (k-5) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                rw [h_S2] at h_sum_val
                have hj_ge : j + 1 ≥ k - 4 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-4) (by omega) (by omega)
                have h_sum_ge_k4 : S (k-4) ≥ 2 * k - 10 := by have h := h_sum_ge_2 (k-4) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                have h_S3 : S 3 = 4 := by
                  rw [S_step 2 (by omega), h_S2, a_two]
                rw [h_S3] at h_sum_val
                have hj_ge : j + 1 ≥ k - 3 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-3) (by omega) (by omega)
                have h_sum_ge_k3 : S (k-3) ≥ 2 * k - 8 := by have h := h_sum_ge_2 (k-3) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                have h_S3 : S 3 = 4 := by
                  rw [S_step 2 (by omega), h_S2, a_two]
                have h_S4 : S 4 = 6 := by
                  rw [S_step 3 (by omega), h_S3, a_three]
                rw [h_S4] at h_sum_val
                have hj_ge : j + 1 ≥ k - 2 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                omega
              · have h_S1 : S 1 = 1 := by
                  rw [S_step 0 (by omega), S_zero, a_zero]
                have h_S2 : S 2 = 2 := by
                  rw [S_step 1 (by omega), h_S1, a_one]
                have h_S3 : S 3 = 4 := by
                  rw [S_step 2 (by omega), h_S2, a_two]
                have h_S4 : S 4 = 6 := by
                  rw [S_step 3 (by omega), h_S3, a_three]
                have h_S5 : S 5 = 9 := by
                  rw [S_step 4 (by omega), h_S4, a_four]
                rw [h_S5] at h_sum_val
                have hj_ge : j + 1 ≥ k - 1 := by omega
                have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                omega
            · omega
          · omega
          · omega

        have h_ak_le_k8 : a (k-1) ≤ k - 8 := by
          have hk_ge_14 : k ≥ 14 := by omega
          by_cases hk_lt : k < 16
          · interval_cases k
            · rw [a_thirteen]; omega
            · rw [a_fourteen]; omega
          · rw [a_eq (k-1)]
            have hk1_nz_eq : k - 1 ≠ 0 := by omega
            rw [if_neg hk1_nz_eq]
            dsimp
            apply Finset.sup_le
            intro i hi
            apply Finset.sup_le
            intro j hj
            have : k - 7 = k - 8 + 1 := by omega
            have : k - 6 = k - 8 + 2 := by omega
            have : k - 5 = k - 8 + 3 := by omega
            have : k - 4 = k - 8 + 4 := by omega
            have : k - 3 = k - 8 + 5 := by omega
            have : k - 2 = k - 8 + 6 := by omega
            have : k - 1 = k - 8 + 7 := by omega
            split_ifs with hij h_sum
            · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
              have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
              have hj_lt : j < k - 1 := by
                rw [Finset.mem_range] at hj
                exact hj
              by_cases h_max : j - i + 1 ≥ k - 7
              · have hk2 : k ≥ 13 := by omega
                have h_eq_i : i < 7 := by omega
                have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                  apply List.ext_get
                  · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                    omega
                  · intro idx h1 h2
                    simp
                rw [h_sublist_eq] at h_sum
                have h_sum_val := S_sum i j hij (by omega)
                rw [h_sum] at h_sum_val
                interval_cases i
                · rw [S_zero] at h_sum_val
                  simp at h_sum_val
                  have hj_ge : j + 1 ≥ k - 7 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-7) (by omega) (by omega)
                  have h_sum_ge_k7 : S (k-7) ≥ 2 * k - 16 := by have h := h_sum_ge_2 (k-7) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  rw [h_S1] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 6 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-6) (by omega) (by omega)
                  have h_sum_ge_k6 : S (k-6) ≥ 2 * k - 14 := by have h := h_sum_ge_2 (k-6) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  rw [h_S2] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 5 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-5) (by omega) (by omega)
                  have h_sum_ge_k5 : S (k-5) ≥ 2 * k - 12 := by have h := h_sum_ge_2 (k-5) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  rw [h_S3] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 4 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-4) (by omega) (by omega)
                  have h_sum_ge_k4 : S (k-4) ≥ 2 * k - 10 := by have h := h_sum_ge_2 (k-4) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  rw [h_S4] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 3 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-3) (by omega) (by omega)
                  have h_sum_ge_k3 : S (k-3) ≥ 2 * k - 8 := by have h := h_sum_ge_2 (k-3) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  rw [h_S5] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 2 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                  have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  have h_S6 : S 6 = 12 := by
                    rw [S_step 5 (by omega), h_S5, a_five]
                  rw [h_S6] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 1 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                  have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                  omega
              · omega
            · omega
            · omega

        have h_ak_le_k9 : a (k-1) ≤ k - 9 := by
          have hk_ge_14 : k ≥ 14 := by omega
          by_cases hk_lt : k < 19
          · interval_cases k
            · rw [a_thirteen]; omega
            · rw [a_fourteen]; omega
            · rw [a_fifteen]; omega
            · rw [a_sixteen]; omega
            · rw [a_seventeen]; omega
          · rw [a_eq (k-1)]
            have hk1_nz_eq : k - 1 ≠ 0 := by omega
            rw [if_neg hk1_nz_eq]
            dsimp
            apply Finset.sup_le
            intro i hi
            apply Finset.sup_le
            intro j hj
            have : k - 8 = k - 9 + 1 := by omega
            have : k - 7 = k - 9 + 2 := by omega
            have : k - 6 = k - 9 + 3 := by omega
            have : k - 5 = k - 9 + 4 := by omega
            have : k - 4 = k - 9 + 5 := by omega
            have : k - 3 = k - 9 + 6 := by omega
            have : k - 2 = k - 9 + 7 := by omega
            have : k - 1 = k - 9 + 8 := by omega
            split_ifs with hij h_sum
            · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
              have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
              have hj_lt : j < k - 1 := by
                rw [Finset.mem_range] at hj
                exact hj
              by_cases h_max : j - i + 1 ≥ k - 8
              · have hk2 : k ≥ 13 := by omega
                have h_eq_i : i < 8 := by omega
                have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                  apply List.ext_get
                  · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                    omega
                  · intro idx h1 h2
                    simp
                rw [h_sublist_eq] at h_sum
                have h_sum_val := S_sum i j hij (by omega)
                rw [h_sum] at h_sum_val
                interval_cases i
                · rw [S_zero] at h_sum_val
                  simp at h_sum_val
                  have hj_ge : j + 1 ≥ k - 8 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-8) (by omega) (by omega)
                  have h_sum_ge_k8 : S (k-8) ≥ 2 * k - 18 := by have h := h_sum_ge_2 (k-8) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  rw [h_S1] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 7 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-7) (by omega) (by omega)
                  have h_sum_ge_k7 : S (k-7) ≥ 2 * k - 16 := by have h := h_sum_ge_2 (k-7) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  rw [h_S2] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 6 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-6) (by omega) (by omega)
                  have h_sum_ge_k6 : S (k-6) ≥ 2 * k - 14 := by have h := h_sum_ge_2 (k-6) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  rw [h_S3] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 5 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-5) (by omega) (by omega)
                  have h_sum_ge_k5 : S (k-5) ≥ 2 * k - 12 := by have h := h_sum_ge_2 (k-5) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  rw [h_S4] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 4 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-4) (by omega) (by omega)
                  have h_sum_ge_k4 : S (k-4) ≥ 2 * k - 10 := by have h := h_sum_ge_2 (k-4) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  rw [h_S5] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 3 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-3) (by omega) (by omega)
                  have h_sum_ge_k3 : S (k-3) ≥ 2 * k - 8 := by have h := h_sum_ge_2 (k-3) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  have h_S6 : S 6 = 12 := by
                    rw [S_step 5 (by omega), h_S5, a_five]
                  rw [h_S6] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 2 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                  have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  have h_S6 : S 6 = 12 := by
                    rw [S_step 5 (by omega), h_S5, a_five]
                  have h_S7 : S 7 = 16 := by
                    rw [S_step 6 (by omega), h_S6, a_six]
                  rw [h_S7] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 1 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                  have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                  omega
              · omega
            · omega
            · omega

        have h_ak_le_k10 : a (k-1) ≤ k - 10 := by
          have hk_ge_14 : k ≥ 14 := by omega
          by_cases hk_lt : k < 24
          · interval_cases k
            · rw [a_thirteen]
            · rw [a_fourteen]
            · rw [a_fifteen]
            · rw [a_sixteen]
            · rw [a_seventeen]; omega
            · rw [a_eighteen]; omega
            · rw [a_nineteen]; omega
            · rw [a_twenty]; omega
            · rw [a_twenty_one]; omega
            · rw [a_twenty_two]; omega
          · rw [a_eq (k-1)]
            have hk1_nz_eq : k - 1 ≠ 0 := by omega
            rw [if_neg hk1_nz_eq]
            dsimp
            apply Finset.sup_le
            intro i hi
            apply Finset.sup_le
            intro j hj
            have : k - 9 = k - 10 + 1 := by omega
            have : k - 8 = k - 10 + 2 := by omega
            have : k - 7 = k - 10 + 3 := by omega
            have : k - 6 = k - 10 + 4 := by omega
            have : k - 5 = k - 10 + 5 := by omega
            have : k - 4 = k - 10 + 6 := by omega
            have : k - 3 = k - 10 + 7 := by omega
            have : k - 2 = k - 10 + 8 := by omega
            have : k - 1 = k - 10 + 9 := by omega
            split_ifs with hij h_sum
            · have h_cnt := List.countP_le_length (p := fun x => decide ¬x = 0) (l := ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)))
              have h_len : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)).length ≤ j - i + 1 := List.length_take_le _ _
              have hj_lt : j < k - 1 := by
                rw [Finset.mem_range] at hj
                exact hj
              by_cases h_max : j - i + 1 ≥ k - 9
              · have hk2 : k ≥ 13 := by omega
                have h_eq_i : i < 9 := by omega
                have h_sublist_eq : ((List.ofFn (fun k_1 : Fin (k-1) => a k_1.val)).drop i |>.take (j - i + 1)) = ((List.ofFn (fun k_1 : Fin n => a k_1.val)).drop i |>.take (j - i + 1)) := by
                  apply List.ext_get
                  · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_take, List.length_drop, List.length_ofFn]
                    omega
                  · intro idx h1 h2
                    simp
                rw [h_sublist_eq] at h_sum
                have h_sum_val := S_sum i j hij (by omega)
                rw [h_sum] at h_sum_val
                interval_cases i
                · rw [S_zero] at h_sum_val
                  simp at h_sum_val
                  have hj_ge : j + 1 ≥ k - 9 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-9) (by omega) (by omega)
                  have h_sum_ge_k9 : S (k-9) ≥ 2 * k - 20 := by have h := h_sum_ge_2 (k-9) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  rw [h_S1] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 8 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-8) (by omega) (by omega)
                  have h_sum_ge_k8 : S (k-8) ≥ 2 * k - 18 := by have h := h_sum_ge_2 (k-8) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  rw [h_S2] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 7 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-7) (by omega) (by omega)
                  have h_sum_ge_k7 : S (k-7) ≥ 2 * k - 16 := by have h := h_sum_ge_2 (k-7) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  rw [h_S3] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 6 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-6) (by omega) (by omega)
                  have h_sum_ge_k6 : S (k-6) ≥ 2 * k - 14 := by have h := h_sum_ge_2 (k-6) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  rw [h_S4] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 5 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-5) (by omega) (by omega)
                  have h_sum_ge_k5 : S (k-5) ≥ 2 * k - 12 := by have h := h_sum_ge_2 (k-5) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  rw [h_S5] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 4 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-4) (by omega) (by omega)
                  have h_sum_ge_k4 : S (k-4) ≥ 2 * k - 10 := by have h := h_sum_ge_2 (k-4) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  have h_S6 : S 6 = 12 := by
                    rw [S_step 5 (by omega), h_S5, a_five]
                  rw [h_S6] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 3 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-3) (by omega) (by omega)
                  have h_sum_ge_k3 : S (k-3) ≥ 2 * k - 8 := by have h := h_sum_ge_2 (k-3) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  have h_S6 : S 6 = 12 := by
                    rw [S_step 5 (by omega), h_S5, a_five]
                  have h_S7 : S 7 = 16 := by
                    rw [S_step 6 (by omega), h_S6, a_six]
                  rw [h_S7] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 2 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-2) (by omega) (by omega)
                  have h_sum_ge_k2 : S (k-2) ≥ 2 * k - 6 := by have h := h_sum_ge_2 (k-2) (by omega) (by omega); omega
                  omega
                · have h_S1 : S 1 = 1 := by
                    rw [S_step 0 (by omega), S_zero, a_zero]
                  have h_S2 : S 2 = 2 := by
                    rw [S_step 1 (by omega), h_S1, a_one]
                  have h_S3 : S 3 = 4 := by
                    rw [S_step 2 (by omega), h_S2, a_two]
                  have h_S4 : S 4 = 6 := by
                    rw [S_step 3 (by omega), h_S3, a_three]
                  have h_S5 : S 5 = 9 := by
                    rw [S_step 4 (by omega), h_S4, a_four]
                  have h_S6 : S 6 = 12 := by
                    rw [S_step 5 (by omega), h_S5, a_five]
                  have h_S7 : S 7 = 16 := by
                    rw [S_step 6 (by omega), h_S6, a_six]
                  have h_S8 : S 8 = 19 := by
                    rw [S_step 7 (by omega), h_S7, a_seven]
                  rw [h_S8] at h_sum_val
                  have hj_ge : j + 1 ≥ k - 1 := by omega
                  have h_S_mono_val := h_S_mono (j+1) (k-1) (by omega) (by omega)
                  have h_sum_ge_k1 : S (k-1) ≥ 2 * k - 4 := by have h := h_sum_ge_2 (k-1) (by omega) (by omega); omega
                  omega
              · omega
            · omega
            · omega

        omega
