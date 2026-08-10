import FormalConjectures.Util.ProblemImports

open List Nat Real Filter Topology Set

/-- Computes the run lengths of a list of natural numbers. -/
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

theorem run_lengths_nat_sum_eq_length (l : List ℕ) : (run_lengths_nat l).sum = l.length := by
  induction l using run_lengths_nat.induct
  · simp [run_lengths_nat]
  · rename_i h_head t_tail run_pref rest ih
    unfold run_lengths_nat
    simp only [sum_cons]
    rw [ih]
    have h_le : run_pref.length ≤ (h_head :: t_tail).length := by
      have h_pref : run_pref <+: (h_head :: t_tail) := List.takeWhile_prefix (fun x => decide (x = h_head))
      exact List.IsPrefix.length_le h_pref
    rw [List.length_drop]
    dsimp only [run_pref] at *
    omega

theorem run_lengths_nat_length_le (l : List ℕ) : (run_lengths_nat l).length ≤ l.length := by
  induction l using run_lengths_nat.induct
  · simp [run_lengths_nat]
  · rename_i h_head t_tail run_pref rest ih
    unfold run_lengths_nat
    simp only [length_cons]
    have h_pref_ge : run_pref.length ≥ 1 := by
      dsimp only [run_pref]
      rw [takeWhile]
      simp only [decide_true, length_cons, ge_iff_le]
      omega
    revert ih h_pref_ge
    dsimp only [rest, run_pref]
    clear rest run_pref
    intro h_pref_ge ih
    simp only [] at *
    have h_drop : (drop (takeWhile (fun x => decide (x = h_head)) (h_head :: t_tail)).length (h_head :: t_tail)).length =
      (h_head :: t_tail).length - (takeWhile (fun x => decide (x = h_head)) (h_head :: t_tail)).length := List.length_drop
    simp only [length_cons] at h_drop
    omega


theorem takeWhile_eq_of_prefix {α : Type*} (p : α → Bool) (A B : List α) (h : A <+: B) (h_len : (A.takeWhile p).length < A.length) : A.takeWhile p = B.takeWhile p := by
  induction A generalizing B with
  | nil =>
    simp at h_len
  | cons a A_tail ih =>
    rcases B with _ | ⟨b, B_tail⟩
    · have h_len_le := List.IsPrefix.length_le h
      simp only [length_cons, List.length_nil] at h_len_le
      omega
    · rcases h with ⟨C, h_eq⟩
      simp only [cons_append] at h_eq
      injection h_eq with h_head h_tail
      subst h_head
      have h_t_tail : A_tail <+: B_tail := ⟨C, h_tail⟩
      rw [List.takeWhile_cons, List.takeWhile_cons]
      by_cases hp : p a = true
      · simp [hp]
        have h_len' : (A_tail.takeWhile p).length < A_tail.length := by
          rw [List.takeWhile_cons] at h_len
          simp [hp] at h_len
          omega
        rw [ih B_tail h_t_tail h_len']
      · simp [hp]

theorem IsPrefix.drop {α : Type*} {A B : List α} (h : A <+: B) (n : ℕ) : A.drop n <+: B.drop n := by
  by_cases hn : n ≤ A.length
  · rcases h with ⟨C, rfl⟩
    rw [drop_append_of_le_length hn]
    exact prefix_append _ _
  · have hn' : A.length ≤ n := by omega
    rw [drop_of_length_le hn']
    exact nil_prefix

theorem run_lengths_nat_prefix_dropLast {P X : List ℕ} (h_pref : P <+: X) : (run_lengths_nat P).dropLast <+: run_lengths_nat X := by
  induction P using run_lengths_nat.induct generalizing X
  · simp [run_lengths_nat]
  · rename_i h_head t_tail run_pref rest ih
    rcases X with _ | ⟨x_head, x_tail⟩
    · have h_len := List.IsPrefix.length_le h_pref
      simp only [length_cons, List.length_nil] at h_len
      omega
    · rcases h_pref with ⟨C, h_eq⟩
      simp only [cons_append] at h_eq
      injection h_eq with h_head_eq h_tail_eq
      subst h_head_eq
      have h_t_tail : t_tail <+: x_tail := ⟨C, h_tail_eq⟩
      have h_prefix_list : (h_head :: t_tail) <+: (h_head :: x_tail) := ⟨C, by simp [h_tail_eq]⟩
      let p := fun x => decide (x = h_head)
      by_cases h_len : run_pref.length < (h_head :: t_tail).length
      · have h_tw_eq_pre := takeWhile_eq_of_prefix p (h_head :: t_tail) (h_head :: x_tail) h_prefix_list h_len
        have h_tw_eq : run_pref = (h_head :: x_tail).takeWhile p := h_tw_eq_pre
        have h_tw_eq_len : run_pref.length = ((h_head :: x_tail).takeWhile p).length := by rw [h_tw_eq]
        have h_drop_pref : rest <+: (h_head :: x_tail).drop ((h_head :: x_tail).takeWhile p).length := by
          rw [← h_tw_eq_len]
          exact IsPrefix.drop h_prefix_list run_pref.length
        have ih_val := ih h_drop_pref
        have h_P_unroll : run_lengths_nat (h_head :: t_tail) = run_pref.length :: run_lengths_nat rest := by
          rw [run_lengths_nat]
        rw [h_P_unroll]
        by_cases hr : run_lengths_nat rest = []
        · rw [hr]
          have h_empty : (run_pref.length :: [] : List ℕ).dropLast = [] := rfl
          rw [h_empty]
          exact nil_prefix
        · rcases h_rl : run_lengths_nat rest with _ | ⟨r_hd, r_tl⟩
          · contradiction
          · change run_pref.length :: (r_hd :: r_tl).dropLast <+: _
            rw [← h_rl]
            have h_X_unroll : run_lengths_nat (h_head :: x_tail) = ((h_head :: x_tail).takeWhile p).length :: run_lengths_nat ((h_head :: x_tail).drop ((h_head :: x_tail).takeWhile p).length) := by
              rw [run_lengths_nat]
            rw [h_X_unroll]
            rw [← h_tw_eq_len]
            rcases ih_val with ⟨C2, hC2⟩
            use C2
            rw [← h_tw_eq_len] at hC2
            change run_pref.length :: ((run_lengths_nat rest).dropLast ++ C2) = _
            rw [hC2]
      · have h_len_ge : (h_head :: t_tail).length ≤ run_pref.length := by omega
        have h_drop_nil : rest = [] := by
          exact drop_of_length_le h_len_ge
        have h_P_unroll : run_lengths_nat (h_head :: t_tail) = run_pref.length :: run_lengths_nat rest := by
          rw [run_lengths_nat]
        rw [h_P_unroll, h_drop_nil]
        have h_empty : run_lengths_nat [] = [] := by
          unfold run_lengths_nat
          rfl
        rw [h_empty]
        have h_empty2 : (run_pref.length :: [] : List ℕ).dropLast = [] := rfl
        rw [h_empty2]
        exact nil_prefix

theorem IsSuffix.drop_one {α : Type*} {A B : List α} (h : A <:+ B) : A.drop 1 <:+ B.drop 1 := by
  rcases h with ⟨C, rfl⟩
  rcases C with _ | ⟨c, C_tail⟩
  · simp
  · simp only [List.cons_append, List.drop]
    use C_tail ++ A.take 1
    rw [List.append_assoc]
    rw [List.take_append_drop]

theorem reverse_dropLast {α : Type*} (l : List α) (hl : l.length ≥ 1) : l.dropLast.reverse = l.reverse.drop 1 := by
  rw [List.dropLast_eq_take]
  rw [List.reverse_take]
  have h_sub : l.length - (l.length - 1) = 1 := by omega
  rw [h_sub]

theorem run_lengths_nat_length_ge_one (L : List ℕ) (hL : L.length ≥ 1) : (run_lengths_nat L).length ≥ 1 := by
  have h_sum := run_lengths_nat_sum_eq_length L
  by_cases h : (run_lengths_nat L).length = 0
  · have h_nil := List.eq_nil_of_length_eq_zero h
    rw [h_nil] at h_sum
    simp only [List.sum_nil] at h_sum
    omega
  · omega

theorem run_lengths_nat_no_adj_eq (l : List ℕ) (hl : ∀ (i : ℕ) (h1 : i + 1 < l.length), l.get ⟨i, by omega⟩ ≠ l.get ⟨i + 1, h1⟩) :
    (run_lengths_nat l).length = l.length := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    simp [run_lengths_nat]
  | case2 h_head t_tail run_pref rest ih =>
    have h_rest : rest = t_tail := by
      rcases t_tail with _ | ⟨y, tail2⟩
      · dsimp only [rest, run_pref]
        simp [takeWhile]
      · -- y :: tail2 is non-empty. Since h_head ≠ y, takeWhile is [h_head].
        have h_neq : h_head ≠ y := by
          have h_get1 : (h_head :: y :: tail2).get ⟨0, by simp only [length_cons]; omega⟩ = h_head := rfl
          have h_get2 : (h_head :: y :: tail2).get ⟨1, by simp only [length_cons]; omega⟩ = y := rfl
          have h_spec := hl 0 (by simp only [length_cons]; omega)
          rw [h_get1, h_get2] at h_spec
          exact h_spec
        have h_tw : (h_head :: y :: tail2).takeWhile (fun x => decide (x = h_head)) = [h_head] := by
          rw [takeWhile_cons]
          simp only [decide_true]
          have h_tw_tail : (y :: tail2).takeWhile (fun x => decide (x = h_head)) = [] := by
            rw [takeWhile_cons]
            simp [h_neq.symm]
          rw [h_tw_tail]
          rfl
        have h_len : ((h_head :: y :: tail2).takeWhile (fun x => decide (x = h_head))).length = 1 := by
          rw [h_tw]
          rfl
        have h_rest_def : rest = drop ((h_head :: y :: tail2).takeWhile (fun x => decide (x = h_head))).length (h_head :: y :: tail2) := rfl
        rw [h_rest_def, h_len]
        rfl
    have hl_tail : ∀ (i : ℕ) (h1 : i + 1 < t_tail.length), t_tail.get ⟨i, by omega⟩ ≠ t_tail.get ⟨i + 1, h1⟩ := by
      intro i h1
      have h_spec := hl (i + 1) (by simp only [length_cons]; omega)
      have h_get1 : (h_head :: t_tail).get ⟨i + 1, by simp only [length_cons]; omega⟩ = t_tail.get ⟨i, by omega⟩ := rfl
      have h_get2 : (h_head :: t_tail).get ⟨i + 1 + 1, by simp only [length_cons]; omega⟩ = t_tail.get ⟨i + 1, by omega⟩ := rfl
      rw [h_get1, h_get2] at h_spec
      exact h_spec
    have ih' := ih
    rw [h_rest] at ih'
    have ih_val := ih' hl_tail
    rw [run_lengths_nat]
    simp only [length_cons]
    change (run_lengths_nat rest).length + 1 = t_tail.length + 1
    rw [h_rest, ih_val]

theorem run_lengths_nat_cons_cons_eq (x : ℕ) (tail : List ℕ) :
    (run_lengths_nat (x :: x :: tail)).length = (run_lengths_nat (x :: tail)).length := by
  unfold run_lengths_nat
  simp only [length_cons]
  let p := fun x_1 => decide (x_1 = x)
  have h_tw : (takeWhile p (x :: x :: tail)).length = (takeWhile p (x :: tail)).length + 1 := by
    change (takeWhile p (x :: x :: tail)).length = (x :: takeWhile p (x :: tail)).length
    congr 2
    unfold takeWhile
    simp [p]
  rw [h_tw]
  have h_drop : ∀ (n : ℕ) (l : List ℕ) (y : ℕ), drop (n + 1) (y :: l) = drop n l := by
    intro n l y
    rfl
  rw [h_drop (takeWhile p (x :: tail)).length (x :: tail) x]


/--
A381587 $T_n$: The $n$-th row of the irregular triangle, following the recurrence:
$T_1=[1], T_2=[1], T_3=[2]$. For $n \ge 4$, $T_n = \text{Runs}(\text{Reverse}(T_{n-1})) \frown T_{n-1}$.
$n$ is 1-indexed here.
-/
private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 => -- Covers indices >= 4. Recurses on k+3, which is n-1.
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

theorem T_3 : A381587_T 3 = [2] := rfl

theorem T_4 : A381587_T 4 = [1, 2] := by
  change run_lengths_nat (A381587_T 3).reverse ++ A381587_T 3 = _
  rw [T_3]
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  rfl

theorem T_5 : A381587_T 5 = [1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 4).reverse ++ A381587_T 4 = _
  rw [T_4]
  simp only [reverse_cons, reverse_nil, cons_append, nil_append]
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  rfl

theorem T_6 : A381587_T 6 = [1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 5).reverse ++ A381587_T 5 = _
  rw [T_5]
  change run_lengths_nat [2, 1, 1, 1] ++ [1, 1, 1, 2] = _
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  rfl

theorem T_7 : A381587_T 7 = [1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 6).reverse ++ A381587_T 6 = _
  rw [T_6]
  change run_lengths_nat [2, 1, 1, 1, 3, 1] ++ [1, 3, 1, 1, 1, 2] = _
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  rfl

theorem T_8 : A381587_T 8 = [1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 7).reverse ++ A381587_T 7 = _
  rw [T_7]
  change run_lengths_nat [2, 1, 1, 1, 3, 1, 1, 1, 3, 1] ++ [1, 3, 1, 1, 1, 3, 1, 1, 1, 2] = _
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; rfl

theorem rl_rev_T_3 : run_lengths_nat (A381587_T 3).reverse = [1] := by
  rw [T_3]
  unfold run_lengths_nat
  simp
  unfold run_lengths_nat
  rfl

theorem rl_rev_T_4 : run_lengths_nat (A381587_T 4).reverse = [1, 1] := by
  rw [T_4]
  change run_lengths_nat [2, 1] = _
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; rfl

theorem rl_rev_T_5 : run_lengths_nat (A381587_T 5).reverse = [1, 3] := by
  rw [T_5]
  change run_lengths_nat [2, 1, 1, 1] = _
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; rfl

theorem rl_rev_T_6 : run_lengths_nat (A381587_T 6).reverse = [1, 3, 1, 1] := by
  rw [T_6]
  change run_lengths_nat [2, 1, 1, 1, 3, 1] = _
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; rfl

theorem rl_rev_T_7 : run_lengths_nat (A381587_T 7).reverse = [1, 3, 1, 3, 1, 1] := by
  rw [T_7]
  change run_lengths_nat [2, 1, 1, 1, 3, 1, 1, 1, 3, 1] = _
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; rfl

theorem rl_rev_T_8 : run_lengths_nat (A381587_T 8).reverse = [1, 3, 1, 3, 1, 3, 1, 1, 1, 1] := by
  rw [T_8]
  change run_lengths_nat [2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1] = _
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; rfl


theorem T_9 : A381587_T 9 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  have h : A381587_T 9 = run_lengths_nat (A381587_T 8).reverse ++ A381587_T 8 := rfl
  rw [h]
  rw [rl_rev_T_8, T_8]
  rfl

theorem rl_rev_T_9 : run_lengths_nat (A381587_T 9).reverse = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] := by
  have h : run_lengths_nat (A381587_T 9).reverse = run_lengths_nat [2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
    rw [T_9]
    rfl
  rw [h]
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; simp
  unfold run_lengths_nat; rfl

theorem T_10 : A381587_T 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  have h : A381587_T 10 = run_lengths_nat (A381587_T 9).reverse ++ A381587_T 9 := rfl
  rw [h]
  rw [rl_rev_T_9, T_9]
  rfl

theorem rl_rev_T_10 : run_lengths_nat (A381587_T 10).reverse = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1] := by
  have h : run_lengths_nat (A381587_T 10).reverse = run_lengths_nat [2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
    rw [T_10]
    rfl
  rw [h]
  repeat (unfold run_lengths_nat; simp)


/--
A381358: Row sums of irregular triangle A381587.
Row $n$ elements are $T_n$. The sequence $a(n)$ is the list sum of $T_n$.
-/
def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

theorem A381358_recurrence (k : ℕ) : A381358 (k + 4) = (A381587_T (k + 3)).length + A381358 (k + 3) := by
  unfold A381358
  rw [A381587_T]
  simp only [List.sum_append_nat]
  rw [run_lengths_nat_sum_eq_length]
  rw [length_reverse]

theorem A381587_T_length_recurrence (k : ℕ) : (A381587_T (k + 4)).length = (run_lengths_nat (A381587_T (k + 3)).reverse).length + (A381587_T (k + 3)).length := by
  rw [A381587_T]
  simp only [length_append]

theorem A381587_T_length_ge_one (n : ℕ) (hn : n ≥ 1) : (A381587_T n).length ≥ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · omega
    · rw [A381587_T]; rfl
    · rw [A381587_T]; rfl
    · rw [A381587_T]; rfl
    · rw [A381587_T_length_recurrence]
      have h1 : k + 3 < k + 4 := by omega
      have h2 : k + 3 ≥ 1 := by omega
      have ih1 := ih (k + 3) h1 h2
      omega

theorem A381587_T_length_le_two_pow (n : ℕ) : (A381587_T n).length ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · rw [A381587_T]; decide
    · rw [A381587_T]; decide
    · rw [A381587_T]; decide
    · rw [A381587_T]; decide
    · rw [A381587_T_length_recurrence]
      have h_le : (run_lengths_nat (A381587_T (k + 3)).reverse).length ≤ (A381587_T (k + 3)).length := by
        have h_len := run_lengths_nat_length_le (A381587_T (k+3)).reverse
        rw [length_reverse] at h_len
        exact h_len
      have h1 : k + 3 < k + 4 := by omega
      have ih1 := ih (k + 3) h1
      change _ ≤ 2 ^ (k + 3) * 2
      rw [mul_two]
      omega

theorem A381358_le_two_pow (n : ℕ) : A381358 n ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · unfold A381358; rw [A381587_T]; decide
    · unfold A381358; rw [A381587_T]; decide
    · unfold A381358; rw [A381587_T]; decide
    · unfold A381358; rw [A381587_T]; decide
    · rw [A381358_recurrence]
      have h1 : k + 3 < k + 4 := by omega
      have ih1 := ih (k + 3) h1
      have h_len := A381587_T_length_le_two_pow (k + 3)
      change _ + A381358 (k + 3) ≤ 2 ^ (k + 3) * 2
      rw [mul_two]
      omega

theorem A381358_ge_one (n : ℕ) (hn : n ≥ 1) : A381358 n ≥ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · omega
    · unfold A381358; rw [A381587_T]; decide
    · unfold A381358; rw [A381587_T]; decide
    · unfold A381358; rw [A381587_T]; decide
    · rw [A381358_recurrence]
      have h1 : k + 3 < k + 4 := by omega
      have h2 : k + 3 ≥ 1 := by omega
      have ih1 := ih (k + 3) h1 h2
      have h_len := A381587_T_length_ge_one (k + 3) h2
      omega

theorem A381358_recurrence_of_ge_three (n : ℕ) (hn : n ≥ 3) : A381358 (n + 1) = (A381587_T n).length + A381358 n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  have h1 : 3 + k + 1 = k + 4 := by omega
  have h2 : 3 + k = k + 3 := by omega
  rw [h1, h2]
  exact A381358_recurrence k

theorem A381358_mono_succ (n : ℕ) : A381358 n ≤ A381358 (n + 1) := by
  rcases n with _ | _ | _ | k
  · unfold A381358; rw [A381587_T]; decide
  · unfold A381358; rw [A381587_T]; decide
  · unfold A381358; rw [A381587_T]; decide
  · change A381358 (k + 3) ≤ A381358 (k + 4)
    rw [A381358_recurrence k]
    omega

theorem A381358_mono_add (n m : ℕ) : A381358 n ≤ A381358 (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : A381358 n ≤ A381358 (n + m) := ih
    have h2 : A381358 (n + m) ≤ A381358 (n + m + 1) := A381358_mono_succ (n + m)
    have h_eq : n + (m + 1) = n + m + 1 := by omega
    rw [h_eq]
    omega

theorem A381358_sum_formula (m n : ℕ) (hm : m ≥ 3) :
    A381358 (m + n) = A381358 m + ((List.range n).map (fun j => (A381587_T (m + j)).length)).sum := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h_eq : m + (n + 1) = (m + n) + 1 := by omega
    rw [h_eq]
    rw [A381358_recurrence_of_ge_three (m + n) (by omega)]
    rw [ih]
    rw [List.range_succ]
    rw [List.map_append]
    rw [List.sum_append]
    simp
    omega

theorem A381358_val_one : A381358 1 = 1 := by
  unfold A381358; rw [A381587_T]; rfl

theorem A381358_val_two : A381358 2 = 1 := by
  unfold A381358; rw [A381587_T]; rfl

theorem A381358_supermult_base (m n : ℕ) (h_m : m ≥ 1) (_ : n ≥ 1) (hm3 : m < 3) :
    A381358 (m + n) ≥ A381358 m * A381358 n := by
  interval_cases m
  · rw [A381358_val_one]
    simp only [one_mul, Nat.add_comm 1 n]
    exact A381358_mono_add n 1
  · rw [A381358_val_two]
    simp only [one_mul, Nat.add_comm 2 n]
    exact A381358_mono_add n 2


theorem T_suffix (k : ℕ) : A381587_T (k + 3) <:+ A381587_T (k + 4) := by
  rw [A381587_T]
  exact suffix_append (run_lengths_nat (A381587_T (k + 3)).reverse) (A381587_T (k + 3))

theorem T_suffix_add (k m : ℕ) : A381587_T (k + 3) <:+ A381587_T (k + 3 + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : A381587_T (k + 3 + m) <:+ A381587_T (k + 3 + m + 1) := by
      have h_eq : k + 3 + m + 1 = (k + m) + 4 := by omega
      have h_eq2 : k + 3 + m = (k + m) + 3 := by omega
      rw [h_eq, h_eq2]
      exact T_suffix (k + m)
    exact IsSuffix.trans ih h

theorem T_suffix_add_general (k m : ℕ) (hk : k ≥ 3) : A381587_T k <:+ A381587_T (k + m) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
  have h_eq : 3 + j = j + 3 := Nat.add_comm 3 j
  rw [h_eq]
  exact T_suffix_add j m

theorem IsSuffix.reverse_prefix {α : Type*} {A B : List α} (h : A <:+ B) : A.reverse <+: B.reverse := by
  rcases h with ⟨C, rfl⟩
  rw [reverse_append]
  exact prefix_append _ _

theorem run_lengths_nat_length_mono {P X : List ℕ} (h_pref : P <+: X) : (run_lengths_nat P).length ≤ (run_lengths_nat X).length := by
  induction P using run_lengths_nat.induct generalizing X
  · simp [run_lengths_nat]
  · rename_i h_head t_tail run_pref rest ih
    rcases X with _ | ⟨x_head, x_tail⟩
    · have h_len := List.IsPrefix.length_le h_pref
      simp only [length_cons, List.length_nil] at h_len
      omega
    · rcases h_pref with ⟨C, h_eq⟩
      simp only [cons_append] at h_eq
      injection h_eq with h_head_eq h_tail_eq
      subst h_head_eq
      have h_t_tail : t_tail <+: x_tail := ⟨C, h_tail_eq⟩
      unfold run_lengths_nat
      simp only [length_cons]
      have h_prefix_list : (h_head :: t_tail) <+: (h_head :: x_tail) := ⟨C, by simp [h_tail_eq]⟩
      let p := fun x => decide (x = h_head)
      change (run_lengths_nat rest).length + 1 ≤ (run_lengths_nat ((h_head :: x_tail).drop ((h_head :: x_tail).takeWhile p).length)).length + 1
      by_cases h_len : run_pref.length < (h_head :: t_tail).length
      · have h_tw_eq : run_pref = (h_head :: x_tail).takeWhile p := by
          have h_tw_eq_pre := takeWhile_eq_of_prefix p (h_head :: t_tail) (h_head :: x_tail) h_prefix_list h_len
          exact h_tw_eq_pre
        have h_tw_eq_len : run_pref.length = ((h_head :: x_tail).takeWhile p).length := by rw [h_tw_eq]
        have h_drop_pref : rest <+: (h_head :: x_tail).drop ((h_head :: x_tail).takeWhile p).length := by
          rw [← h_tw_eq_len]
          exact IsPrefix.drop h_prefix_list run_pref.length
        have h_mono := ih h_drop_pref
        omega
      · have h_len_ge : (h_head :: t_tail).length ≤ run_pref.length := by omega
        have h_drop_nil : rest = [] := by
          exact drop_of_length_le h_len_ge
        rw [h_drop_nil]
        simp [run_lengths_nat]

theorem A381587_T_length_mono (n : ℕ) (hn : n ≥ 3) : (A381587_T n).length ≤ (A381587_T (n + 1)).length := by
  have h_ge : n ≥ 3 := hn
  rcases Nat.exists_eq_add_of_le h_ge with ⟨k, hk⟩
  have h_eq1 : n + 1 = k + 4 := by omega
  have h_eq2 : n = k + 3 := by omega
  rw [h_eq1, h_eq2]
  rw [A381587_T_length_recurrence]
  omega

theorem A381587_T_length_mono_add (n m : ℕ) (hn : n ≥ 3) : (A381587_T n).length ≤ (A381587_T (n + m)).length := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (A381587_T n).length ≤ (A381587_T (n + m)).length := ih
    have h2 : (A381587_T (n + m)).length ≤ (A381587_T (n + m + 1)).length := by
      apply A381587_T_length_mono
      omega
    have h_eq : n + (m + 1) = n + m + 1 := by omega
    rw [h_eq]
    omega


theorem run_lengths_nat_cons_ge (x : ℕ) (B : List ℕ) :
    (run_lengths_nat B).length ≤ (run_lengths_nat (x :: B)).length := by
  rcases B with _ | ⟨b, tail⟩
  · simp [run_lengths_nat]
  · by_cases hb : b = x
    · subst hb
      conv_lhs => rw [run_lengths_nat]
      conv_rhs => rw [run_lengths_nat]
      simp only [takeWhile, decide_true, length_cons, drop]
      omega
    · conv_rhs => rw [run_lengths_nat]
      have h_dec : decide (b = x) = false := decide_eq_false hb
      simp [takeWhile, h_dec]


theorem run_lengths_nat_cons_le (x : ℕ) (B : List ℕ) :
    (run_lengths_nat (x :: B)).length ≤ (run_lengths_nat B).length + 1 := by
  rcases B with _ | ⟨b, tail⟩
  · simp [run_lengths_nat]
  · by_cases hb : b = x
    · subst hb
      rw [run_lengths_nat_cons_cons_eq]
      omega
    · conv_lhs => rw [run_lengths_nat]
      have h_tw : (takeWhile (fun y => decide (y = x)) (x :: b :: tail)) = [x] := by
        rw [takeWhile_cons]
        simp only [decide_true]
        have h_tw_tail : (takeWhile (fun y => decide (y = x)) (b :: tail)) = [] := by
          rw [takeWhile_cons]
          have h_dec : decide (b = x) = false := decide_eq_false hb
          rw [h_dec]
          rfl
        rw [h_tw_tail]
        rfl
      have h_len : (takeWhile (fun y => decide (y = x)) (x :: b :: tail)).length = 1 := by
        rw [h_tw]
        rfl
      rw [h_len]
      change (run_lengths_nat (b :: tail)).length + 1 ≤ (run_lengths_nat (b :: tail)).length + 1
      omega

theorem run_lengths_nat_length_le_append (A B : List ℕ) :
    (run_lengths_nat B).length ≤ (run_lengths_nat (A ++ B)).length := by
  induction A generalizing B with
  | nil => simp
  | cons a t ih =>
    have h1 : (run_lengths_nat B).length ≤ (run_lengths_nat (t ++ B)).length := ih B
    have h2 : (run_lengths_nat (t ++ B)).length ≤ (run_lengths_nat (a :: (t ++ B))).length := run_lengths_nat_cons_ge a (t ++ B)
    exact Nat.le_trans h1 h2

theorem run_lengths_nat_append_le (A B : List ℕ) :
    (run_lengths_nat A).length + (run_lengths_nat B).length ≤ (run_lengths_nat (A ++ B)).length + 1 := by
  induction A using run_lengths_nat.induct generalizing B with
  | case1 =>
    simp [run_lengths_nat]
  | case2 h_head t_tail run_pref rest ih =>
    rw [run_lengths_nat]
    change (run_lengths_nat rest).length + 1 + (run_lengths_nat B).length ≤ (run_lengths_nat (h_head :: t_tail ++ B)).length + 1
    by_cases h_len : run_pref.length < (h_head :: t_tail).length
    · have h_tw : takeWhile (fun x => decide (x = h_head)) (h_head :: (t_tail ++ B)) = run_pref := by
        have h_tw_pre := takeWhile_eq_of_prefix (fun x => decide (x = h_head)) (h_head :: t_tail) (h_head :: (t_tail ++ B)) (prefix_append (h_head :: t_tail) B) h_len
        exact h_tw_pre.symm
      have h_drop : drop (takeWhile (fun x => decide (x = h_head)) (h_head :: (t_tail ++ B))).length (h_head :: (t_tail ++ B)) = rest ++ B := by
        rw [h_tw]
        have h_le : run_pref.length ≤ (h_head :: t_tail).length := by
          have h_pref : run_pref <+: h_head :: t_tail := List.takeWhile_prefix (fun x => decide (x = h_head))
          exact List.IsPrefix.length_le h_pref
        exact drop_append_of_le_length h_le
      change (run_lengths_nat rest).length + 1 + (run_lengths_nat B).length ≤ (run_lengths_nat (h_head :: (t_tail ++ B))).length + 1
      conv_rhs => rw [run_lengths_nat]
      rw [h_drop, h_tw]
      simp only [length_cons]
      have ih_B := ih B
      omega
    · have h_rest_nil : rest = [] := drop_of_length_le (by omega)
      rw [h_rest_nil]
      simp only [run_lengths_nat, length_nil, zero_add]
      have h_le := run_lengths_nat_length_le_append (h_head :: t_tail) B
      omega


theorem IsPrefix.reverse_suffix {α : Type*} {A B : List α} (h : A <+: B) : A.reverse <:+ B.reverse := by
  rcases h with ⟨C, rfl⟩
  rw [reverse_append]
  use C.reverse

theorem run_lengths_nat_drop_one_le (A : List ℕ) (hA : A.length ≥ 1) :
    (run_lengths_nat A).length ≤ (run_lengths_nat (A.drop 1)).length + 1 := by
  rcases A with _ | ⟨a, t⟩
  · simp at hA
  · rw [List.drop]
    exact run_lengths_nat_cons_le a t

theorem run_lengths_nat_length_mono_suffix {S T : List ℕ} (h : S <:+ T) :
    (run_lengths_nat S).length ≤ (run_lengths_nat T).length := by
  rcases h with ⟨C, rfl⟩
  exact run_lengths_nat_length_le_append C S


theorem exists_concat_eq {α : Type*} {l : List α} (hl : l ≠ []) : ∃ l' x, l = l' ++ [x] := by
  induction l with
  | nil => contradiction
  | cons a t ih =>
    rcases t with _ | ⟨b, t'⟩
    · use [], a
      rfl
    · have h_ne : b :: t' ≠ [] := by simp
      rcases ih h_ne with ⟨l'', x, h⟩
      use a :: l'', x
      rw [h]
      rfl

theorem run_lengths_nat_cons_different (x : ℕ) (B : List ℕ) (hB : B ≠ []) (h_diff : x ≠ B.head hB) :
    (run_lengths_nat (x :: B)).length = (run_lengths_nat B).length + 1 := by
  rcases B with _ | ⟨y, tail⟩
  · contradiction
  · simp only [List.head_cons] at h_diff
    conv_lhs => unfold run_lengths_nat
    simp only [length_cons]
    let p := fun z => decide (z = x)
    have h_tw : (takeWhile p (x :: y :: tail)) = [x] := by
      dsimp [p]
      rw [takeWhile_cons]
      simp only [decide_true]
      rw [takeWhile_cons]
      have hy : decide (y = x) = false := by
        rw [decide_eq_false_iff_not]
        exact h_diff.symm
      rw [hy]
      rfl
    have h_dr : (drop (takeWhile p (x :: y :: tail)).length (x :: y :: tail)) = y :: tail := by
      rw [h_tw]
      rfl
    rw [h_dr]

theorem run_lengths_nat_append_different_ge (A B : List ℕ) (hA : A ≠ []) (hB : B ≠ []) (h_diff : A.getLast hA ≠ B.head hB) :
    (run_lengths_nat (A ++ B)).length ≥ (run_lengths_nat B).length + 1 := by
  rcases exists_concat_eq hA with ⟨A', x, rfl⟩
  have h_last : (A' ++ [x]).getLast (by simp) = x := List.getLast_append_singleton A'
  rw [h_last] at h_diff
  have h_assoc : (A' ++ [x]) ++ B = A' ++ (x :: B) := by simp
  rw [h_assoc]
  have h_mono := run_lengths_nat_length_le_append A' (x :: B)
  have h_diff_eq : (run_lengths_nat (x :: B)).length = (run_lengths_nat B).length + 1 := by
    apply run_lengths_nat_cons_different x B hB h_diff
  omega


theorem runs_R_step (i : ℕ) (hi : i ≥ 4) :
    (run_lengths_nat (run_lengths_nat (A381587_T i).reverse).reverse).length + 1 ≥
    (run_lengths_nat (run_lengths_nat (A381587_T (i - 1)).reverse).reverse).length := by
  have h_suf : A381587_T (i - 1) <:+ A381587_T i := by
    have h_eq : i = (i - 1) + 1 := by omega
    rw [h_eq]
    apply T_suffix_add_general (i - 1) 1 (by omega)
  have h_pref := IsSuffix.reverse_prefix h_suf
  have h_pref_rl := run_lengths_nat_prefix_dropLast h_pref
  have h_suf_rl := IsPrefix.reverse_suffix h_pref_rl
  have h_len_ge : (A381587_T (i - 1)).reverse.length ≥ 1 := by
    rw [length_reverse]
    apply A381587_T_length_ge_one
    omega
  have h_rl_ge : (run_lengths_nat (A381587_T (i - 1)).reverse).length ≥ 1 := by
    apply run_lengths_nat_length_ge_one
    exact h_len_ge
  have h_rev_drop := reverse_dropLast (run_lengths_nat (A381587_T (i - 1)).reverse) h_rl_ge
  rw [h_rev_drop] at h_suf_rl
  have h_mono_suf := run_lengths_nat_length_mono_suffix h_suf_rl
  have h_drop_le := run_lengths_nat_drop_one_le (run_lengths_nat (A381587_T (i - 1)).reverse).reverse (by
    rw [length_reverse]
    exact h_rl_ge
  )
  omega

theorem r_recurrence_ge (k : ℕ) (hk : k ≥ 3) :
    (run_lengths_nat (A381587_T (k + 3)).reverse).length ≥
    (run_lengths_nat (A381587_T (k + 2)).reverse).length + (run_lengths_nat (A381587_T k).reverse).length := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | _ | _ | _ | j
    · omega
    · omega
    · omega
    · -- k = 3
      rw [rl_rev_T_6, rl_rev_T_5, rl_rev_T_3]
      decide
    · -- k = 4
      rw [rl_rev_T_7, rl_rev_T_6, rl_rev_T_4]
      decide
    · -- k = 5
      rw [rl_rev_T_8, rl_rev_T_7, rl_rev_T_5]
      decide
    · -- k >= 6
      have h1 := ih (j + 4) (by omega) (by omega)
      have h_eq_j7 : j + 4 + 3 = j + 7 := by omega
      have h_eq_j6 : j + 4 + 2 = j + 6 := by omega
      rw [h_eq_j7, h_eq_j6] at h1
      
      have h2 := ih (j + 5) (by omega) (by omega)
      have h_eq_j8 : j + 5 + 3 = j + 8 := by omega
      have h_eq_j7_2 : j + 5 + 2 = j + 7 := by omega
      rw [h_eq_j8, h_eq_j7_2] at h2
      
      have h_rev_eq : (A381587_T (j + 9)).reverse = (A381587_T (j + 8)).reverse ++ (run_lengths_nat (A381587_T (j + 8)).reverse).reverse := by
        have h_eq1 : j + 9 = (j + 5) + 4 := by omega
        have h_eq2 : j + 8 = (j + 5) + 3 := by omega
        rw [h_eq1, h_eq2]
        change ((run_lengths_nat (A381587_T ((j + 5) + 3)).reverse) ++ A381587_T ((j + 5) + 3)).reverse = (A381587_T ((j + 5) + 3)).reverse ++ (run_lengths_nat (A381587_T ((j + 5) + 3)).reverse).reverse
        simp only [reverse_append]
      
      have h_append := run_lengths_nat_append_le (A381587_T (j + 8)).reverse (run_lengths_nat (A381587_T (j + 8)).reverse).reverse
      rw [← h_rev_eq] at h_append
      
      have h_R_ge : (run_lengths_nat (run_lengths_nat (A381587_T (j + 8)).reverse).reverse).length + 1 ≥ (run_lengths_nat (run_lengths_nat (A381587_T (j + 6)).reverse).reverse).length := by
        have h_suf : A381587_T (j + 6) <:+ A381587_T (j + 8) := by
          apply T_suffix_add_general (j + 6) 2 (by omega)
        have h_pref := IsSuffix.reverse_prefix h_suf
        have h_pref_rl := run_lengths_nat_prefix_dropLast h_pref
        have h_suf_rl := IsPrefix.reverse_suffix h_pref_rl
        have h_len_ge : (A381587_T (j + 6)).reverse.length ≥ 1 := by
          rw [length_reverse]
          apply A381587_T_length_ge_one
          omega
        have h_rl_ge : (run_lengths_nat (A381587_T (j + 6)).reverse).length ≥ 1 := by
          apply run_lengths_nat_length_ge_one
          exact h_len_ge
        have h_rev_drop := reverse_dropLast (run_lengths_nat (A381587_T (j + 6)).reverse) h_rl_ge
        rw [h_rev_drop] at h_suf_rl
        have h_mono_suf := run_lengths_nat_length_mono_suffix h_suf_rl
        have h_drop_le := run_lengths_nat_drop_one_le (run_lengths_nat (A381587_T (j + 6)).reverse).reverse (by
          rw [length_reverse]
          exact h_rl_ge
        )
        omega
      
      change (run_lengths_nat (A381587_T (j + 9)).reverse).length ≥ (run_lengths_nat (A381587_T (j + 8)).reverse).length + (run_lengths_nat (A381587_T (j + 6)).reverse).length
      omega

theorem r_ge_L (k : ℕ) (hk : k ≥ 3) : (run_lengths_nat (A381587_T (k + 2)).reverse).length ≥ (A381587_T k).length := by
  rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
  induction j with
  | zero =>
    have h3 : A381587_T 3 = [2] := rfl
    have h4 : A381587_T 4 = [1, 2] := by
      change run_lengths_nat (A381587_T 3).reverse ++ A381587_T 3 = _
      rw [h3]
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      rfl
    have h5 : A381587_T 5 = [1, 1, 1, 2] := by
      change run_lengths_nat (A381587_T 4).reverse ++ A381587_T 4 = _
      rw [h4]
      simp only [reverse_cons, reverse_nil, cons_append, nil_append]
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      rfl
    have h_rev : [1, 1, 1, 2].reverse = [2, 1, 1, 1] := rfl
    have h_rl : run_lengths_nat [2, 1, 1, 1] = [1, 3] := by
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      rfl
    rw [h3, h5, h_rev, h_rl]
    decide
  | succ j ih =>
    have h_eq_goal1 : 3 + (j + 1) + 2 = 3 + j + 3 := by omega
    have h_eq_goal2 : 3 + (j + 1) = 3 + j + 1 := by omega
    rw [h_eq_goal1, h_eq_goal2]
    have h_step := r_recurrence_ge (3 + j) (by omega)
    have h_L_rec : (A381587_T (3 + j + 1)).length = (run_lengths_nat (A381587_T (3 + j)).reverse).length + (A381587_T (3 + j)).length := by
      have h_eq1 : 3 + j + 1 = j + 4 := by omega
      have h_eq2 : 3 + j = j + 3 := by omega
      rw [h_eq1, h_eq2]
      exact A381587_T_length_recurrence j
    have ih_val : (run_lengths_nat (A381587_T (3 + j + 2)).reverse).length ≥ (A381587_T (3 + j)).length := ih (by omega)
    omega

theorem lemma2_base (k : ℕ) (hk : k ≥ 3) :
    (A381587_T (3 + k)).length ≥ 2 * (A381587_T k).length := by
  have h_eq : 3 + k = k + 3 := by omega
  rw [h_eq]
  have h_rec1 : (A381587_T (k + 3)).length = (run_lengths_nat (A381587_T (k + 2)).reverse).length + (A381587_T (k + 2)).length := by
    have h_eq1 : k + 3 = (k - 1) + 4 := by omega
    have h_eq2 : k + 2 = (k - 1) + 3 := by omega
    rw [h_eq1, h_eq2]
    exact A381587_T_length_recurrence (k - 1)
  have h_rec2 : (A381587_T (k + 2)).length = (run_lengths_nat (A381587_T (k + 1)).reverse).length + (A381587_T (k + 1)).length := by
    have h_eq1 : k + 2 = (k - 2) + 4 := by omega
    have h_eq2 : k + 1 = (k - 2) + 3 := by omega
    rw [h_eq1, h_eq2]
    exact A381587_T_length_recurrence (k - 2)
  have h_rec3 : (A381587_T (k + 1)).length = (run_lengths_nat (A381587_T k).reverse).length + (A381587_T k).length := by
    rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
    have h_eq1 : 3 + j + 1 = j + 4 := by omega
    have h_eq2 : 3 + j = j + 3 := by omega
    rw [h_eq1, h_eq2]
    exact A381587_T_length_recurrence j
  rw [h_rec1, h_rec2, h_rec3]
  have h_r_ge := r_ge_L k hk
  omega


theorem lemma2_base_strong (k : ℕ) (hk : k ≥ 7) :
    (A381587_T (k + 2)).length ≥ 2 * (A381587_T k).length := by
  have h_rec1 : (A381587_T (k + 2)).length = (run_lengths_nat (A381587_T (k + 1)).reverse).length + (A381587_T (k + 1)).length := by
    have h_eq1 : k + 2 = (k - 2) + 4 := by omega
    have h_eq2 : k + 1 = (k - 2) + 3 := by omega
    rw [h_eq1, h_eq2]
    exact A381587_T_length_recurrence (k - 2)
  have h_rec2 : (A381587_T (k + 1)).length = (run_lengths_nat (A381587_T k).reverse).length + (A381587_T k).length := by
    have h_eq1 : k + 1 = (k - 3) + 4 := by omega
    have h_eq2 : k = (k - 3) + 3 := by omega
    rw [h_eq1, h_eq2]
    exact A381587_T_length_recurrence (k - 3)
  have h_rec3 : (A381587_T k).length = (run_lengths_nat (A381587_T (k - 1)).reverse).length + (A381587_T (k - 1)).length := by
    have h_eq1 : k = (k - 4) + 4 := by omega
    have h_eq2 : k - 1 = (k - 4) + 3 := by omega
    nth_rw 1 [h_eq1]
    rw [h_eq2]
    exact A381587_T_length_recurrence (k - 4)
  have h_rec4 : (A381587_T (k - 1)).length = (run_lengths_nat (A381587_T (k - 2)).reverse).length + (A381587_T (k - 2)).length := by
    have h_eq1 : k - 1 = (k - 5) + 4 := by omega
    have h_eq2 : k - 2 = (k - 5) + 3 := by omega
    nth_rw 1 [h_eq1]
    rw [h_eq2]
    exact A381587_T_length_recurrence (k - 5)
  have h_rec5 : (A381587_T (k - 2)).length = (run_lengths_nat (A381587_T (k - 3)).reverse).length + (A381587_T (k - 3)).length := by
    have h_eq1 : k - 2 = (k - 6) + 4 := by omega
    have h_eq2 : k - 3 = (k - 6) + 3 := by omega
    nth_rw 1 [h_eq1]
    rw [h_eq2]
    exact A381587_T_length_recurrence (k - 6)

  have hr1 := r_recurrence_ge (k - 2) (by omega)
  have hr1_rec := r_recurrence_ge (k - 3) (by omega)
  have hr1_rec2 := r_recurrence_ge (k - 4) (by omega)

  have hr2 := r_ge_L k (by omega)
  have hr3 := r_ge_L (k - 1) (by omega)
  have hr4 := r_ge_L (k - 2) (by omega)
  have hr5 := r_ge_L (k - 3) (by omega)

  have h_eq_r1 : k - 2 + 3 = k + 1 := by omega
  have h_eq_r2 : k - 2 + 2 = k := by omega
  rw [h_eq_r1, h_eq_r2] at hr1

  have h_eq_r1_rec : k - 3 + 3 = k := by omega
  have h_eq_r2_rec : k - 3 + 2 = k - 1 := by omega
  rw [h_eq_r1_rec, h_eq_r2_rec] at hr1_rec

  have h_eq_r1_rec2 : k - 4 + 3 = k - 1 := by omega
  have h_eq_r2_rec2 : k - 4 + 2 = k - 2 := by omega
  rw [h_eq_r1_rec2, h_eq_r2_rec2] at hr1_rec2

  have h_eq_r3 : k - 1 + 2 = k + 1 := by omega
  rw [h_eq_r3] at hr3

  have h_eq_r4 : k - 2 + 2 = k := by omega
  rw [h_eq_r4] at hr4

  have h_eq_r5 : k - 3 + 2 = k - 1 := by omega
  rw [h_eq_r5] at hr5

  have hl1 := run_lengths_nat_length_le (A381587_T k).reverse
  have hl2 := run_lengths_nat_length_le (A381587_T (k - 1)).reverse
  have hl3 := run_lengths_nat_length_le (A381587_T (k - 2)).reverse
  have hl4 := run_lengths_nat_length_le (A381587_T (k - 3)).reverse

  rw [length_reverse] at hl1 hl2 hl3 hl4

  omega

theorem lemma3_helper (d k : ℕ) (hk : k ≥ 3) (hd : d ≥ 2) (ih : ∀ c < d, ∀ k, k ≥ 3 → (run_lengths_nat (A381587_T (3 + c + k)).reverse).length ≥ (A381587_T (3 + c)).length * (A381587_T k).length) :
    (run_lengths_nat (A381587_T (d + k)).reverse).length ≥ (run_lengths_nat (A381587_T d).reverse).length * (A381587_T k).length := by
  by_cases hd2 : d = 2
  · subst hd2
    have h_r2 : (run_lengths_nat (A381587_T 2).reverse).length = 1 := by
      change (run_lengths_nat [1]).length = 1
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      rfl
    rw [h_r2, one_mul]
    have h_eq_add : 2 + k = k + 2 := by omega
    rw [h_eq_add]
    exact r_ge_L k hk
  · have hd3 : d - 3 < d := by omega
    have ih3 := ih (d - 3) hd3 k hk
    have h_eq : 3 + (d - 3) = d := by omega
    rw [h_eq] at ih3
    have h_le : (run_lengths_nat (A381587_T d).reverse).length ≤ (A381587_T d).length := by
      have h := run_lengths_nat_length_le (A381587_T d).reverse
      rw [length_reverse] at h
      exact h
    have h_mul_le : (run_lengths_nat (A381587_T d).reverse).length * (A381587_T k).length ≤ (A381587_T d).length * (A381587_T k).length := Nat.mul_le_mul_right _ h_le
    omega

theorem lemma3 (d k : ℕ) (hk : k ≥ 3) :
    (run_lengths_nat (A381587_T (3 + d + k)).reverse).length ≥ (A381587_T (3 + d)).length * (A381587_T k).length := by
  induction d using Nat.strong_induction_on generalizing k with
  | h d ih =>
    rcases d with _ | d
    · -- d = 0
      have h_r_ge := r_ge_L k hk
      have h_L3 : (A381587_T 3).length = 1 := rfl
      rw [h_L3]
      simp only [one_mul]
      have h_mono : (run_lengths_nat (A381587_T (3 + 0 + k)).reverse).length ≥ (run_lengths_nat (A381587_T (k + 2)).reverse).length := by
        have h_eq : 3 + 0 + k = (k + 2) + 1 := by omega
        rw [h_eq]
        apply run_lengths_nat_length_mono
        apply IsSuffix.reverse_prefix
        exact T_suffix_add_general (k + 2) 1 (by omega)
      omega
    · rcases d with _ | d
      · -- d = 1
        rcases k with _ | _ | _ | _ | _ | j
        · omega
        · omega
        · omega
        · -- k = 3
          change (run_lengths_nat (A381587_T 7).reverse).length ≥ (A381587_T 4).length * (A381587_T 3).length
          rw [rl_rev_T_7, T_4, T_3]
          decide
        · -- k = 4
          change (run_lengths_nat (A381587_T 8).reverse).length ≥ (A381587_T 4).length * (A381587_T 4).length
          rw [rl_rev_T_8, T_4]
          decide
        · rcases j with _ | j
          · -- k = 5
            change (run_lengths_nat (A381587_T 9).reverse).length ≥ (A381587_T 4).length * (A381587_T 5).length
            have hT9 : A381587_T 9 = run_lengths_nat (A381587_T 8).reverse ++ A381587_T 8 := rfl
            rw [hT9]
            rw [rl_rev_T_8, T_8, T_5, T_4]
            repeat (unfold run_lengths_nat; simp)
          · -- k = j + 6 >= 6
            change (run_lengths_nat (A381587_T (3 + 1 + (j + 6))).reverse).length ≥ (A381587_T (3 + 1)).length * (A381587_T (j + 6)).length
            have h_rec : (run_lengths_nat (A381587_T (3 + 1 + (j + 6))).reverse).length ≥
                (run_lengths_nat (A381587_T (3 + (j + 6))).reverse).length + (run_lengths_nat (A381587_T (3 + (j + 4))).reverse).length := by
              have h_step := r_recurrence_ge (j + 7) (by omega)
              have h_eq1 : j + 7 + 3 = 3 + 1 + (j + 6) := by omega
              have h_eq2 : j + 7 + 2 = 3 + (j + 6) := by omega
              have h_eq3 : j + 7 = 3 + (j + 4) := by omega
              rw [← h_eq1, ← h_eq2, ← h_eq3]
              exact h_step
            have h_ge1 : (run_lengths_nat (A381587_T (3 + (j + 6))).reverse).length ≥ (A381587_T (j + 7)).length := by
              have h_eq : 3 + (j + 6) = (j + 7) + 2 := by omega
              rw [h_eq]
              exact r_ge_L (j + 7) (by omega)
            have h_ge2 : (run_lengths_nat (A381587_T (3 + (j + 4))).reverse).length ≥ (A381587_T (j + 5)).length := by
              have h_eq : 3 + (j + 4) = (j + 5) + 2 := by omega
              rw [h_eq]
              exact r_ge_L (j + 5) (by omega)
            have h_mono_r : (run_lengths_nat (A381587_T (j + 5)).reverse).length ≤ (run_lengths_nat (A381587_T (j + 6)).reverse).length := by
              apply run_lengths_nat_length_mono
              apply IsSuffix.reverse_prefix
              exact T_suffix_add_general (j + 5) 1 (by omega)
            have h_L6 : (A381587_T (j + 6)).length = (run_lengths_nat (A381587_T (j + 5)).reverse).length + (A381587_T (j + 5)).length := by
              have h_eq4 : j + 6 = (j + 2) + 4 := by omega
              have h_eq5 : j + 5 = (j + 2) + 3 := by omega
              rw [h_eq4, h_eq5]
              exact A381587_T_length_recurrence (j + 2)
            have h_L7 : (A381587_T (j + 7)).length = (run_lengths_nat (A381587_T (j + 6)).reverse).length + (A381587_T (j + 6)).length := by
              have h_eq4 : j + 7 = (j + 3) + 4 := by omega
              have h_eq5 : j + 6 = (j + 3) + 3 := by omega
              rw [h_eq4, h_eq5]
              exact A381587_T_length_recurrence (j + 3)
            have h_L4 : (A381587_T 4).length = 2 := by rw [T_4]; rfl
            rw [h_L4]
            omega
      · -- d >= 2
        change (run_lengths_nat (A381587_T (3 + (d + 2) + k)).reverse).length ≥ (A381587_T (3 + (d + 2))).length * (A381587_T k).length
        have h_rec_L : (A381587_T (3 + (d + 2))).length = (run_lengths_nat (A381587_T (d + 4)).reverse).length + (A381587_T (3 + d + 1)).length := by
          have h_eq1 : 3 + (d + 2) = (d + 1) + 4 := by omega
          have h_eq2 : 3 + d + 1 = (d + 1) + 3 := by omega
          have h_eq3 : d + 4 = (d + 1) + 3 := by omega
          rw [h_eq1, h_eq2, h_eq3]
          exact A381587_T_length_recurrence (d + 1)
        rw [h_rec_L]
        rw [add_mul]
        
        have h_step := r_recurrence_ge (3 + d + k - 1) (by omega)
        have h_eq3 : 3 + d + k - 1 + 3 = 3 + (d + 2) + k := by omega
        have h_eq4 : 3 + d + k - 1 + 2 = 3 + d + 1 + k := by omega
        have h_eq5 : 3 + d + k - 1 = d + 2 + k := by omega
        rw [h_eq3, h_eq4, h_eq5] at h_step
        
        have ih1 := ih (d + 1) (by omega) k hk
        have h_eq6 : 3 + (d + 1) = 3 + d + 1 := by omega
        rw [h_eq6] at ih1
        
        have h_helper := lemma3_helper (d + 2) k hk (by omega) ih
        omega

theorem lemma2 (m k : ℕ) (hm : m ≥ 3) (hk : k ≥ 3) :
    (A381587_T (m + k)).length ≥ A381358 m * (A381587_T k).length := by
  rcases Nat.exists_eq_add_of_le hm with ⟨d, rfl⟩
  induction d generalizing k with
  | zero =>
    rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
    induction j with
    | zero =>
      have h3 : A381587_T 3 = [2] := rfl
      have h6 : A381587_T 6 = [1, 3, 1, 1, 1, 2] := by
        change run_lengths_nat (A381587_T 5).reverse ++ A381587_T 5 = _
        have h4 : A381587_T 4 = [1, 2] := by
          change run_lengths_nat (A381587_T 3).reverse ++ A381587_T 3 = _
          rw [h3]
          unfold run_lengths_nat
          simp
          unfold run_lengths_nat
          rfl
        have h5 : A381587_T 5 = [1, 1, 1, 2] := by
          change run_lengths_nat (A381587_T 4).reverse ++ A381587_T 4 = _
          rw [h4]
          simp only [reverse_cons, reverse_nil, cons_append, nil_append]
          unfold run_lengths_nat
          simp
          unfold run_lengths_nat
          simp
          unfold run_lengths_nat
          rfl
        rw [h5]
        change run_lengths_nat [2, 1, 1, 1] ++ [1, 1, 1, 2] = _
        unfold run_lengths_nat
        simp
        unfold run_lengths_nat
        simp
        unfold run_lengths_nat
        rfl
      rw [h3, h6]
      decide
    | succ j ih =>
      exact lemma2_base (3 + j + 1) (by omega)
  | succ d ih =>
    have hn : 3 + d ≥ 3 := by omega
    have h_rec : A381358 (3 + d + 1) = (A381587_T (3 + d)).length + A381358 (3 + d) := A381358_recurrence_of_ge_three (3 + d) hn
    have h_eq_add : 3 + (d + 1) = 3 + d + 1 := by omega
    rw [h_eq_add]
    rw [h_rec]
    have h_eq1 : 3 + d + 1 + k = 3 + d + k + 1 := by omega
    rw [h_eq1]
    have h_rec_L : (A381587_T (3 + d + k + 1)).length = (run_lengths_nat (A381587_T (3 + d + k)).reverse).length + (A381587_T (3 + d + k)).length := by
      have h_eq2 : 3 + d + k + 1 = (d + k) + 4 := by omega
      have h_eq3 : 3 + d + k = (d + k) + 3 := by omega
      rw [h_eq2, h_eq3]
      exact A381587_T_length_recurrence (d + k)
    rw [h_rec_L]
    rw [add_mul]
    have ih_val := ih k hk
    have h_lem3 := lemma3 d k hk
    omega

theorem lemma1 (m : ℕ) (hm : m ≥ 3) :
    (A381587_T m).length + (A381587_T (m + 1)).length + (A381587_T (m + 2)).length ≥ A381358 m := by
  rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
  induction k with
  | zero =>
    have h3 : A381587_T 3 = [2] := rfl
    have h4 : A381587_T 4 = [1, 2] := by
      change run_lengths_nat (A381587_T 3).reverse ++ A381587_T 3 = [1, 2]
      rw [h3]
      simp only [reverse_cons, reverse_nil, nil_append]
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      rfl
    have h5 : A381587_T 5 = [1, 1, 1, 2] := by
      change run_lengths_nat (A381587_T 4).reverse ++ A381587_T 4 = [1, 1, 1, 2]
      rw [h4]
      simp only [reverse_cons, reverse_nil, cons_append, nil_append]
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      simp
      unfold run_lengths_nat
      rfl
    rw [h3, h4, h5]
    decide
  | succ k ih =>
    have hn : 3 + k ≥ 3 := by omega
    have h_rec : A381358 (3 + k + 1) = (A381587_T (3 + k)).length + A381358 (3 + k) := A381358_recurrence_of_ge_three (3 + k) hn
    have h_L : (A381587_T (3 + k + 3)).length ≥ 2 * (A381587_T (3 + k)).length := by
      have h_lem := lemma2_base (3 + k) (by omega)
      have h_eq : 3 + (3 + k) = 3 + k + 3 := by omega
      rw [h_eq] at h_lem
      exact h_lem
    have h_eq1 : 3 + (k + 1) = 3 + k + 1 := by omega
    have h_eq2 : 3 + (k + 1) + 1 = 3 + k + 2 := by omega
    have h_eq3 : 3 + (k + 1) + 2 = 3 + k + 3 := by omega
    rw [h_eq3, h_eq2, h_eq1]
    have ih_val : (A381587_T (3 + k)).length + (A381587_T (3 + k + 1)).length + (A381587_T (3 + k + 2)).length ≥ A381358 (3 + k) := ih hn
    omega

theorem sum_le_sum_map {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [map_cons, sum_cons]
    have h1 : f head ≤ g head := h head (by simp)
    have h2 : (tail.map f).sum ≤ (tail.map g).sum := by
      apply ih
      intro x hx
      exact h x (by simp [hx])
    omega

theorem A381358_supermult_ge_three (m n : ℕ) (hm : m ≥ 3) (hn : n ≥ 3) :
    A381358 (m + n) ≥ A381358 m * A381358 n := by
  let k := n - 3
  have h_n_eq : n = 3 + k := by omega
  rw [h_n_eq]
  rw [A381358_sum_formula m (3 + k) hm]
  rw [List.range_add]
  simp only [List.map_append, List.sum_append, List.map_map]
  change A381358 m + (((A381587_T m).length + ((A381587_T (m + 1)).length + ((A381587_T (m + 2)).length + 0))) +
      ((List.range k).map (fun j => (A381587_T (m + (3 + j))).length)).sum) ≥
    A381358 m * A381358 (3 + k)
  have h_range3 : List.range 3 = [0, 1, 2] := rfl
  rw [A381358_sum_formula 3 k (by decide)]
  have h3 : A381358 3 = 2 := rfl
  rw [h3]
  rw [Nat.mul_add]
  rw [← List.sum_map_mul_left]
  have h_sum_le : ((List.range k).map (fun j => A381358 m * (A381587_T (3 + j)).length)).sum ≤
      ((List.range k).map (fun j => (A381587_T (m + (3 + j))).length)).sum := by
    apply sum_le_sum_map
    intro j hj
    have h_ge : 3 + j ≥ 3 := by omega
    exact lemma2 m (3 + j) hm h_ge
  have hl1 : (A381587_T m).length + (A381587_T (m + 1)).length + (A381587_T (m + 2)).length ≥ A381358 m := lemma1 m hm
  omega

theorem A381358_supermult (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    A381358 (m + n) ≥ A381358 m * A381358 n := by
  by_cases hm3 : m < 3
  · exact A381358_supermult_base m n hm hn hm3
  · by_cases hn3 : n < 3
    · have h_eq1 : m + n = n + m := by omega
      have h_eq2 : A381358 m * A381358 n = A381358 n * A381358 m := by ring
      rw [h_eq1, h_eq2]
      exact A381358_supermult_base n m hn hm hn3
    · have hm_ge : m ≥ 3 := by omega
      have hn_ge : n ≥ 3 := by omega
      exact A381358_supermult_ge_three m n hm_ge hn_ge

noncomputable def s (n : ℕ) : ℝ := if n = 0 then 1 else (A381358 n : ℝ)

theorem s_pos (n : ℕ) : s n > 0 := by
  unfold s
  split_ifs with hn
  · linarith
  · have hn_ge : n ≥ 1 := Nat.pos_of_ne_zero hn
    have h := A381358_ge_one n hn_ge
    exact_mod_cast h

theorem s_le_two_pow (n : ℕ) : s n ≤ (2 : ℝ) ^ n := by
  unfold s
  split_ifs with hn
  · subst hn
    simp
  · have h : A381358 n ≤ 2 ^ n := A381358_le_two_pow n
    exact_mod_cast h

theorem s_supermult (m n : ℕ) : s (m + n) ≥ s m * s n := by
  by_cases hm : m = 0
  · subst hm
    simp [s]
  · by_cases hn : n = 0
    · subst hn
      simp [s]
    · have hmn : m + n ≠ 0 := by omega
      unfold s
      rw [if_neg hmn, if_neg hm, if_neg hn]
      have hm1 : m ≥ 1 := Nat.pos_of_ne_zero hm
      have hn1 : n ≥ 1 := Nat.pos_of_ne_zero hn
      have h := A381358_supermult m n hm1 hn1
      exact_mod_cast h

noncomputable def u (n : ℕ) : ℝ := - Real.log (s n)

theorem log_mul_le_log_add (m n : ℕ) :
    - Real.log (s (m + n)) ≤ - Real.log (s m) + - Real.log (s n) := by
  have h1 : Real.log (s (m + n)) ≥ Real.log (s m * s n) := by
    apply Real.log_le_log
    · exact mul_pos (s_pos m) (s_pos n)
    · exact s_supermult m n
  have h2 : Real.log (s m * s n) = Real.log (s m) + Real.log (s n) := by
    exact Real.log_mul (ne_of_gt (s_pos m)) (ne_of_gt (s_pos n))
  linarith

theorem u_subadditive : Subadditive u := by
  intro m n
  unfold u
  exact log_mul_le_log_add m n

theorem u_ge (n : ℕ) : u n ≥ - (n : ℝ) * Real.log 2 := by
  unfold u
  have h1 : s n ≤ (2 : ℝ) ^ n := s_le_two_pow n
  have h2 : Real.log (s n) ≤ Real.log ((2 : ℝ) ^ n) := by
    apply Real.log_le_log (s_pos n)
    exact h1
  rw [Real.log_pow] at h2
  linarith

theorem bdd_below_u_div_n : BddBelow (range (fun n => u n / (n : ℝ))) := by
  use - Real.log 2
  rintro x ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst hn
    unfold u s
    simp
    have : Real.log 2 ≥ 0 := Real.log_nonneg (by linarith)
    linarith
  · have h : u n ≥ - (n : ℝ) * Real.log 2 := u_ge n
    have hn_pos : (n : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h_div : u n / (n : ℝ) ≥ (- (n : ℝ) * Real.log 2) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right h (le_of_lt hn_pos)
    have h_cancel : (- (n : ℝ) * Real.log 2) / (n : ℝ) = - Real.log 2 := by
      rw [neg_mul, neg_div, mul_div_cancel_left₀ _ (ne_of_gt hn_pos)]
    linarith

theorem s_pow_one_div_eq_exp_neg_u_div_n (n : ℕ) (hn : n ≠ 0) :
    s n ^ ((n : ℝ) ⁻¹) = exp (- (u n / (n : ℝ))) := by
  unfold u
  have hn_pos : (n : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [rpow_def_of_pos (s_pos n)]
  congr 1
  field_simp

theorem s_limit_exists :
    ∃ L : ℝ, Tendsto (fun n : ℕ => s n ^ ((n : ℝ)⁻¹)) atTop (𝓝 L) := by
  have h_lim := Subadditive.tendsto_lim u_subadditive bdd_below_u_div_n
  have h_neg : Tendsto (fun n : ℕ => - (u n / (n : ℝ))) atTop (𝓝 (- u_subadditive.lim)) := by
    exact Tendsto.neg h_lim
  have h_exp : Tendsto (fun n : ℕ => exp (- (u n / (n : ℝ)))) atTop (𝓝 (exp (- u_subadditive.lim))) := by
    exact (continuous_exp.tendsto _).comp h_neg
  use exp (- u_subadditive.lim)
  refine (tendsto_congr' ?_).mpr h_exp
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_ne : n ≠ 0 := by omega
  exact s_pow_one_div_eq_exp_neg_u_div_n n hn_ne

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
by
  rcases s_limit_exists with ⟨L, hL⟩
  use L
  refine (tendsto_congr' ?_).mpr hL
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_ne : n ≠ 0 := by omega
  unfold s
  rw [if_neg hn_ne]
