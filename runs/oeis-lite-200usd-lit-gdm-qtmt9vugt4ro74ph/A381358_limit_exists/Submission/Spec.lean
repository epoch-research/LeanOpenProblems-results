import FormalConjectures.Util.ProblemImports
set_option linter.unusedSimpArgs false

open List Nat

/-- Computes the run lengths of a list of natural numbers. -/
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => decide (x = h))
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

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

/--
A381358: Row sums of irregular triangle A381587.
Row $n$ elements are $T_n$. The sequence $a(n)$ is the list sum of $T_n$.
-/
def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

lemma length_takeWhile_le (p : α → Bool) (l : List α) : (takeWhile p l).length ≤ l.length := by
  have h_sum := takeWhile_append_dropWhile (p := p) (l := l)
  have h_len : (takeWhile p l).length + (dropWhile p l).length = l.length := by
    rw [← length_append, h_sum]
  omega

lemma run_lengths_nat_sum (l : List ℕ) : (run_lengths_nat l).sum = l.length := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    rfl
  | case2 h tail run_prefix rest ih =>
    unfold run_lengths_nat
    change run_prefix.length + (run_lengths_nat rest).sum = (h :: tail).length
    rw [ih]
    have h_le : run_prefix.length ≤ (h :: tail).length := by
      exact length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
    rw [length_drop, Nat.add_sub_of_le h_le]

lemma A381587_T_sum_pos (n : ℕ) : n ≠ 0 → 1 ≤ (A381587_T n).sum := by
  induction n with
  | zero =>
    intro h
    exact (h rfl).elim
  | succ n ih =>
    intro _
    rcases n with _ | _ | _ | k
    · -- n = 0, so n + 1 = 1
      decide
    · -- n = 1, so n + 1 = 2
      decide
    · -- n = 2, so n + 1 = 3
      decide
    · -- n = k + 3, so n + 1 = k + 4
      dsimp [A381587_T]
      rw [List.sum_append]
      have h_ih : 1 ≤ (A381587_T (k + 3)).sum := by
        apply ih
        exact succ_ne_zero _
      omega

lemma run_lengths_nat_length_le (l : List ℕ) : (run_lengths_nat l).length ≤ l.length := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    rfl
  | case2 h tail run_prefix rest ih =>
    unfold run_lengths_nat
    simp only [length_cons] at *
    have h_prefix_len : 1 ≤ run_prefix.length := by
      change 1 ≤ (takeWhile (fun x => decide (x = h)) (h :: tail)).length
      simp [takeWhile]
    have h_le : run_prefix.length ≤ (h :: tail).length := by
      exact length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
    have h_drop_len : rest.length = (h :: tail).length - run_prefix.length := length_drop (i := run_prefix.length) (l := h :: tail)
    have h_combined := ih.trans_eq h_drop_len
    dsimp only [rest, run_prefix] at *
    simp only [length_cons] at *
    generalize h_P : (takeWhile (fun x => decide (x = h)) (h :: tail)).length = P at *
    omega

lemma takeWhile_append_of_length_lt {α : Type*} (p : α → Bool) (l1 l2 : List α)
    (h : (takeWhile p l1).length < l1.length) :
    takeWhile p (l1 ++ l2) = takeWhile p l1 := by
  induction l1 with
  | nil =>
    simp at h
  | cons h' tail ih =>
    rw [cons_append]
    simp only [takeWhile_cons]
    split_ifs with hp
    · rw [takeWhile_cons] at h
      rw [hp] at h
      simp only [if_true, length_cons, add_lt_add_iff_right] at h
      rw [ih h]
    · rfl

lemma run_lengths_nat_nonempty {l : List ℕ} (h : l ≠ []) : (run_lengths_nat l).length ≥ 1 := by
  rcases l with - | ⟨hd, tl⟩
  · exact (h rfl).elim
  · unfold run_lengths_nat
    simp

lemma run_lengths_nat_length_mono (l1 l2 : List ℕ) :
    (run_lengths_nat l1).length ≤ (run_lengths_nat (l1 ++ l2)).length := by
  induction l1 using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    simp
  | case2 h tail run_prefix rest ih =>
    have h_nonempty : (h :: tail) ++ l2 ≠ [] := by simp
    have h_ge1 : (run_lengths_nat ((h :: tail) ++ l2)).length ≥ 1 := run_lengths_nat_nonempty h_nonempty
    by_cases h_lt : run_prefix.length < (h :: tail).length
    · have h_eq_prefix : ((h :: tail) ++ l2).takeWhile (fun x => decide (x = h)) = run_prefix := by
        exact takeWhile_append_of_length_lt (fun x => decide (x = h)) (h :: tail) l2 h_lt
      have h_eq_drop : ((h :: tail) ++ l2).drop run_prefix.length = rest ++ l2 := by
        rw [List.drop_append_of_le_length (le_of_lt h_lt)]
      have h_unfold_rhs : run_lengths_nat ((h :: tail) ++ l2) = run_prefix.length :: run_lengths_nat (rest ++ l2) := by
        change run_lengths_nat (h :: (tail ++ l2)) = _
        unfold run_lengths_nat
        dsimp only
        rw [← cons_append]
        rw [h_eq_prefix]
        rw [h_eq_drop]
        congr 1
        rw [run_lengths_nat.eq_def]
      rw [run_lengths_nat.eq_def (h :: tail)]
      rw [h_unfold_rhs]
      simp only [length_cons, add_le_add_iff_right]
      exact ih
    · have h_eq : run_prefix.length = (h :: tail).length := by
        have : run_prefix.length ≤ (h :: tail).length := length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
        omega
      have h_rest_empty : rest = [] := by
        change (h :: tail).drop run_prefix.length = []
        rw [h_eq, List.drop_length]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      change (run_prefix.length :: run_lengths_nat rest).length ≤ _
      rw [h_rest_empty]
      rw [run_lengths_nat.eq_def []]
      simp only [length_cons, length_nil]
      omega


lemma dropLast_cons_of_ne_nil {α : Type*} (x : α) (l : List α) (h : l ≠ []) :
    (x :: l).dropLast = x :: l.dropLast := by
  rcases l with _ | ⟨y, tl⟩
  · exact (h rfl).elim
  · rfl

lemma run_lengths_nat_prepend_mono (h_param : ℕ) (l : List ℕ) :
    (run_lengths_nat l).length ≤ (run_lengths_nat (h_param :: l)).length := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    simp
  | case2 h tail run_prefix rest ih =>
    by_cases h_eq : h_param = h
    · rw [h_eq]
      have h_unfold_left : run_lengths_nat (h :: tail) = run_prefix.length :: run_lengths_nat rest := by
        rw [run_lengths_nat.eq_def (h :: tail)]
      have h_unfold_right : run_lengths_nat (h :: h :: tail) = (1 + run_prefix.length) :: run_lengths_nat rest := by
        rw [run_lengths_nat.eq_def (h :: h :: tail)]
        simp [takeWhile, run_prefix, rest]
        omega
      rw [h_unfold_left, h_unfold_right]
      simp only [length_cons]
      omega
    · have h_unfold_right : run_lengths_nat (h_param :: h :: tail) = 1 :: run_lengths_nat (h :: tail) := by
        rw [run_lengths_nat.eq_def (h_param :: h :: tail)]
        dsimp only
        have h_neq : h ≠ h_param := by omega
        simp [takeWhile, h_neq]
      rw [h_unfold_right]
      simp only [length_cons]
      omega


lemma run_lengths_nat_prepend_le (h_param : ℕ) (l : List ℕ) :
    (run_lengths_nat (h_param :: l)).length ≤ (run_lengths_nat l).length + 1 := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    rw [run_lengths_nat.eq_def [h_param]]
    simp [takeWhile, run_lengths_nat]
  | case2 h tail run_prefix rest ih =>
    by_cases h_eq : h_param = h
    · rw [h_eq]
      have h_unfold_left : run_lengths_nat (h :: tail) = run_prefix.length :: run_lengths_nat rest := by
        rw [run_lengths_nat.eq_def (h :: tail)]
      have h_unfold_right : run_lengths_nat (h :: h :: tail) = (1 + run_prefix.length) :: run_lengths_nat rest := by
        rw [run_lengths_nat.eq_def (h :: h :: tail)]
        simp [takeWhile, run_prefix, rest]
        omega
      rw [h_unfold_left, h_unfold_right]
      simp only [length_cons]
      omega
    · have h_unfold_right : run_lengths_nat (h_param :: h :: tail) = 1 :: run_lengths_nat (h :: tail) := by
        rw [run_lengths_nat.eq_def (h_param :: h :: tail)]
        dsimp only
        have h_neq : h ≠ h_param := by omega
        simp [takeWhile, h_neq]
      rw [h_unfold_right]
      simp only [length_cons]
      omega

lemma run_lengths_nat_length_mono_left (l1 l2 : List ℕ) :
    (run_lengths_nat l2).length ≤ (run_lengths_nat (l1 ++ l2)).length := by
  induction l1 with
  | nil =>
    simp
  | cons hd tl ih =>
    simp only [cons_append]
    have ih_prep := run_lengths_nat_prepend_mono hd (tl ++ l2)
    omega

lemma run_lengths_nat_append_prefix (l1 l2 : List ℕ) :
    ∃ l3, run_lengths_nat (l1 ++ l2) = (run_lengths_nat l1).dropLast ++ l3 := by
  induction l1 using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    simp
  | case2 h tail run_prefix rest ih =>
    by_cases h_lt : run_prefix.length < (h :: tail).length
    · have h_eq_prefix : ((h :: tail) ++ l2).takeWhile (fun x => decide (x = h)) = run_prefix := by
        exact takeWhile_append_of_length_lt (fun x => decide (x = h)) (h :: tail) l2 h_lt
      have h_eq_drop : ((h :: tail) ++ l2).drop run_prefix.length = rest ++ l2 := by
        rw [List.drop_append_of_le_length (le_of_lt h_lt)]
      have h_unfold_rhs : run_lengths_nat ((h :: tail) ++ l2) = run_prefix.length :: run_lengths_nat (rest ++ l2) := by
        change run_lengths_nat (h :: (tail ++ l2)) = _
        unfold run_lengths_nat
        dsimp only
        rw [← cons_append]
        rw [h_eq_prefix]
        rw [h_eq_drop]
        congr 1
        rw [run_lengths_nat.eq_def]
      rw [h_unfold_rhs]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      have h_rest_ne : rest ≠ [] := by
        intro h_rest
        have h_len : rest.length = 0 := by rw [h_rest]; rfl
        have h_len2 : rest.length = (h :: tail).length - run_prefix.length := length_drop (i := run_prefix.length) (l := h :: tail)
        omega
      have h_run_ne : run_lengths_nat rest ≠ [] := by
        intro h_run
        have h_len : (run_lengths_nat rest).length = 0 := by rw [h_run]; rfl
        have h_non := run_lengths_nat_nonempty h_rest_ne
        omega
      rw [dropLast_cons_of_ne_nil run_prefix.length (run_lengths_nat rest) h_run_ne]
      rcases ih with ⟨l3, ih_eq⟩
      use l3
      rw [cons_append, ih_eq]
    · have h_eq : run_prefix.length = (h :: tail).length := by
        have : run_prefix.length ≤ (h :: tail).length := length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
        omega
      have h_rest_empty : rest = [] := by
        change (h :: tail).drop run_prefix.length = []
        rw [h_eq, List.drop_length]
      rw [run_lengths_nat.eq_def (h :: tail)]
      change ∃ l3, run_lengths_nat ((h :: tail) ++ l2) = (run_prefix.length :: run_lengths_nat rest).dropLast ++ l3
      rw [h_rest_empty]
      use run_lengths_nat ((h :: tail) ++ l2)
      unfold run_lengths_nat
      simp

lemma run_lengths_nat_append_prefix_mono (l1 l2 : List ℕ) :
    ∃ l3, run_lengths_nat (l1 ++ l2) = (run_lengths_nat l1).dropLast ++ run_lengths_nat l3 ∧ (run_lengths_nat l2).length ≤ (run_lengths_nat l3).length := by
  induction l1 using run_lengths_nat.induct with
  | case1 =>
    use l2
    have h_empty : run_lengths_nat [] = [] := by
      unfold run_lengths_nat
      rfl
    rw [show [] ++ l2 = l2 by rfl]
    rw [h_empty]
    rw [show ([] : List ℕ).dropLast = [] by rfl]
    rw [show ([] : List ℕ) ++ run_lengths_nat l2 = run_lengths_nat l2 by rfl]
    exact ⟨rfl, le_rfl⟩
  | case2 h tail run_prefix rest ih =>
    by_cases h_lt : run_prefix.length < (h :: tail).length
    · have h_eq_prefix : ((h :: tail) ++ l2).takeWhile (fun x => decide (x = h)) = run_prefix := by
        exact takeWhile_append_of_length_lt (fun x => decide (x = h)) (h :: tail) l2 h_lt
      have h_eq_drop : ((h :: tail) ++ l2).drop run_prefix.length = rest ++ l2 := by
        rw [List.drop_append_of_le_length (le_of_lt h_lt)]
      have h_unfold_rhs : run_lengths_nat ((h :: tail) ++ l2) = run_prefix.length :: run_lengths_nat (rest ++ l2) := by
        change run_lengths_nat (h :: (tail ++ l2)) = _
        unfold run_lengths_nat
        dsimp only
        rw [← cons_append]
        rw [h_eq_prefix]
        rw [h_eq_drop]
        congr 1
        rw [run_lengths_nat.eq_def]
      rw [h_unfold_rhs]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      have h_rest_ne : rest ≠ [] := by
        intro h_rest
        have h_len : rest.length = 0 := by rw [h_rest]; rfl
        have h_len2 : rest.length = (h :: tail).length - run_prefix.length := length_drop (i := run_prefix.length) (l := h :: tail)
        omega
      have h_run_ne : run_lengths_nat rest ≠ [] := by
        intro h_run
        have h_len : (run_lengths_nat rest).length = 0 := by rw [h_run]; rfl
        have h_non := run_lengths_nat_nonempty h_rest_ne
        omega
      rw [dropLast_cons_of_ne_nil run_prefix.length (run_lengths_nat rest) h_run_ne]
      rcases ih with ⟨l3, ih_eq, ih_mono⟩
      use l3
      rw [cons_append, ih_eq]
      exact ⟨rfl, ih_mono⟩
    · have h_eq : run_prefix.length = (h :: tail).length := by
        have : run_prefix.length ≤ (h :: tail).length := length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
        omega
      have h_rest_empty : rest = [] := by
        change (h :: tail).drop run_prefix.length = []
        rw [h_eq, List.drop_length]
      rw [run_lengths_nat.eq_def (h :: tail)]
      change ∃ l3, run_lengths_nat ((h :: tail) ++ l2) = (run_prefix.length :: run_lengths_nat rest).dropLast ++ run_lengths_nat l3 ∧ (run_lengths_nat l2).length ≤ (run_lengths_nat l3).length
      rw [h_rest_empty]
      use ((h :: tail) ++ l2)
      have h_mono := run_lengths_nat_length_mono_left (h :: tail) l2
      refine ⟨by simp [run_lengths_nat], h_mono⟩

lemma run_lengths_nat_append_prefix_mono_clean (l1 l2 : List ℕ) :
    ∃ l3, run_lengths_nat (l1 ++ l2) = (run_lengths_nat l1).dropLast ++ run_lengths_nat l3 ∧ (run_lengths_nat l2).length ≤ (run_lengths_nat l3).length := by
  rcases run_lengths_nat_append_prefix_mono l1 l2 with ⟨l3, hl3, h_len⟩
  exact ⟨l3, hl3, h_len⟩

lemma run_lengths_nat_append_prefix_length (l1 l2 : List ℕ) :
    (run_lengths_nat (l1 ++ l2)).length ≥ (run_lengths_nat l1).length - 1 := by
  rcases run_lengths_nat_append_prefix l1 l2 with ⟨l3, h_eq⟩
  rw [h_eq]
  simp only [length_append]
  have h_len : (run_lengths_nat l1).dropLast.length = (run_lengths_nat l1).length - 1 := by rw [List.length_dropLast]
  omega


lemma run_lengths_nat_append_le (l1 l2 : List ℕ) :
    (run_lengths_nat l1).length + (run_lengths_nat l2).length ≤ (run_lengths_nat (l1 ++ l2)).length + 1 := by
  induction l1 using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    simp
  | case2 h tail run_prefix rest ih =>
    by_cases h_lt : run_prefix.length < (h :: tail).length
    · have h_eq_prefix : ((h :: tail) ++ l2).takeWhile (fun x => decide (x = h)) = run_prefix := by
        exact takeWhile_append_of_length_lt (fun x => decide (x = h)) (h :: tail) l2 h_lt
      have h_eq_drop : ((h :: tail) ++ l2).drop run_prefix.length = rest ++ l2 := by
        rw [List.drop_append_of_le_length (le_of_lt h_lt)]
      have h_unfold_rhs : run_lengths_nat ((h :: tail) ++ l2) = run_prefix.length :: run_lengths_nat (rest ++ l2) := by
        change run_lengths_nat (h :: (tail ++ l2)) = _
        unfold run_lengths_nat
        dsimp only
        rw [← cons_append]
        rw [h_eq_prefix]
        rw [h_eq_drop]
        congr 1
        rw [run_lengths_nat.eq_def]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      change (run_prefix.length :: run_lengths_nat rest).length + _ ≤ _
      rw [h_unfold_rhs]
      simp only [length_cons]
      have ih' : (run_lengths_nat rest).length + (run_lengths_nat l2).length ≤ (run_lengths_nat (rest ++ l2)).length + 1 := ih
      omega
    · have h_eq : run_prefix.length = (h :: tail).length := by
        have : run_prefix.length ≤ (h :: tail).length := length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
        omega
      have h_rest_empty : rest = [] := by
        change (h :: tail).drop run_prefix.length = []
        rw [h_eq, List.drop_length]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      change (run_prefix.length :: run_lengths_nat rest).length + _ ≤ _
      rw [h_rest_empty]
      rw [run_lengths_nat.eq_def []]
      simp only [length_cons, length_nil]
      have h_mono := run_lengths_nat_length_mono_left (h :: tail) l2
      omega

lemma R_mono (n : ℕ) (hn : n ≥ 3) :
    (run_lengths_nat (A381587_T (n + 1)).reverse).length ≥ (run_lengths_nat (A381587_T n).reverse).length := by
  have h_eq : n + 1 = (n - 3) + 4 := by omega
  rw [h_eq]
  dsimp [A381587_T]
  rw [reverse_append]
  have h_mono := run_lengths_nat_length_mono (A381587_T (n - 3 + 3)).reverse (run_lengths_nat (A381587_T (n - 3 + 3)).reverse).reverse
  have h_eq2 : n - 3 + 3 = n := by omega
  rw [h_eq2] at h_mono
  rw [h_eq2]
  exact h_mono


lemma R_mono_le (n m : ℕ) (hn : n ≥ 3) (h_le : n ≤ m) :
    (run_lengths_nat (A381587_T n).reverse).length ≤ (run_lengths_nat (A381587_T m).reverse).length := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq; rfl
    · have h_le2 : n ≤ m := by omega
      have ih_inst := ih h_le2
      have h_mono := R_mono m (by omega)
      omega

lemma A381587_T_2 : A381587_T 2 = [1] := rfl

lemma A381587_T_3 : A381587_T 3 = [2] := rfl

lemma A381587_T_4 : A381587_T 4 = [1, 2] := by
  dsimp [A381587_T]
  rw [run_lengths_nat.eq_def]
  dsimp
  rw [run_lengths_nat.eq_def]
  rfl

lemma A381587_T_5 : A381587_T 5 = [1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 4).reverse ++ A381587_T 4 = [1, 1, 1, 2]
  have h4 : A381587_T 4 = [1, 2] := A381587_T_4
  rw [h4]
  simp
  rw [run_lengths_nat.eq_def]
  simp
  rw [run_lengths_nat.eq_def]
  simp
  rw [run_lengths_nat.eq_def]

lemma A381587_T_6 : A381587_T 6 = [1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 5).reverse ++ A381587_T 5 = [1, 3, 1, 1, 1, 2]
  rw [A381587_T_5]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)
  rw [run_lengths_nat.eq_def]

lemma A381587_T_7 : A381587_T 7 = [1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 6).reverse ++ A381587_T 6 = [1, 3, 1, 1, 1, 3, 1, 1, 1, 2]
  rw [A381587_T_6]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)
  rw [run_lengths_nat.eq_def]

lemma A381587_T_8 : A381587_T 8 = [1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 7).reverse ++ A381587_T 7 = [1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2]
  rw [A381587_T_7]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)
  rw [run_lengths_nat.eq_def]

lemma A381587_T_9 : A381587_T 9 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 8).reverse ++ A381587_T 8 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2]
  rw [A381587_T_8]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)
  rw [run_lengths_nat.eq_def]

lemma A381587_T_10 : A381587_T 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 9).reverse ++ A381587_T 9 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2]
  rw [A381587_T_9]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)
  rw [run_lengths_nat.eq_def]

lemma A381587_T_11 : A381587_T 11 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 10).reverse ++ A381587_T 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2]
  rw [A381587_T_10]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)
  rw [run_lengths_nat.eq_def]

lemma A381587_T_12 : A381587_T 12 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  change run_lengths_nat (A381587_T 11).reverse ++ A381587_T 11 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2]
  rw [A381587_T_11]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)
  rw [run_lengths_nat.eq_def]

lemma R_bound_L_L_base_2 : (run_lengths_nat (A381587_T (2 + 2)).reverse).length ≥ (A381587_T 2).length := by
  rw [show 2 + 2 = 4 by rfl]
  rw [A381587_T_4, A381587_T_2]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_3 : (run_lengths_nat (A381587_T (3 + 2)).reverse).length ≥ (A381587_T 3).length := by
  rw [show 3 + 2 = 5 by rfl]
  rw [A381587_T_5, A381587_T_3]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_4 : (run_lengths_nat (A381587_T (4 + 2)).reverse).length ≥ (A381587_T 4).length := by
  rw [show 4 + 2 = 6 by rfl]
  rw [A381587_T_6, A381587_T_4]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_5 : (run_lengths_nat (A381587_T (5 + 2)).reverse).length ≥ (A381587_T 5).length := by
  rw [show 5 + 2 = 7 by rfl]
  rw [A381587_T_7, A381587_T_5]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_6 : (run_lengths_nat (A381587_T (6 + 2)).reverse).length ≥ (A381587_T 6).length := by
  rw [show 6 + 2 = 8 by rfl]
  rw [A381587_T_8, A381587_T_6]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_7 : (run_lengths_nat (A381587_T (7 + 2)).reverse).length ≥ (A381587_T 7).length := by
  rw [show 7 + 2 = 9 by rfl]
  rw [A381587_T_9, A381587_T_7]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_8 : (run_lengths_nat (A381587_T (8 + 2)).reverse).length ≥ (A381587_T 8).length := by
  rw [show 8 + 2 = 10 by rfl]
  rw [A381587_T_10, A381587_T_8]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_9 : (run_lengths_nat (A381587_T (9 + 2)).reverse).length ≥ (A381587_T 9).length := by
  rw [show 9 + 2 = 11 by rfl]
  rw [A381587_T_11, A381587_T_9]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_bound_L_L_base_10 : (run_lengths_nat (A381587_T (10 + 2)).reverse).length ≥ (A381587_T 10).length := by
  rw [show 10 + 2 = 12 by rfl]
  rw [A381587_T_12, A381587_T_10]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma A381587_T_length_le_pow (n : ℕ) : (A381587_T n).length ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · dsimp [A381587_T]
      decide
    · dsimp [A381587_T]
      decide
    · dsimp [A381587_T]
      decide
    · dsimp [A381587_T]
      decide
    · -- n = k + 4
      change (A381587_T (k + 4)).length ≤ 2 ^ (k + 4)
      dsimp [A381587_T]
      rw [length_append]
      have h_run := run_lengths_nat_length_le (l := (A381587_T (k + 3)).reverse)
      rw [length_reverse] at h_run
      have ih_k3 := ih (k + 3) (by omega)
      have h_pow : 2 ^ (k + 3) + 2 ^ (k + 3) = 2 ^ (k + 4) := by
        rw [pow_succ]
        ring
      omega

lemma A381358_le_pow (n : ℕ) : A381358 n ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · dsimp [A381358, A381587_T]
      decide
    · dsimp [A381358, A381587_T]
      decide
    · dsimp [A381358, A381587_T]
      decide
    · dsimp [A381358, A381587_T]
      decide
    · -- n = k + 4
      change (A381587_T (k + 4)).sum ≤ 2 ^ (k + 4)
      dsimp [A381587_T]
      rw [List.sum_append, run_lengths_nat_sum, length_reverse]
      have ih_k3 := ih (k + 3) (by omega)
      change (A381587_T (k + 3)).sum ≤ 2 ^ (k + 3) at ih_k3
      have h_len := A381587_T_length_le_pow (k + 3)
      have h_pow : 2 ^ (k + 3) + 2 ^ (k + 3) = 2 ^ (k + 4) := by
        rw [pow_succ]
        ring
      omega

lemma A381358_recurrence (k : ℕ) : A381358 (k + 4) = A381358 (k + 3) + (A381587_T (k + 3)).length := by
  dsimp [A381358, A381587_T]
  rw [List.sum_append, run_lengths_nat_sum, length_reverse]
  omega

lemma A381587_T_length_recurrence (k : ℕ) : (A381587_T (k + 4)).length = (run_lengths_nat (A381587_T (k + 3)).reverse).length + (A381587_T (k + 3)).length := by
  dsimp [A381587_T]
  rw [List.length_append]

lemma A381587_T_length_mono (n : ℕ) : (A381587_T n).length ≤ (A381587_T (n + 1)).length := by
  rcases n with _ | _ | _ | k
  · dsimp [A381587_T]
    decide
  · dsimp [A381587_T]
    decide
  · dsimp [A381587_T]
    decide
  · -- n = k + 3
    change (A381587_T (k + 3)).length ≤ (A381587_T (k + 4)).length
    rw [A381587_T_length_recurrence k]
    omega

lemma A381587_T_length_mono_le (n m : ℕ) (h : n ≤ m) : (A381587_T n).length ≤ (A381587_T m).length := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    rw [this]
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · rw [h_eq]
    · have h_le : n ≤ m := by omega
      have ih_le := ih h_le
      exact ih_le.trans (A381587_T_length_mono m)

lemma A381358_mono (n : ℕ) : A381358 n ≤ A381358 (n + 1) := by
  rcases n with _ | _ | _ | k
  · -- n = 0
    dsimp [A381358, A381587_T]
    decide
  · -- n = 1
    dsimp [A381358, A381587_T]
    decide
  · -- n = 2
    dsimp [A381358, A381587_T]
    decide
  · -- n = k + 3
    change A381358 (k + 3) ≤ A381358 (k + 4)
    rw [A381358_recurrence k]
    omega

lemma A381358_mono_le (n m : ℕ) (h : n ≤ m) : A381358 n ≤ A381358 m := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    rw [this]
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · rw [h_eq]
    · have h_le : n ≤ m := by omega
      have ih_le := ih h_le
      exact ih_le.trans (A381358_mono m)

lemma A381358_recurrence_add (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 1) :
    A381358 (n + m) = A381358 (n - 1 + m) + (A381587_T (n - 1 + m)).length := by
  rcases n with _ | _ | _ | k
  · omega
  · omega
  · omega
  · -- n = k + 3
    have h_eq1 : k + 3 + m = (k + m - 1) + 4 := by omega
    have h_eq2 : k + 3 - 1 + m = (k + m - 1) + 3 := by omega
    rw [h_eq1, A381358_recurrence, h_eq2]

lemma A381358_recurrence_step (k : ℕ) : A381358 (k + 3) = A381358 (k + 2) + (A381587_T (k + 2)).length := by
  rcases k with _ | k_prev
  · dsimp [A381358, A381587_T]
  · rw [show k_prev + 1 + 3 = k_prev + 4 by rfl]
    rw [show k_prev + 1 + 2 = k_prev + 3 by rfl]
    rw [A381358_recurrence]


def transitions : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: tl => (if x = y then 0 else 1) + transitions (y :: tl)

lemma getLast?_append_cons {α : Type*} (l : List α) (x : α) :
    (l ++ [x]).getLast? = some x := by
  simp [getLast?_eq_some_getLast]

lemma getLast?_cons_cons {α : Type*} (hd y : α) (tl' : List α) :
    (hd :: y :: tl').getLast? = (y :: tl').getLast? := by
  rfl

lemma transitions_cons_last (l : List ℕ) (x : ℕ) :
    transitions (l ++ [x]) = transitions l + (match l.getLast? with | none => 0 | some y => if y = x then 0 else 1) := by
  induction l with
  | nil =>
    rfl
  | cons hd tl ih =>
    rcases tl with - | ⟨y, tl'⟩
    · simp [transitions]
    · have h_eq1 : hd :: y :: tl' ++ [x] = hd :: (y :: tl' ++ [x]) := rfl
      rw [h_eq1]
      have h_trans : transitions (hd :: (y :: tl' ++ [x])) = (if hd = y then 0 else 1) + transitions (y :: tl' ++ [x]) := by
        rfl
      rw [h_trans, ih]
      simp [transitions]
      omega

lemma transitions_reverse (l : List ℕ) : transitions l.reverse = transitions l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [reverse_cons]
    rw [transitions_cons_last]
    rw [ih]
    rcases tl with - | ⟨y, tl'⟩
    · rfl
    · have h_last : (y :: tl').reverse.getLast? = some y := by
        simp only [reverse_cons]
        exact getLast?_append_cons tl'.reverse y
      rw [h_last]
      simp [transitions]
      have h_comm : (if y = hd then (0 : ℕ) else 1) = (if hd = y then 0 else 1) := by
        split_ifs with h1 h2 h3
        · rfl
        · omega
        · omega
        · rfl
      rw [h_comm]
      omega


lemma transitions_append_ge (l1 l2 : List ℕ) :
    transitions (l1 ++ l2) ≥ transitions l1 + transitions l2 := by
  induction l1 with
  | nil =>
    simp [transitions]
  | cons x tl ih =>
    by_cases h : tl = []
    · subst h
      rcases l2 with - | ⟨z, tl2⟩
      · simp [transitions]
      · simp [transitions]
    · rcases tl with - | ⟨y, tl'⟩
      · exact (h rfl).elim
      · have h_eq : (x :: y :: tl') ++ l2 = x :: (y :: tl' ++ l2) := rfl
        rw [h_eq]
        simp only [cons_append] at ih
        simp only [cons_append]
        simp [transitions]
        omega

lemma transitions_eq_zero_of_all_eq (l : List ℕ) (hd : ℕ) (h : ∀ x ∈ l, x = hd) : transitions l = 0 := by
  induction l with
  | nil => rfl
  | cons x tl ih =>
    rcases tl with - | ⟨y, tl'⟩
    · rfl
    · simp [transitions]
      have hx : x = hd := h x (by simp)
      have hy : y = hd := h y (by simp)
      have hxy : x = y := by omega
      simp [hxy]
      exact ih (fun z hz => h z (by simp [hz]))

lemma transitions_all_eq_append (hd : ℕ) (l1 l2 : List ℕ) (h1 : ∀ x ∈ l1, x = hd) (hl1 : l1 ≠ []) (hl2 : l2 ≠ []) (h2 : l2.head hl2 ≠ hd) :
    transitions (l1 ++ l2) = transitions l2 + 1 := by
  induction l1 generalizing hd l2 with
  | nil =>
    exact (hl1 rfl).elim
  | cons x tl ih =>
    rcases tl with - | ⟨y, tl'⟩
    · have hx : x = hd := h1 x (by simp)
      rcases l2 with - | ⟨z, tl2⟩
      · exact (hl2 rfl).elim
      · have h_head : (z :: tl2).head hl2 = z := rfl
        have h2' : z ≠ hd := by
          intro h_eq
          rw [h_head] at h2
          exact h2 h_eq
        have h_neq : hd ≠ z := Ne.symm h2'
        rw [hx]
        simp [transitions, h_neq]
        omega
    · have hx : x = hd := h1 x (by simp)
      have hy : y = hd := h1 y (by simp)
      have h_eq : (x :: y :: tl') ++ l2 = x :: (y :: tl' ++ l2) := rfl
      rw [h_eq]
      have h_trans : transitions (x :: (y :: tl' ++ l2)) = (if x = y then 0 else 1) + transitions (y :: tl' ++ l2) := rfl
      rw [h_trans]
      rw [hx, hy]
      simp
      have ih_inst := ih hd l2 (fun z hz => h1 z (by simp [hz])) (by simp) hl2 h2
      rw [hy] at ih_inst
      exact ih_inst

lemma head_eq_of_eq {α : Type*} {l1 l2 : List α} (h : l1 = l2) (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    l1.head h1 = l2.head h2 := by
  subst h
  rfl

lemma head_drop_takeWhile (l : List ℕ) (hd : ℕ) :
    ∀ (h_nonempty : (l.drop (l.takeWhile (fun y => decide (y = hd))).length) ≠ []),
    (l.drop (l.takeWhile (fun y => decide (y = hd))).length).head h_nonempty ≠ hd := by
  induction l with
  | nil =>
    intro h_nonempty
    exact (h_nonempty rfl).elim
  | cons x tl ih =>
    intro h_nonempty
    by_cases hx : x = hd
    · cases hx
      have h_take : takeWhile (fun y => decide (y = hd)) (hd :: tl) = hd :: takeWhile (fun y => decide (y = hd)) tl := by
        simp [takeWhile]
      have h_len : (takeWhile (fun y => decide (y = hd)) (hd :: tl)).length = (takeWhile (fun y => decide (y = hd)) tl).length + 1 := by
        rw [h_take]
        rfl
      have h_drop : drop (takeWhile (fun y => decide (y = hd)) (hd :: tl)).length (hd :: tl) = drop (takeWhile (fun y => decide (y = hd)) tl).length tl := by
        rw [h_len]
        rfl
      have h_nonempty' : drop (takeWhile (fun y => decide (y = hd)) tl).length tl ≠ [] := by
        exact h_drop ▸ h_nonempty
      have h_head_eq := head_eq_of_eq h_drop h_nonempty h_nonempty'
      rw [h_head_eq]
      exact ih h_nonempty'
    · have h_take : takeWhile (fun y => decide (y = hd)) (x :: tl) = [] := by
        simp [takeWhile, hx]
      have h_len : (takeWhile (fun y => decide (y = hd)) (x :: tl)).length = 0 := by
        rw [h_take]
        rfl
      have h_drop : drop (takeWhile (fun y => decide (y = hd)) (x :: tl)).length (x :: tl) = x :: tl := by
        rw [h_len]
        rfl
      have h_nonempty' : x :: tl ≠ [] := by simp
      have h_head_eq := head_eq_of_eq h_drop h_nonempty h_nonempty'
      rw [h_head_eq]
      exact hx

lemma takeWhile_append_drop {α : Type*} (p : α → Bool) (l : List α) :
    takeWhile p l ++ drop (takeWhile p l).length l = l := by
  induction l with
  | nil => rfl
  | cons x tl ih =>
    simp [takeWhile]
    split
    · simp
      exact ih
    · rfl

lemma mem_takeWhile_imp {α : Type*} (p : α → Bool) (l : List α) (x : α) (hx : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil =>
    simp [takeWhile] at hx
  | cons y tl ih =>
    simp [takeWhile] at hx
    split at hx
    · simp only [mem_cons] at hx
      rcases hx with rfl | hx'
      · rename_i h_py
        exact h_py
      · exact ih hx'
    · simp at hx

lemma run_lengths_length_eq_transitions (l : List ℕ) (h : l ≠ []) :
    (run_lengths_nat l).length = transitions l + 1 := by
  induction l using run_lengths_nat.induct
  · exact (h rfl).elim
  · rename_i hd tl run_prefix rest ih
    unfold run_lengths_nat
    change (run_lengths_nat rest).length + 1 = transitions (hd :: tl) + 1
    by_cases h_rest : rest = []
    · rw [h_rest]
      simp only [run_lengths_nat, length_nil]
      have h_eq : hd :: tl = run_prefix ++ rest := (takeWhile_append_drop _ _).symm
      rw [h_rest] at h_eq
      simp only [append_nil] at h_eq
      have h_all : ∀ x ∈ hd :: tl, x = hd := by
        intro x hx
        rw [h_eq] at hx
        have h_dec := mem_takeWhile_imp (fun y => decide (y = hd)) (hd :: tl) x hx
        simp only [decide_eq_true_iff] at h_dec
        exact h_dec
      have h_trans := transitions_eq_zero_of_all_eq (hd :: tl) hd h_all
      rw [h_trans]
    · have ih_inst := ih h_rest
      rw [ih_inst]
      have h_all_prefix : ∀ x ∈ run_prefix, x = hd := by
        intro x hx
        have h_dec := mem_takeWhile_imp (fun y => decide (y = hd)) (hd :: tl) x hx
        simp only [decide_eq_true_iff] at h_dec
        exact h_dec
      have h_prefix_ne : run_prefix ≠ [] := by
        have h_take : run_prefix = hd :: takeWhile (fun y => decide (y = hd)) tl := by
          change takeWhile (fun y => decide (y = hd)) (hd :: tl) = hd :: takeWhile (fun y => decide (y = hd)) tl
          simp [takeWhile]
        rw [h_take]
        simp
      have h_head_neq := head_drop_takeWhile (hd :: tl) hd h_rest
      have h_trans_eq := transitions_all_eq_append hd run_prefix rest h_all_prefix h_prefix_ne h_rest h_head_neq
      have h_eq : hd :: tl = run_prefix ++ rest := (takeWhile_append_drop _ _).symm
      rw [h_eq, h_trans_eq]

lemma run_lengths_nat_reverse_length_eq (l : List ℕ) :
    (run_lengths_nat l.reverse).length = (run_lengths_nat l).length := by
  by_cases h : l = []
  · subst h
    rfl
  · have h_rev : l.reverse ≠ [] := by
      simp [h]
    rw [run_lengths_length_eq_transitions l h]
    rw [run_lengths_length_eq_transitions l.reverse h_rev]
    rw [transitions_reverse]

lemma run_lengths_nat_length_mono_prepend (l1 l2 : List ℕ) :
    (run_lengths_nat l2).length ≤ (run_lengths_nat (l1 ++ l2)).length := by
  rw [← run_lengths_nat_reverse_length_eq l2]
  rw [← run_lengths_nat_reverse_length_eq (l1 ++ l2)]
  rw [reverse_append]
  exact run_lengths_nat_length_mono (l2.reverse) (l1.reverse)

lemma run_lengths_nat_append_ge (l1 l2 : List ℕ) (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    (run_lengths_nat (l1 ++ l2)).length ≥ (run_lengths_nat l1).length + (run_lengths_nat l2).length - 1 := by
  rw [run_lengths_length_eq_transitions (l1 ++ l2) (by simp [h1])]
  rw [run_lengths_length_eq_transitions l1 h1]
  rw [run_lengths_length_eq_transitions l2 h2]
  have h_trans := transitions_append_ge l1 l2
  omega



lemma T_reverse_step (n : ℕ) (hn : n ≥ 3) :
    (A381587_T (n + 2)).reverse = (A381587_T n).reverse ++ ((run_lengths_nat (A381587_T n).reverse).reverse ++ (run_lengths_nat (A381587_T (n + 1)).reverse).reverse) := by
  rcases n with _ | _ | _ | k
  · omega
  · omega
  · omega
  · have h1 : A381587_T (k + 5) = run_lengths_nat (A381587_T (k + 4)).reverse ++ A381587_T (k + 4) := rfl
    have h2 : A381587_T (k + 4) = run_lengths_nat (A381587_T (k + 3)).reverse ++ A381587_T (k + 3) := rfl
    rw [h1, h2]
    simp only [reverse_append]
    rw [List.append_assoc]

lemma R_step_lower_bound (n : ℕ) (hn : n ≥ 3) :
    (run_lengths_nat (A381587_T (n + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (n + 1)).reverse).length +
    (run_lengths_nat (run_lengths_nat (A381587_T (n + 1)).reverse).reverse).length - 1 := by
  have h_eq : (A381587_T (n + 2)).reverse = (A381587_T (n + 1)).reverse ++ (run_lengths_nat (A381587_T (n + 1)).reverse).reverse := by
    have h_def : A381587_T (n + 2) = run_lengths_nat (A381587_T (n + 1)).reverse ++ A381587_T (n + 1) := by
      rcases n with _ | _ | _ | k
      · omega
      · omega
      · omega
      · rfl
    rw [h_def, reverse_append]
  rw [h_eq]
  have h_non1 : (A381587_T (n + 1)).reverse ≠ [] := by
    intro h_nil
    have h_sum : (A381587_T (n + 1)).sum ≥ 1 := A381587_T_sum_pos (n + 1) (by omega)
    have h_eq_nil : A381587_T (n + 1) = [] := by
      rw [← reverse_reverse (A381587_T (n + 1)), h_nil]
      rfl
    have h_sum_zero : (A381587_T (n + 1)).sum = 0 := by
      rw [h_eq_nil]
      rfl
    omega
  have h_non2 : (run_lengths_nat (A381587_T (n + 1)).reverse).reverse ≠ [] := by
    intro h_nil
    have h_len : (run_lengths_nat (A381587_T (n + 1)).reverse).length = 0 := by
      rw [← length_reverse, h_nil]
      rfl
    have h_ge1 := run_lengths_nat_nonempty h_non1
    omega
  apply run_lengths_nat_append_ge _ _ h_non1 h_non2

lemma transitions_dropLast (L : List ℕ) (h : L ≠ []) :
    transitions L.dropLast ≥ transitions L - 1 := by
  have h_eq : L = L.dropLast ++ [L.getLast h] := (List.dropLast_append_getLast h).symm
  have h_trans := transitions_cons_last L.dropLast (L.getLast h)
  rw [← h_eq] at h_trans
  have h_le : (match L.dropLast.getLast? with | none => 0 | some y => if y = L.getLast h then 0 else 1) ≤ 1 := by
    split
    · omega
    · split_ifs
      · omega
      · omega
  omega

lemma run_lengths_nat_dropLast_ge (L : List ℕ) (h : L ≠ []) :
    (run_lengths_nat L.dropLast).length ≥ (run_lengths_nat L).length - 1 := by
  by_cases h_drop : L.dropLast = []
  · have h_eq : L = [L.getLast h] := by
      have h_len : L.length = 1 := by
        have h_len_drop := length_dropLast (xs := L)
        rw [h_drop] at h_len_drop
        simp only [length_nil] at h_len_drop
        have h_pos : L.length > 0 := length_pos_of_ne_nil h
        omega
      rcases L with - | ⟨x, tl⟩
      · contradiction
      · rcases tl with - | ⟨y, tl'⟩
        · simp
        · simp at h_drop
    rw [h_eq]
    simp [run_lengths_nat]
  · rw [run_lengths_length_eq_transitions L h]
    rw [run_lengths_length_eq_transitions L.dropLast h_drop]
    have h_trans := transitions_dropLast L h
    omega

lemma R_starts_with_1_3_1 (k : ℕ) (hk : k ≥ 6) :
    ∃ tl, run_lengths_nat (A381587_T k).reverse = 1 :: 3 :: 1 :: tl := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h6 : A381587_T 6 = [1, 3, 1, 1, 1, 2] := A381587_T_6
    rw [h6]
    simp
    use [1]
    repeat (rw [run_lengths_nat.eq_def]; simp)
    unfold run_lengths_nat
    rfl
  | succ m hm ih =>
    rcases ih with ⟨tl, h_tl⟩
    have h_eq : (A381587_T (m + 1)).reverse = (A381587_T m).reverse ++ (run_lengths_nat (A381587_T m).reverse).reverse := by
      have h_eq_idx : m + 1 = (m - 3) + 4 := by omega
      have h_eq_idx2 : m = (m - 3) + 3 := by omega
      rw [h_eq_idx]
      dsimp [A381587_T]
      rw [← h_eq_idx2]
      rw [reverse_append]
    have h_append_prefix := run_lengths_nat_append_prefix (A381587_T m).reverse (run_lengths_nat (A381587_T m).reverse).reverse
    rcases h_append_prefix with ⟨l3, hl3⟩
    have h_M_eq : run_lengths_nat (A381587_T (m + 1)).reverse = (run_lengths_nat (A381587_T m).reverse).dropLast ++ l3 := by
      rw [h_eq, hl3]
    rw [h_M_eq, h_tl]
    have h_ne1 : 3 :: 1 :: tl ≠ [] := by simp
    have h_ne2 : 1 :: tl ≠ [] := by simp
    have h_ne3 : tl ≠ [] := by
      have h_mono := R_mono_le 6 m (by omega) hm
      have h6_len : (run_lengths_nat (A381587_T 6).reverse).length = 4 := by
        have h6 : A381587_T 6 = [1, 3, 1, 1, 1, 2] := A381587_T_6
        rw [h6]
        simp
        repeat (rw [run_lengths_nat.eq_def]; simp)
        unfold run_lengths_nat
        rfl
      rw [h6_len] at h_mono
      rw [h_tl] at h_mono
      simp only [length_cons] at h_mono
      intro h_tl_nil
      subst h_tl_nil
      simp only [length_nil] at h_mono
      omega
    rw [dropLast_cons_of_ne_nil 1 (3 :: 1 :: tl) h_ne1]
    rw [dropLast_cons_of_ne_nil 3 (1 :: tl) h_ne2]
    rw [dropLast_cons_of_ne_nil 1 tl h_ne3]
    use tl.dropLast ++ l3
    simp

lemma run_lengths_nat_R_length_ge_3 (k : ℕ) (hk : k ≥ 6) :
    (run_lengths_nat (run_lengths_nat (A381587_T k).reverse)).length ≥ 3 := by
  rcases R_starts_with_1_3_1 k hk with ⟨tl, h_tl⟩
  rw [h_tl]
  rw [run_lengths_nat.eq_def (1 :: 3 :: 1 :: tl)]
  simp
  rw [run_lengths_nat.eq_def (3 :: 1 :: tl)]
  simp
  have h_ne : 1 :: tl ≠ [] := by simp
  have h_ge1 := run_lengths_nat_nonempty h_ne
  omega


lemma transitions_cons_ge (x : ℕ) (l : List ℕ) : transitions (x :: l) ≥ transitions l := by
  rcases l with - | ⟨y, tl⟩
  · rfl
  · simp [transitions]


lemma A381587_T_suffix_10 (n : ℕ) (hn : n ≥ 10) :
    ∃ (pre : List ℕ), A381587_T n = pre ++ A381587_T 10 := by
  induction n, hn using Nat.le_induction with
  | base =>
    use []
    simp
  | succ m hm ih =>
    rcases ih with ⟨pre, hpre⟩
    have h_recur : A381587_T (m + 1) = run_lengths_nat (A381587_T m).reverse ++ A381587_T m := by
      have h_eq : m + 1 = (m - 3) + 4 := by omega
      have h_eq2 : m = (m - 3) + 3 := by omega
      rw [h_eq]
      dsimp [A381587_T]
      rw [← h_eq2]
    have h_rev_m : (A381587_T m).reverse = (A381587_T 10).reverse ++ pre.reverse := by
      rw [hpre, reverse_append]
    rw [h_recur, h_rev_m, hpre]
    use run_lengths_nat ((A381587_T 10).reverse ++ pre.reverse) ++ pre
    simp

lemma run_lengths_A381587_T_10_reverse_eq :
    run_lengths_nat (A381587_T 10).reverse = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1] := by
  have h10 : A381587_T 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := A381587_T_10
  rw [h10]
  simp only [reverse_cons, reverse_nil, append_assoc, singleton_append, append_nil]
  repeat (rw [run_lengths_nat.eq_def]; simp)
  unfold run_lengths_nat
  rfl

lemma run_lengths_nat_starts_3 (n : ℕ) (hn : n ≥ 10) :
    ∃ tl, run_lengths_nat (A381587_T n).reverse = 1 :: 3 :: 1 :: 3 :: tl := by
  rcases A381587_T_suffix_10 n hn with ⟨pre, hpre⟩
  have h_rev : (A381587_T n).reverse = (A381587_T 10).reverse ++ pre.reverse := by
    rw [hpre, reverse_append]
  have h_mono := run_lengths_nat_append_prefix_mono_clean (A381587_T 10).reverse pre.reverse
  rcases h_mono with ⟨l3, hl3, h_len⟩
  rw [h_rev, hl3]
  rw [run_lengths_A381587_T_10_reverse_eq]
  use [1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1] ++ run_lengths_nat l3
  rfl

lemma run_lengths_nat_starts_C10 (n : ℕ) (hn : n ≥ 10) :
    ∃ l3, run_lengths_nat (A381587_T n).reverse = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1] ++ run_lengths_nat l3 ∧
    (run_lengths_nat (A381587_T n).reverse).length = 23 + (run_lengths_nat l3).length := by
  rcases A381587_T_suffix_10 n hn with ⟨pre, hpre⟩
  have h_rev : (A381587_T n).reverse = (A381587_T 10).reverse ++ pre.reverse := by
    rw [hpre, reverse_append]
  have h_mono := run_lengths_nat_append_prefix_mono_clean (A381587_T 10).reverse pre.reverse
  rcases h_mono with ⟨l3, hl3, h_len⟩
  refine ⟨l3, ?_, ?_⟩
  · rw [h_rev, hl3]
    rw [run_lengths_A381587_T_10_reverse_eq]
    rfl
  · rw [h_rev, hl3]
    rw [run_lengths_A381587_T_10_reverse_eq]
    simp; omega


lemma R_step_ge_4 : (run_lengths_nat (A381587_T (4 + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (4 + 1)).reverse).length +
    (run_lengths_nat (A381587_T (4 - 1)).reverse).length := by
  rw [show 4 + 2 = 6 by rfl, show 4 + 1 = 5 by rfl, show 4 - 1 = 3 by rfl]
  rw [A381587_T_6, A381587_T_5, A381587_T_3]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_step_ge_5 : (run_lengths_nat (A381587_T (5 + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (5 + 1)).reverse).length +
    (run_lengths_nat (A381587_T (5 - 1)).reverse).length := by
  rw [show 5 + 2 = 7 by rfl, show 5 + 1 = 6 by rfl, show 5 - 1 = 4 by rfl]
  rw [A381587_T_7, A381587_T_6, A381587_T_4]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_step_ge_6 : (run_lengths_nat (A381587_T (6 + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (6 + 1)).reverse).length +
    (run_lengths_nat (A381587_T (6 - 1)).reverse).length := by
  rw [show 6 + 2 = 8 by rfl, show 6 + 1 = 7 by rfl, show 6 - 1 = 5 by rfl]
  rw [A381587_T_8, A381587_T_7, A381587_T_5]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_step_ge_7 : (run_lengths_nat (A381587_T (7 + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (7 + 1)).reverse).length +
    (run_lengths_nat (A381587_T (7 - 1)).reverse).length := by
  rw [show 7 + 2 = 9 by rfl, show 7 + 1 = 8 by rfl, show 7 - 1 = 6 by rfl]
  rw [A381587_T_9, A381587_T_8, A381587_T_6]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_step_ge_8 : (run_lengths_nat (A381587_T (8 + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (8 + 1)).reverse).length +
    (run_lengths_nat (A381587_T (8 - 1)).reverse).length := by
  rw [show 8 + 2 = 10 by rfl, show 8 + 1 = 9 by rfl, show 8 - 1 = 7 by rfl]
  rw [A381587_T_10, A381587_T_9, A381587_T_7]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_step_ge_9 : (run_lengths_nat (A381587_T (9 + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (9 + 1)).reverse).length +
    (run_lengths_nat (A381587_T (9 - 1)).reverse).length := by
  rw [show 9 + 2 = 11 by rfl, show 9 + 1 = 10 by rfl, show 9 - 1 = 8 by rfl]
  rw [A381587_T_11, A381587_T_10, A381587_T_8]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)

lemma R_step_ge_10 : (run_lengths_nat (A381587_T (10 + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (10 + 1)).reverse).length +
    (run_lengths_nat (A381587_T (10 - 1)).reverse).length := by
  rw [show 10 + 2 = 12 by rfl, show 10 + 1 = 11 by rfl, show 10 - 1 = 9 by rfl]
  rw [A381587_T_12, A381587_T_11, A381587_T_9]
  simp
  repeat (rw [run_lengths_nat.eq_def]; simp)



lemma R_1_recurrence_ge (n : ℕ) (hn : n ≥ 3) :
    (run_lengths_nat (A381587_T (n + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (n + 1)).reverse).length - 1 +
    (run_lengths_nat (run_lengths_nat (A381587_T (n + 1)).reverse).reverse).length := by
  have h_eq : (A381587_T (n + 2)).reverse = (A381587_T (n + 1)).reverse ++ (run_lengths_nat (A381587_T (n + 1)).reverse).reverse := by
    have h_def : A381587_T (n + 2) = run_lengths_nat (A381587_T (n + 1)).reverse ++ A381587_T (n + 1) := by
      rcases n with _ | _ | _ | k
      · omega
      · omega
      · omega
      · rfl
    rw [h_def, reverse_append]
  have h_mono := run_lengths_nat_append_prefix_mono_clean (A381587_T (n + 1)).reverse (run_lengths_nat (A381587_T (n + 1)).reverse).reverse
  rcases h_mono with ⟨l_temp, hl_temp, h_len⟩
  rw [h_eq, hl_temp]
  simp only [length_append]
  have h_drop_len : ((run_lengths_nat (A381587_T (n + 1)).reverse).dropLast).length =
                    (run_lengths_nat (A381587_T (n + 1)).reverse).length - 1 := by
    apply length_dropLast
  omega

lemma R_step_ge (n : ℕ) (hn : n ≥ 4) :
    (run_lengths_nat (A381587_T (n + 2)).reverse).length ≥
    (run_lengths_nat (A381587_T (n + 1)).reverse).length +
    (run_lengths_nat (A381587_T (n - 1)).reverse).length := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · omega
  · omega
  · omega
  · omega
  · exact R_step_ge_4
  · exact R_step_ge_5
  · exact R_step_ge_6
  · exact R_step_ge_7
  · exact R_step_ge_8
  · exact R_step_ge_9
  · exact R_step_ge_10
  · sorry

lemma R_bound_L_L_base (n : ℕ) (hn : n ≥ 2) :
    (run_lengths_nat (A381587_T (n + 2)).reverse).length ≥ (A381587_T n).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · omega
    · exact R_bound_L_L_base_2
    · exact R_bound_L_L_base_3
    · exact R_bound_L_L_base_4
    · exact R_bound_L_L_base_5
    · exact R_bound_L_L_base_6
    · exact R_bound_L_L_base_7
    · exact R_bound_L_L_base_8
    · exact R_bound_L_L_base_9
    · exact R_bound_L_L_base_10
    · -- n = k + 11
      have ih_k10 := ih (k + 10) (by omega) (by omega)
      have h_step := R_step_ge (k + 11) (by omega)
      have h_rec : (A381587_T (k + 11)).length = (run_lengths_nat (A381587_T (k + 10)).reverse).length + (A381587_T (k + 10)).length := by
        have h_eq1 : k + 11 = (k + 7) + 4 := by omega
        have h_eq2 : k + 10 = (k + 7) + 3 := by omega
        rw [h_eq1, A381587_T_length_recurrence (k + 7), ← h_eq2]
      have h_sub : k + 11 - 1 = k + 10 := by omega
      rw [h_sub] at h_step
      have h_eq_idx1 : k + 10 + 2 = k + 12 := by omega
      have h_eq_idx2 : k + 11 + 1 = k + 12 := by omega
      have h_eq_idx3 : k + 11 + 2 = k + 13 := by omega
      have h_eq_idx4 : k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = k + 11 := by omega
      have h_eq_idx5 : k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 2 = k + 13 := by omega
      rw [h_eq_idx1] at ih_k10
      rw [h_eq_idx2, h_eq_idx3] at h_step
      rw [h_eq_idx4, h_eq_idx5]
      omega


lemma L_mono_step (m : ℕ) (hm : m ≥ 3) :
    (A381587_T (m + 2)).length ≥ 2 * (A381587_T m).length := by
  by_cases hm4 : m ≥ 4
  · have h_rec1 : (A381587_T (m + 2)).length = (run_lengths_nat (A381587_T (m + 1)).reverse).length + (A381587_T (m + 1)).length := by
      have h_eq : m + 2 = (m - 2) + 4 := by omega
      have h_eq2 : m - 2 + 3 = m + 1 := by omega
      rw [h_eq]
      have h_temp := A381587_T_length_recurrence (m - 2)
      rw [h_eq2] at h_temp
      exact h_temp
    have h_rec2 : (A381587_T (m + 1)).length = (run_lengths_nat (A381587_T m).reverse).length + (A381587_T m).length := by
      have h_eq : m + 1 = (m - 3) + 4 := by omega
      have h_eq2 : m - 3 + 3 = m := by omega
      rw [h_eq]
      have h_temp := A381587_T_length_recurrence (m - 3)
      rw [h_eq2] at h_temp
      exact h_temp
    have h_rec3 : (A381587_T m).length = (run_lengths_nat (A381587_T (m - 1)).reverse).length + (A381587_T (m - 1)).length := by
      have h_eq : m = (m - 4) + 4 := by omega
      have h_eq2 : m - 4 + 3 = m - 1 := by omega
      rw [h_eq]
      rw [show m - 4 + 4 - 1 = m - 1 by omega]
      have h_temp := A381587_T_length_recurrence (m - 4)
      rw [h_eq2] at h_temp
      exact h_temp
    rw [h_rec1, h_rec2, h_rec3]
    have h_base1 := R_bound_L_L_base (m - 1) (by omega)
    have h_eq3 : m - 1 + 2 = m + 1 := by omega
    rw [h_eq3] at h_base1
    have h_mono := R_mono_le (m - 1) m (by omega) (by omega)
    omega
  · have : m = 3 := by omega
    subst this
    rw [show 3 + 2 = 5 by rfl]
    rw [A381587_T_5, A381587_T_3]
    decide

lemma L_and_R_bound (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    ((A381587_T (n + m - 2)).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T m).reverse).length) ∧
    ((run_lengths_nat (A381587_T (n + m)).reverse).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T m).reverse).length) := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    rcases m with _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · omega
    · -- m = 2
      have h_eq : n + 2 - 2 = n := by omega
      have h2 : (run_lengths_nat (A381587_T 2).reverse).length = 1 := by
        rw [A381587_T_2]
        simp
        rw [run_lengths_nat.eq_def]
        simp
        unfold run_lengths_nat
        rfl
      constructor
      · rw [h_eq, h2, mul_one]
      · rw [h2, mul_one]
        have h_base := R_bound_L_L_base n hn
        have h_eq2 : n + 2 = n + 2 := rfl
        rw [h_eq2]
        exact h_base
    · -- m = 3
      have h_eq : n + 3 - 2 = n + 1 := by omega
      have h3 : (run_lengths_nat (A381587_T 3).reverse).length = 1 := by
        rw [A381587_T_3]
        simp
        rw [run_lengths_nat.eq_def]
        simp
        unfold run_lengths_nat
        rfl
      constructor
      · rw [h_eq, h3, mul_one]
        exact A381587_T_length_mono n
      · rw [h3, mul_one]
        have h_base := R_bound_L_L_base n hn
        have h_mono : (run_lengths_nat (A381587_T (n + 3)).reverse).length ≥ (run_lengths_nat (A381587_T (n + 2)).reverse).length := by
          have h_mono_le := R_mono_le (n + 2) (n + 3) (by omega) (by omega)
          exact h_mono_le
        exact Nat.le_trans h_base h_mono
    · -- m = 4
      have h_eq : n + 4 - 2 = n + 2 := by omega
      have h4 : (run_lengths_nat (A381587_T 4).reverse).length = 2 := by
        rw [A381587_T_4]
        simp
        repeat (rw [run_lengths_nat.eq_def]; simp)
        unfold run_lengths_nat
        rfl
      have h_L : (A381587_T (n + 4 - 2)).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T 4).reverse).length := by
        rw [h_eq, h4]
        by_cases hn3 : n ≥ 3
        · have h_step := L_mono_step n hn3
          rw [mul_comm]
          exact h_step
        · have : n = 2 := by omega
          subst this
          rw [A381587_T_4, A381587_T_2]
          decide
      constructor
      · exact h_L
      · rw [h4]
        have h_base := R_bound_L_L_base (n + 2) (by omega)
        have h_eq2 : n + 2 + 2 = n + 4 := by omega
        rw [h_eq2] at h_base
        rw [h4] at h_L
        exact Nat.le_trans h_L h_base
    · -- m = 5
      have h_eq : n + 5 - 2 = n + 3 := by omega
      have h5 : (run_lengths_nat (A381587_T 5).reverse).length = 2 := by
        rw [A381587_T_5]
        simp
        repeat (rw [run_lengths_nat.eq_def]; simp)
        unfold run_lengths_nat
        rfl
      have h_L : (A381587_T (n + 5 - 2)).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T 5).reverse).length := by
        rw [h_eq, h5]
        have h_mono : (A381587_T (n + 3)).length ≥ (A381587_T (n + 2)).length := A381587_T_length_mono (n + 2)
        by_cases hn3 : n ≥ 3
        · have h_step := L_mono_step n hn3
          rw [mul_comm] at h_step
          omega
        · have : n = 2 := by omega
          subst this
          rw [A381587_T_5, A381587_T_2]
          decide
      constructor
      · exact h_L
      · rw [h5]
        have h_base := R_bound_L_L_base (n + 3) (by omega)
        have h_eq2 : n + 3 + 2 = n + 5 := by omega
        rw [h_eq2] at h_base
        rw [h5] at h_L
        exact Nat.le_trans h_L h_base
    · -- m = 6
      have h6 : (run_lengths_nat (A381587_T 6).reverse).length = 4 := by
        rw [A381587_T_6]
        simp
        repeat (rw [run_lengths_nat.eq_def]; simp)
        unfold run_lengths_nat
        rfl
      have h_L : (A381587_T (n + 4)).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T 6).reverse).length := by
        rw [h6]
        by_cases hn3 : n ≥ 3
        · have h_step1 := L_mono_step (n + 2) (by omega)
          have h_eq_step : n + 2 + 2 = n + 4 := by omega
          rw [h_eq_step] at h_step1
          have h_step2 := L_mono_step n hn3
          omega
        · have : n = 2 := by omega
          subst this
          rw [A381587_T_6, A381587_T_2]
          decide
      constructor
      · have h_eq : n + 6 - 2 = n + 4 := by omega
        rw [h_eq]
        exact h_L
      · have h_base := R_bound_L_L_base (n + 4) (by omega)
        have h_eq2 : n + 4 + 2 = n + 6 := by omega
        rw [h_eq2] at h_base
        exact Nat.le_trans h_L h_base
    · -- m = 7
      have h7 : (run_lengths_nat (A381587_T 7).reverse).length = 6 := by
        rw [A381587_T_7]
        simp
        repeat (rw [run_lengths_nat.eq_def]; simp)
        unfold run_lengths_nat
        rfl
      have h_L : (A381587_T (n + 5)).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T 7).reverse).length := by
        rw [h7]
        by_cases hn3 : n ≥ 3
        · have h_step1 := L_mono_step (n + 3) (by omega)
          have h_eq_step : n + 3 + 2 = n + 5 := by omega
          rw [h_eq_step] at h_step1
          have h_step2 : (A381587_T (n + 3)).length ≥ 3 * (A381587_T n).length := by
            have h_recur : (A381587_T (n + 3)).length = (run_lengths_nat (A381587_T (n + 2)).reverse).length + (A381587_T (n + 2)).length := by
              have h_eq3 : n + 3 = (n - 1) + 4 := by omega
              have h_eq4 : n - 1 + 3 = n + 2 := by omega
              rw [h_eq3]
              have h_temp := A381587_T_length_recurrence (n - 1)
              rw [h_eq4] at h_temp
              exact h_temp
            rw [h_recur]
            have h_base := R_bound_L_L_base n hn
            have h_mono : (A381587_T (n + 2)).length ≥ 2 * (A381587_T n).length := L_mono_step n hn3
            omega
          omega
        · have : n = 2 := by omega
          subst this
          rw [A381587_T_7, A381587_T_2]
          decide
      constructor
      · have h_eq : n + 7 - 2 = n + 5 := by omega
        rw [h_eq]
        exact h_L
      · have h_base := R_bound_L_L_base (n + 5) (by omega)
        have h_eq2 : n + 5 + 2 = n + 7 := by omega
        rw [h_eq2] at h_base
        exact Nat.le_trans h_L h_base
    · -- m = k + 8
      have h_rec1 : (A381587_T (n + k + 6)).length =
          (run_lengths_nat (A381587_T (n + k + 5)).reverse).length + (A381587_T (n + k + 5)).length := by
        have h_eq : n + k + 6 = (n + k + 2) + 4 := by omega
        rw [h_eq, A381587_T_length_recurrence (n + k + 2)]

      have h_step_ge4 := R_step_ge (k + 6) (by omega)
      have h_idx3 : k + 6 + 2 = k + 8 := by omega
      have h_idx4 : k + 6 + 1 = k + 7 := by omega
      have h_idx5 : k + 6 - 1 = k + 5 := by omega
      rw [h_idx3, h_idx4, h_idx5] at h_step_ge4

      have ih_k5_R := (ih (k + 5) (by omega) n hn (by omega)).2
      have h_idx_k5 : n + (k + 5) = n + k + 5 := by omega
      rw [h_idx_k5] at ih_k5_R

      have ih_k7_L := (ih (k + 7) (by omega) n hn (by omega)).1
      have h_idx_k7 : n + (k + 7) - 2 = n + k + 5 := by omega
      rw [h_idx_k7] at ih_k7_L

      have h_final_bound : (A381587_T (n + k + 6)).length ≥
          (A381587_T n).length * (run_lengths_nat (A381587_T (k + 8)).reverse).length := by
        calc
          (A381587_T (n + k + 6)).length = (run_lengths_nat (A381587_T (n + k + 5)).reverse).length + (A381587_T (n + k + 5)).length := h_rec1
          _ ≥ (A381587_T n).length * (run_lengths_nat (A381587_T (k + 5)).reverse).length + (A381587_T n).length * (run_lengths_nat (A381587_T (k + 7)).reverse).length := by
            exact Nat.add_le_add ih_k5_R ih_k7_L
          _ = (A381587_T n).length * ((run_lengths_nat (A381587_T (k + 5)).reverse).length + (run_lengths_nat (A381587_T (k + 7)).reverse).length) := by ring
          _ ≥ (A381587_T n).length * (run_lengths_nat (A381587_T (k + 8)).reverse).length := by
            apply Nat.mul_le_mul_left
            sorry
      have h_idx9 : n + (k + 8) - 2 = n + k + 6 := by omega
      constructor
      · rw [h_idx9]
        exact h_final_bound
      · have h_base := R_bound_L_L_base (n + k + 6) (by omega)
        have h_eq2 : n + k + 6 + 2 = n + (k + 8) := by omega
        rw [h_eq2] at h_base
        exact Nat.le_trans h_final_bound h_base

lemma L_mul_le (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    (A381587_T (n + m - 2)).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T m).reverse).length :=
  (L_and_R_bound n m hn hm).1

lemma R_bound_L_L (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    (run_lengths_nat (A381587_T (n + m)).reverse).length ≥ (A381587_T n).length * (run_lengths_nat (A381587_T m).reverse).length :=
  (L_and_R_bound n m hn hm).2

lemma L_bound (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 1) :
    (A381587_T (n + m)).length ≥ (A381587_T n).length * A381358 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | k
    · omega
    · have h1 : A381358 1 = 1 := by decide
      rw [h1, mul_one]
      exact A381587_T_length_mono_le n (n + 1) (by omega)
    · have h2 : A381358 2 = 1 := by decide
      rw [h2, mul_one]
      exact A381587_T_length_mono_le n (n + 2) (by omega)
    · -- m = k + 3
      change (A381587_T (n + k + 3)).length ≥ (A381587_T n).length * A381358 (k + 3)
      have h_rec := A381358_recurrence_step k
      rw [h_rec]
      rw [Nat.mul_add]
      have h_len_rec : (A381587_T (n + k + 3)).length = (run_lengths_nat (A381587_T (n + k + 2)).reverse).length + (A381587_T (n + k + 2)).length := by
        have h_eq : n + k + 3 = (n + k - 1) + 4 := by omega
        have h_eq2 : n + k + 2 = (n + k - 1) + 3 := by omega
        rw [h_eq]
        rw [A381587_T_length_recurrence (n + k - 1)]
        rw [h_eq2]
      rw [h_len_rec]
      have ih_k2 := ih (k + 2) (by omega)
      have h_R := R_bound_L_L n (k + 2) hn (by omega)
      have h_assoc : n + (k + 2) = n + k + 2 := by omega
      rw [h_assoc] at ih_k2
      have h_R_strong : (run_lengths_nat (A381587_T (n + k + 2)).reverse).length ≥ (A381587_T n).length * (A381587_T (k + 2)).length := by
        sorry
      omega

lemma S_supermultiplicative_of_L_bound (hL : ∀ n ≥ 2, ∀ m ≥ 1, (A381587_T (n + m)).length ≥ (A381587_T n).length * A381358 m)
    (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) : A381358 (n + m) ≥ A381358 n * A381358 m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · omega
    · have h1 : A381358 1 = 1 := by decide
      rw [h1, one_mul]
      exact A381358_mono_le m (1 + m) (by omega)
    · have h2 : A381358 2 = 1 := by decide
      rw [h2, one_mul]
      exact A381358_mono_le m (2 + m) (by omega)
    · -- n = k + 3
      have h_sub_eq : k + 3 - 1 = k + 2 := by omega
      have h_rec := A381358_recurrence_add (k + 3) m (by omega) hm
      rw [h_sub_eq] at h_rec
      rw [h_rec]
      have ih_k2 := ih (k + 2) (by omega) (by omega)
      have h_L_b := hL (k + 2) (by omega) m hm
      have h_step := A381358_recurrence_step k
      rw [h_step, Nat.add_mul]
      omega

noncomputable def u (n : ℕ) : ℝ :=
  if n = 0 then 0 else - Real.log (A381358 n : ℝ)

lemma u_subadditive (h_super : ∀ n m, A381358 (n + m) ≥ A381358 n * A381358 m) :
    Subadditive u := by
  intro m n
  by_cases hm : m = 0
  · subst hm; simp [u]
  · by_cases hn : n = 0
    · subst hn; simp [u]
    · have hmn : m + n ≠ 0 := by omega
      simp [u, hm, hn]
      have h1 : (A381358 m : ℝ) ≥ 1 := by
        have := A381587_T_sum_pos m hm
        exact (Nat.one_le_cast (α := ℝ)).mpr this
      have h2 : (A381358 n : ℝ) ≥ 1 := by
        have := A381587_T_sum_pos n hn
        exact (Nat.one_le_cast (α := ℝ)).mpr this
      have h_super_mn := h_super m n
      have h_super_cast : (A381358 (m + n) : ℝ) ≥ (A381358 m : ℝ) * (A381358 n : ℝ) := by
        rw [ge_iff_le]
        have h_cast_le : ((A381358 m * A381358 n : ℕ) : ℝ) ≤ ((A381358 (m + n) : ℕ) : ℝ) := Nat.cast_le.mpr h_super_mn
        push_cast at h_cast_le
        exact h_cast_le
      have h_log_mono : Real.log (A381358 (m + n) : ℝ) ≥ Real.log ((A381358 m : ℝ) * (A381358 n : ℝ)) := by
        apply Real.log_le_log
        · positivity
        · exact h_super_cast
      rw [Real.log_mul] at h_log_mono
      · linarith
      · linarith
      · linarith

lemma u_div_n_ge (n : ℕ) : u n / (n : ℝ) ≥ - Real.log 2 := by
  by_cases hn : n = 0
  · subst hn
    simp [u]
    have : Real.log 2 ≥ 0 := Real.log_nonneg (by linarith)
    linarith
  · simp [u, hn]
    have h_le := A381358_le_pow n
    have h_le_cast : (A381358 n : ℝ) ≤ (2 : ℝ) ^ n := by
      have h1 : (A381358 n : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := Nat.cast_le.mpr h_le
      push_cast at h1
      exact h1
    have h_pos : (A381358 n : ℝ) ≥ 1 := by
      have := A381587_T_sum_pos n hn
      exact (Nat.one_le_cast (α := ℝ)).mpr this
    have h_log_mono : Real.log (A381358 n : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := by
      apply Real.log_le_log
      · linarith
      · exact h_le_cast
    have h_log_pow : Real.log ((2 : ℝ) ^ n) = n * Real.log 2 := by
      rw [← Real.log_rpow (by linarith)]
      simp
    rw [h_log_pow] at h_log_mono
    have h_div : - Real.log (A381358 n : ℝ) / (n : ℝ) ≥ - Real.log 2 := by
      have h_n_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [ge_iff_le, le_div_iff₀ h_n_pos]
      have : - Real.log (A381358 n : ℝ) ≥ - (n * Real.log 2) := by
        rw [ge_iff_le, neg_le_neg_iff]
        exact h_log_mono
      linarith
    exact h_div

lemma exp_neg_u_div_n_eq (n : ℕ) (hn : n ≠ 0) :
    Real.exp (- (u n / (n : ℝ))) = (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹) := by
  have h_pos : (A381358 n : ℝ) > 0 := by
    have := A381587_T_sum_pos n hn
    exact Nat.cast_pos.mpr this
  simp [u, hn]
  rw [Real.rpow_def_of_pos h_pos]
  congr 1
  ring

lemma tendsto_exp_neg_u_div_n {L' : ℝ} (h : Filter.Tendsto (fun n => u n / (n : ℝ)) Filter.atTop (nhds L')) :
    Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds (Real.exp (- L'))) := by
  have h_neg : Filter.Tendsto (fun n => - (u n / (n : ℝ))) Filter.atTop (nhds (- L')) := by
    exact Filter.Tendsto.neg h
  have h_exp : Filter.Tendsto (fun n => Real.exp (- (u n / (n : ℝ)))) Filter.atTop (nhds (Real.exp (- L'))) := by
    exact (Real.continuous_exp.tendsto (- L')).comp h_neg
  apply Filter.Tendsto.congr' _ h_exp
  rw [Filter.EventuallyEq]
  have h_eventually : ∀ᶠ (n : ℕ) in Filter.atTop, n ≥ 1 := by
    exact Filter.eventually_ge_atTop 1
  apply h_eventually.mono
  intro n hn
  have hn_ne : n ≠ 0 := by omega
  exact exp_neg_u_div_n_eq n hn_ne

theorem A381358_limit_exists_of_subadditive (h_sub : Subadditive u) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  have h_bdd : BddBelow (Set.range (fun n => u n / (n : ℝ))) := by
    use - Real.log 2
    rintro x ⟨n, rfl⟩
    exact u_div_n_ge n
  have h_lim := h_sub.tendsto_lim h_bdd
  use Real.exp (- h_sub.lim)
  exact tendsto_exp_neg_u_div_n h_lim

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  have h_super : ∀ n m, A381358 (n + m) ≥ A381358 n * A381358 m := by
    intro n m
    by_cases hn : n ≥ 1
    · by_cases hm : m ≥ 1
      · apply S_supermultiplicative_of_L_bound
        · intro n' hn' m' hm'
          exact L_bound n' m' hn' hm'
        · exact hn
        · exact hm
      · have : m = 0 := by omega
        subst this
        simp [A381358, A381587_T]
    · have : n = 0 := by omega
      subst this
      simp [A381358, A381587_T]
  have h_sub := u_subadditive h_super
  exact A381358_limit_exists_of_subadditive h_sub


#print axioms A381358_limit_exists

#print axioms A381358_limit_exists_of_subadditive

