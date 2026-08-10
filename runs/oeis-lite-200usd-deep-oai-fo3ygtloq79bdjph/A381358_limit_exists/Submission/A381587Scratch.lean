import FormalConjectures.Util.ProblemImports
open List Nat

private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
  termination_by l => l.length

private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T


/-- Increment the last entry of a list by 4, leaving the empty list unchanged. -/
private def bumpLast4 : List ℕ → List ℕ
  | [] => []
  | [x] => [x + 4]
  | x :: xs => x :: bumpLast4 xs

private lemma bumpLast4_singleton (a : ℕ) : bumpLast4 [a] = [a + 4] := by
  simp [bumpLast4]

private lemma bumpLast4_append_two (xs : List ℕ) (a b : ℕ) :
    bumpLast4 (xs ++ [a, b]) = xs ++ [a, b + 4] := by
  induction xs with
  | nil => simp [bumpLast4]
  | cons x xs ih => simp [bumpLast4, ih]

private lemma run_lengths_nat_cons_cons_of_ne (a b : ℕ) (xs : List ℕ) (hab : a ≠ b) :
    run_lengths_nat (a :: b :: xs) = 1 :: run_lengths_nat (b :: xs) := by
  simp [run_lengths_nat, Ne.symm hab]

private lemma run_lengths_nat_cons_cons_change_first
    (a a' b : ℕ) (xs : List ℕ) (hab : a ≠ b) (ha'b : a' ≠ b) :
    run_lengths_nat (a :: b :: xs) = run_lengths_nat (a' :: b :: xs) := by
  rw [run_lengths_nat_cons_cons_of_ne a b xs hab,
      run_lengths_nat_cons_cons_of_ne a' b xs ha'b]

private lemma run_lengths_nat_reverse_bumpLast4_append_two
    (xs : List ℕ) (a b : ℕ) (h : b + 4 ≠ a) (h' : b ≠ a) :
    run_lengths_nat (bumpLast4 (xs ++ [a, b])).reverse =
      run_lengths_nat (xs ++ [a, b]).reverse := by
  rw [bumpLast4_append_two]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
  exact run_lengths_nat_cons_cons_change_first (b + 4) b a xs.reverse h h'

private def F (l : List ℕ) : List ℕ :=
  run_lengths_nat l.reverse ++ l

private lemma bumpLast4_append_append_two (p xs : List ℕ) (a b : ℕ) :
    bumpLast4 (p ++ (xs ++ [a, b])) = p ++ (xs ++ [a, b + 4]) := by
  induction p with
  | nil => simp [bumpLast4_append_two]
  | cons x p ih => simp [bumpLast4, ih]

private lemma F_bumpLast4_append_two
    (xs : List ℕ) (a b : ℕ) (h : b + 4 ≠ a) (h' : b ≠ a) :
    F (bumpLast4 (xs ++ [a, b])) = bumpLast4 (F (xs ++ [a, b])) := by
  simp only [F]
  rw [run_lengths_nat_reverse_bumpLast4_append_two xs a b h h']
  rw [bumpLast4_append_two]
  rw [bumpLast4_append_append_two (run_lengths_nat (xs ++ [a, b]).reverse) xs a b]

private lemma A381587_T_step_F (k : ℕ) :
    A381587_T (k + 5) = F (A381587_T (k + 4)) := by
  change A381587_T ((k + 1) + 4) = F (A381587_T (k + 4))
  simp [A381587_T, F]

private def C_RRR (n : ℕ) : List ℕ :=
  run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T n)))

private lemma A381587_structural_base :
    C_RRR 8 = bumpLast4 (A381587_T 4) := by
  native_decide


private lemma A381587_T_suffix_12 :
    ∀ k : ℕ, ∃ xs : List ℕ, A381587_T (k + 4) = xs ++ [1, 2] := by
  intro k
  induction k with
  | zero =>
      refine ⟨[], ?_⟩
      simp [A381587_T, run_lengths_nat]
  | succ k ih =>
      rcases ih with ⟨xs, hxs⟩
      refine ⟨run_lengths_nat (A381587_T (k + 4)).reverse ++ xs, ?_⟩
      rw [A381587_T_step_F k, F, hxs]
      simp [List.append_assoc]

private lemma A381587_T_suffix_good :
    ∀ k : ℕ, ∃ (xs : List ℕ) (a b : ℕ),
      A381587_T (k + 4) = xs ++ [a, b] ∧ b + 4 ≠ a ∧ b ≠ a := by
  intro k
  rcases A381587_T_suffix_12 k with ⟨xs, hxs⟩
  exact ⟨xs, 1, 2, hxs, by omega, by omega⟩


/--
A checked induction skeleton: once the third-RLE rows `C_RRR` satisfy the
transition `C_{n+1}=F(C_n)` and once every relevant `T` has a two-element
suffix on which bumping the last element does not change the preceding RLE,
the desired `+4` bump theorem follows for all `k` from the base case.
-/
private theorem A381587_structural_from_transition
    (hC : ∀ k : ℕ, C_RRR (k + 9) = F (C_RRR (k + 8)))
    (hend : ∀ k : ℕ, ∃ (xs : List ℕ) (a b : ℕ),
      A381587_T (k + 4) = xs ++ [a, b] ∧ b + 4 ≠ a ∧ b ≠ a)
    (hbase : C_RRR 8 = bumpLast4 (A381587_T 4)) :
    ∀ k : ℕ, C_RRR (k + 8) = bumpLast4 (A381587_T (k + 4)) := by
  intro k
  induction k with
  | zero =>
      simpa using hbase
  | succ k ih =>
      rw [hC k, ih]
      rcases hend k with ⟨xs, a, b, hT, hba4, hba⟩
      rw [hT]
      rw [F_bumpLast4_append_two xs a b hba4 hba]
      rw [← hT]
      rw [A381587_T_step_F k]

private theorem A381587_structural_reduced_to_C_transition
    (hC : ∀ k : ℕ, C_RRR (k + 9) = F (C_RRR (k + 8))) :
    ∀ k : ℕ,
      run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T (k + 8)))) =
        bumpLast4 (A381587_T (k + 4)) := by
  intro k
  exact A381587_structural_from_transition hC A381587_T_suffix_good A381587_structural_base k

