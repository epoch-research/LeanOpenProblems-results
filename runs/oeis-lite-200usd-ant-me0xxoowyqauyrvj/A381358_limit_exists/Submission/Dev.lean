import FormalConjectures.Util.ProblemImports
open List Nat

/-- Computes the run lengths of a list of natural numbers. -/
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

def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

-- Foundational lemma: sum of run lengths = length.
-- First, understand takeWhile length and drop.

example : run_lengths_nat [2,2,1,1,3] = [2,2,1] := by native_decide

-- key: takeWhile length ≤ length, and is > 0 when list nonempty with matching head
theorem rl_sum (l : List ℕ) : (run_lengths_nat l).sum = l.length := by
  induction l using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 h t ih =>
    rename_i hIH
    rw [run_lengths_nat]
    simp only [List.sum_cons]
    rw [hIH, List.length_drop]
    have hle : (List.takeWhile (fun x => x = h) (h :: t)).length ≤ (h :: t).length :=
      (List.takeWhile_sublist _).length_le
    have heq : ih.length = (List.takeWhile (fun x => decide (x = h)) (h :: t)).length := rfl
    omega

noncomputable def Lseq (n : ℕ) : ℕ := (A381587_T n).length
noncomputable def Rseq (n : ℕ) : ℕ := (run_lengths_nat (A381587_T n)).length
noncomputable def Sseq (n : ℕ) : ℕ := (A381587_T n).sum

theorem A381358_eq_Sseq (n : ℕ) : A381358 n = Sseq n := rfl

theorem T_succ (k : ℕ) :
    A381587_T (k + 4) = run_lengths_nat (A381587_T (k+3)).reverse ++ A381587_T (k+3) := rfl

theorem rl_reverse_sum (l : List ℕ) : (run_lengths_nat l.reverse).sum = l.length := by
  rw [rl_sum]; exact l.length_reverse

theorem Sseq_succ (k : ℕ) : Sseq (k+4) = Lseq (k+3) + Sseq (k+3) := by
  unfold Sseq Lseq
  rw [T_succ, List.sum_append, rl_reverse_sum]
