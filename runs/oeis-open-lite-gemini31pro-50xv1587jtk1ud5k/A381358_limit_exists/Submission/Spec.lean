import FormalConjectures.Util.ProblemImports
open List Nat

def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  sorry

theorem A381358_limit_exists.disproof : ¬ (type_of% @A381358_limit_exists) := by sorry
