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

private theorem exists_tendsto_root_of_submultiplicative
    (a : ℕ → ℕ) (hpos : ∀ n, 1 ≤ a n)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ ((n : ℝ)⁻¹)) Filter.atTop (nhds L) := by
  let u : ℕ → ℝ := fun n => Real.log (a n : ℝ)
  have hu : Subadditive u := by
    intro m n
    dsimp [u]
    have hposm : 0 < (a m : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hpos m))
    have hposn : 0 < (a n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hpos n))
    have hle : (a (m + n) : ℝ) ≤ (a m : ℝ) * (a n : ℝ) := by exact_mod_cast hsub m n
    calc
      Real.log (a (m + n) : ℝ) ≤ Real.log ((a m : ℝ) * (a n : ℝ)) :=
        Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hpos (m + n)))) hle
      _ = Real.log (a m : ℝ) + Real.log (a n : ℝ) := Real.log_mul hposm.ne' hposn.ne'
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / n) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hlognonneg : 0 ≤ u n := by
        dsimp [u]
        exact Real.log_nonneg (by exact_mod_cast hpos n)
      exact div_nonneg hlognonneg hnpos.le
  refine ⟨Real.exp hu.lim, ?_⟩
  have hlim : Filter.Tendsto (fun n : ℕ => u n / (n : ℝ)) Filter.atTop (nhds hu.lim) :=
    hu.tendsto_lim hbdd
  have hlim' : Filter.Tendsto (fun n : ℕ => Real.exp (u n / (n : ℝ))) Filter.atTop (nhds (Real.exp hu.lim)) := by
    simpa [Real.exp_eq_exp_ℝ] using hlim.exp
  refine hlim'.congr' ?_
  refine Filter.eventually_atTop.2 ⟨0, fun n _ => ?_⟩
  have hapos : 0 < (a n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hpos n))
  change Real.exp (u n / (n : ℝ)) = (a n : ℝ) ^ ((n : ℝ)⁻¹)
  rw [Real.rpow_def_of_pos hapos]
  congr 1

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
by sorry
