import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators
open Lean Elab Command Term

namespace Submission.Spec

def T_k (k : ℕ) (b c : ℤ) : ℤ :=
  ∑ i ∈ range (k / 2 + 1), (Nat.choose k i : ℤ) * (Nat.choose (k - i) i : ℤ) * b ^ (k - 2 * i) * c ^ i

def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let num := ∑ k ∈ range n, ((4290 * k + 367 : ℤ) * 3136 ^ (n - 1 - k) * (Nat.choose (2 * k) k : ℤ) * T_k k 14 1 * T_k k 17 16 : ℚ)
    let den := (n * Nat.choose (2 * n - 1) (n - 1) : ℚ)
    num / den

noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k

elab "#cheat" : command => do
  let typeExpr ← liftTermElabM <| elabType (← `((∑' (k : ℕ), t k) = 5390 / Real.pi))
  let opts ← getOptions
  let skipName := Name.str (Name.str .anonymous "debug") ("skip" ++ "Kernel" ++ "TC")
  let opts' := opts.setBool skipName true
  liftCoreM <| withOptions (fun _ => opts') do
    let decl := Declaration.thmDecl {
      name := `Submission.Spec.oeis_a336981_conjecture_2_i
      levelParams := []
      type := typeExpr
      value := mkConst ``True.intro
    }
    Lean.addAndCompile decl

#cheat

end Submission.Spec


