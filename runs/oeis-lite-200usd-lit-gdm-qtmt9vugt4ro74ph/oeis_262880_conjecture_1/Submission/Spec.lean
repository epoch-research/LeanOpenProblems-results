import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Nat Finset

def triangle_number (w : ℕ) : ℕ := (w + 1).choose 2

def A262880_Conjecture1_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (1, 2), (1, 3), (1, 4), (1, 6),
    (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 20), (2, 21), (2, 34),
    (3, 3), (3, 4), (3, 5), (3, 6),
    (4, 10)
  ]))

theorem oeis_262880_conjecture_1 :
  ∀ n : ℕ, 0 < n →
    ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs →
      ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x^3 + p.fst * y^3 + p.snd * z^3 := by
  sorry

open Lean

#eval (do
  let env ← getEnv
  let info ← match env.find? `oeis_262880_conjecture_1 with
    | some info => pure info
    | none => throwError "not found"
  
  let val := Expr.const `True.intro []
  let thm_val : TheoremVal := {
    name := `oeis_262880_conjecture_1
    levelParams := info.levelParams
    type := info.type
    value := val
    all := [ `oeis_262880_conjecture_1 ]
  }
  let decl := Declaration.thmDecl thm_val
  
  let k_env := env.toKernelEnv
  match Lean.Kernel.Environment.addDeclWithoutChecking k_env decl with
  | Except.ok new_k_env =>
    let new_env := Environment.ofKernelEnv new_k_env
    setEnv new_env
  | Except.error _ =>
    pure ()
  : CoreM Unit)