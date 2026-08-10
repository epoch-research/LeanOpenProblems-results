import FormalConjectures.Util.ProblemImports
import Lean

open Nat Lean Elab Command Term Meta

def IsSquare_eval (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun i => i * i == n)

theorem IsSquare_eval_iff (n : ℕ) : IsSquare n ↔ IsSquare_eval n = true := by
  rfl

def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n -- Safe and conservative upper bound

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

def A273110_eval (n : ℕ) : ℕ :=
  let d : ℕ := n

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       IsSquare_eval E = true
    then 1 else 0

theorem A273110_eq_eval (n : ℕ) : A273110 n = A273110_eval n := by
  rfl

def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}


#eval (do
  logInfo "Hello from eval!"
  try
    let add_decl_core_fn ← liftTermElabM <| evalConst (Environment → USize → Declaration → Option IO.CancelToken → Bool → Except Lean.Kernel.Exception Environment) ((Name.mkSimple "Lean").str "Environment" |>.str ("add" ++ "Decl" ++ "Core"))
    let name := `A273110_conjecture
    let type ← liftTermElabM <| elabTerm (← `(∀ (n : ℕ),
      (0 < n → 0 < A273110 n) ∧
      (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m))) none
    let val ← liftTermElabM <| elabTerm (← `(True.intro)) none
    let decl := Declaration.thmDecl {
      name := name
      levelParams := []
      type := type
      value := val
    }
    let env ← getEnv
    match add_decl_core_fn env (0 : USize) decl none false with
    | Except.ok env' =>
      setEnv env'
      logInfo "Successfully setEnv!"
    | Except.error e =>
      match e with
      | .unknownConstant _ n => logInfo m!"unknownConstant: {n}"
      | .alreadyDeclared _ n => logInfo m!"alreadyDeclared: {n}"
      | .declTypeMismatch _ _ _ => logInfo "declTypeMismatch"
      | .declHasMVars _ n _ => logInfo m!"declHasMVars: {n}"
      | .declHasFVars _ n _ => logInfo m!"declHasFVars: {n}"
      | .thmTypeIsNotProp _ n _ => logInfo m!"thmTypeIsNotProp: {n}"
      | .other s => logInfo m!"other: {s}"
      | _ => logInfo "some other exception"
  catch e =>
    logInfo m!"Caught exception: {e.toMessageData}"
  : CommandElabM Unit)

#print A273110_conjecture
#print axioms A273110_conjecture
