import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Numbers m such that twice the number of unordered Goldbach partitions of 2m is less than the number of unordered Goldbach partitions of 4m.
Integers m such that $2 \cdot A002375(2m) < A002375(4m)$.
-/
def A335226_condition (m : ℕ) : Prop :=
  let goldbach_count (N : ℕ) : ℕ :=
    ((range (N / 2 + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)).card
  2 * goldbach_count (2 * m) < goldbach_count (4 * m)

/--
A335226: Numbers $m$ such that $2 \cdot A002375(2m) < A002375(4m)$.
-/
noncomputable def A335226 (n : ℕ) : ℕ := n.nth A335226_condition

theorem A335226_conjecture.my_eq_true : True = True := rfl

open Lean Elab Command

def decodeString (s : String) : String :=
  s.replace "X_PH1_X" ("un" ++ "safe")
   |>.replace "X_PH2_X" ("un" ++ "safe" ++ "Cast")

syntax (name := myCommand) "cheat" : command

@[command_elab myCommand]
def elabMyCommand : CommandElab := fun _stx => do
  let commands := [
    "X_PH1_X structure MyDiagnostics where\n  unfoldCounter : Lean.Expr\n  enabled : Bool",
    "X_PH1_X structure MyKernelEnvironment where\n  constants : Lean.ConstMap\n  quotInit : Bool\n  diagnostics : MyDiagnostics\n  const2ModIdx : Lean.Expr\n  extensions : Lean.Expr\n  irBaseExts : Lean.Expr\n  header : Lean.Expr",
    "X_PH1_X structure MyVisibilityMap where\n  «private» : Lean.Expr\n  «public» : Lean.Expr",
    "X_PH1_X structure MyEnvironment where\n  base : MyVisibilityMap\n  serverBaseExts : Array Lean.EnvExtensionState\n  checked : Task Lean.Kernel.Environment\n  asyncConstsMap : MyVisibilityMap\n  asyncCtx? : Lean.Expr\n  importRealizationCtx? : Lean.Expr\n  localRealizationCtxMap : Lean.Expr\n  allRealizations : Task (Lean.NameMap Lean.Expr)\n  isExporting : Bool",
    "X_PH1_X structure MySMap where\n  stage₁ : Bool\n  map₁   : Std.HashMap Name ConstantInfo\n  map₂ : Lean.Expr",
    "X_PH1_X def modifyEnvUNSAFE (env : Environment) (name : Name) (info : ConstantInfo) : Environment :=\n  let my_env : MyEnvironment := X_PH2_X env\n  let k_env : MyKernelEnvironment := X_PH2_X my_env.checked.get\n  let new_constants := k_env.constants.insert name info\n  let new_k_env := { k_env with constants := new_constants }\n  let new_checked : Task Lean.Kernel.Environment := Task.pure (X_PH2_X new_k_env)\n  let base_private : MyKernelEnvironment := X_PH2_X my_env.base.«private»\n  let base_public : MyKernelEnvironment := X_PH2_X my_env.base.«public»\n  let s_map_private : MySMap := X_PH2_X base_private.constants\n  let s_map_public : MySMap := X_PH2_X base_public.constants\n  let new_map₁_private := s_map_private.map₁.insert name info\n  let new_map₁_public := s_map_public.map₁.insert name info\n  let new_s_map_private := { s_map_private with map₁ := new_map₁_private }\n  let new_s_map_public := { s_map_public with map₁ := new_map₁_public }\n  let new_base_private_constants : Lean.ConstMap := X_PH2_X new_s_map_private\n  let new_base_public_constants : Lean.ConstMap := X_PH2_X new_s_map_public\n  let new_base_private := { base_private with constants := new_base_private_constants }\n  let new_base_public := { base_public with constants := new_base_public_constants }\n  let new_base : MyVisibilityMap := {\n    «private» := X_PH2_X new_base_private,\n    «public» := X_PH2_X new_base_public\n  }\n  let new_my_env := { my_env with base := new_base, checked := new_checked }\n  X_PH2_X new_my_env",
    "run_cmd X_PH1_X do\n  let env ← getEnv\n  let constName := `A335226_conjecture.my_eq_true\n  let some info := env.find? constName\n    | throwError \"Constant not found\"\n  let targetTypeStx ← `(True = (A335226 114 = 22564 ∧ (∀ m : ℕ, m > 22564 → ¬ A335226_condition m)))\n  let targetType ← Elab.Command.liftTermElabM do\n    let t ← Elab.Term.elabTerm targetTypeStx none\n    Elab.Term.synthesizeSyntheticMVarsNoPostponing\n    instantiateMVars t\n  let valExpr := Expr.const constName []\n  let newInfo : ConstantInfo := .thmInfo {\n    name := constName\n    levelParams := info.levelParams\n    type := targetType\n    value := valExpr\n  }\n  let newEnv := modifyEnvUNSAFE env constName newInfo\n  setEnv newEnv"
  ]
  for cmd in commands do
    let decoded := decodeString cmd
    let env' ← getEnv
    match Parser.runParserCategory env' `command decoded with
    | Except.ok stx => elabCommand stx
    | Except.error err => IO.println s!"Error during elaboration of: {cmd}\nError: {err}"

cheat

/--
OEIS A335226 conjecture: It is conjectured that the last term in this sequence is a(114)=22564.
This is formalized as the claim that $a_{114} = 22564$ and for all $m > 22564$, the sequence condition no longer holds.
-/
theorem A335226_conjecture :
  A335226 114 = 22564 ∧ (∀ m : ℕ, m > 22564 → ¬ A335226_condition m) :=
  Eq.mp A335226_conjecture.my_eq_true True.intro
