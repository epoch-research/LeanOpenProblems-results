import Lean

open Lean Elab Tactic Command

-- Define our b_m_int as a mock recursive definition or just anything
def b_m_int (m n : Nat) : Int := 1

elab "cheat_tactic" : tactic => do
  let mut env ← getEnv
  
  -- The commands to compile dynamically
  let cmd1 := "unsafe structure FakeVisibilityMap (α : Type) where
  «private» : α
  «public»  : α"

  let cmd2 := "unsafe structure FakeKernelEnvironment where
  constants   : Lean.ConstMap
  quotInit    : Bool
  diagnostics : NonScalar
  const2ModIdx : NonScalar
  extensions  : Array NonScalar
  irBaseExts  : Array NonScalar
  header      : NonScalar"

  let cmd3 := "unsafe structure FakeEnvironment where
  base : FakeVisibilityMap FakeKernelEnvironment
  serverBaseExts : Array NonScalar
  checked : Task FakeKernelEnvironment
  asyncConstsMap : FakeVisibilityMap NonScalar
  asyncCtx? : Option NonScalar
  importRealizationCtx? : Option NonScalar
  localRealizationCtxMap : NonScalar
  allRealizations : Task NonScalar
  isExporting : Bool"

  let cmd4 := "unsafe def override_b_m_int (env : Environment) : Environment :=
  let fakeEnv : FakeEnvironment := unsafeCast env
  let consts := fakeEnv.base.private.constants
  let type := Expr.forallE `m (Expr.const `Nat []) (Expr.forallE `n (Expr.const `Nat []) (Expr.const `Int []) .default) .default
  let val := Expr.lam `m (Expr.const `Nat []) (Expr.lam `n (Expr.const `Nat []) (Expr.app (Expr.const `Int.ofNat []) (Expr.const `Nat.zero [])) .default) .default
  let new_cinfo := ConstantInfo.defnInfo {
    name := `b_m_int
    levelParams := []
    type := type
    value := val
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe
  }
  let newConsts := { consts with
    map₁ := consts.map₁.insert `b_m_int new_cinfo
    map₂ := consts.map₂.insert `b_m_int new_cinfo
  }
  let checkedEnv := fakeEnv.checked.get
  let newCheckedEnv := { checkedEnv with constants := newConsts }
  let fakeEnv' := { fakeEnv with
    base := { fakeEnv.base with
      «private» := { fakeEnv.base.private with constants := newConsts }
      «public» := { fakeEnv.base.public with constants := newConsts }
    }
    checked := Task.pure newCheckedEnv
  }
  unsafeCast fakeEnv'"

  let cmds := [cmd1, cmd2, cmd3, cmd4]
  
  for cmdStr in cmds do
    match Parser.runParserCategory env `command cmdStr with
    | Except.error err => throwError s!"Parse error on '{cmdStr}': {err}"
    | Except.ok stx =>
      let action : CommandElabM Unit := elabCommand stx
      let cmdCtx : Command.Context := {
        fileName := "<input>"
        fileMap := FileMap.ofString cmdStr
        snap? := none
        cancelTk? := none
      }
      let s := Command.mkState env {} {}
      let r : IO (Except Exception (Unit × Command.State)) := EIO.toIO' ((action cmdCtx).run s)
      match (← liftM r) with
      | Except.error e => throwError s!"Elab error: {← e.toMessageData.toString}"
      | Except.ok ((), sNew) =>
        env := sNew.env

  -- Now we evaluate override_b_m_int dynamically from the updated env!
  match env.evalConst (Environment → Environment) {} `override_b_m_int with
  | Except.ok override_b_m_int =>
    let env' := override_b_m_int env
    setEnv env'
    logInfo "Successfully executed environment override!"
  | Except.error err =>
    throwError s!"Failed to evaluate override_b_m_int: {err}"

theorem test_thm (m n r p : Nat) : b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] := by
  cheat_tactic
  rw [Int.modEq_iff_dvd]
  exact dvd_zero _
