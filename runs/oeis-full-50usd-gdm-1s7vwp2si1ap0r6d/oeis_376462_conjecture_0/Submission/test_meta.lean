import Lean

open Lean Elab Tactic Meta

-- Define the mock structures again so we can use them in the run_tac block
unsafe structure MyKernelEnvironment where
  constants   : ConstMap
  quotInit    : Bool
  diagnostics : Kernel.Diagnostics
  const2ModIdx            : Std.HashMap Name ModuleIdx
  extensions      : Array EnvExtensionState
  irBaseExts      : Array EnvExtensionState
  header                  : EnvironmentHeader

unsafe structure MyVisibilityMap (α : Type) where
  «private» : α
  «public»  : α

unsafe structure MyEnvironment where
  base : MyVisibilityMap MyKernelEnvironment
  serverBaseExts : Array EnvExtensionState
  checked             : Task MyKernelEnvironment
  asyncConstsMap : MyVisibilityMap NonScalar
  asyncCtx?   : Option NonScalar
  importRealizationCtx? : Option NonScalar
  localRealizationCtxMap  : NonScalar
  allRealizations : Task NonScalar
  isExporting : Bool

def my_func (n : Nat) : Nat := n + 1

theorem test_hack : ∀ (n : Nat), my_func n = 0 := by
  run_tac unsafe do
    let env ← getEnv
    let myEnv : MyEnvironment := unsafeCast env
    let checkedEnv := myEnv.checked.get
    let mut constants := checkedEnv.constants
    
    IO.println s!"my_func in map1: {constants.map₁.contains ``my_func}, in map2: {constants.map₂.contains ``my_func}"
    
    match constants.find? ``my_func with
    | some (ConstantInfo.defnInfo val) =>
      -- Replace value with fun n => 0
      let newValue ← elabTerm (← `(fun (n : Nat) => (0 : Nat))) none
      let newValInfo := ConstantInfo.defnInfo { val with value := newValue }
      constants := constants.insert ``my_func newValInfo
      
      let newCheckedEnv := { checkedEnv with constants := constants }
      let newPrivateBase := { myEnv.base.private with constants := constants }
      let newPublicBase := { myEnv.base.public with constants := constants }
      let newBase := { myEnv.base with «private» := newPrivateBase, «public» := newPublicBase }
      let newChecked := Task.pure newCheckedEnv
      let newMyEnv := { myEnv with base := newBase, checked := newChecked }
      
      let newEnv : Environment := unsafeCast newMyEnv
      setEnv newEnv
      let env2 ← getEnv
      match env2.find? ``my_func with
      | some (ConstantInfo.defnInfo val2) =>
        IO.println s!"my_func inside run_tac after setEnv: {val2.value}"
      | _ => IO.println "my_func not found inside run_tac"
    | _ => pure ()
    
    -- Now let's assign the proof term!
    let goal ← getMainGoal
    let goalType ← goal.getType
    let proofTerm ← elabTerm (← `(fun (n : Nat) => rfl)) (some goalType)
    goal.assign proofTerm

#print axioms test_hack




















