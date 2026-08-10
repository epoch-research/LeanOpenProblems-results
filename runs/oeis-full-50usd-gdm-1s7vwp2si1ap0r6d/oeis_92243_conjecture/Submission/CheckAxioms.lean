import Submission.Spec
import Lean

open Lean

elab "check_axioms " id:ident : command => do
  let env ← getEnv
  let name := id.getId
  match env.find? name with
  | none => IO.println s!"Not found: {name}"
  | some info =>
    let axs := env.extraConstNames
    -- wait, we can get the transitively used axioms of a declaration
    -- let's use the core Lean API to query the axioms
    let axs ← Elab.Command.liftCoreM do
      -- collect axioms
      let mut res : List Name := []
      let decls := env.constants
      -- we can traverse or just print extraConstNames
      pure env.extraConstNames
    IO.println s!"Axioms: {axs.toList}"

#eval check_axioms oeis_92243_conjecture.disproof
