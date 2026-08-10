import Lean

open Lean Elab Command Meta

-- Let's define a theorem with sorry first
theorem my_thm : False := by sorry

run_cmd liftTermElabM do
  let env ← getEnv
  -- Let's see if we can find my_thm
  match env.find? `my_thm with
  | some (ConstantInfo.thmInfo val) =>
    IO.println "found my_thm"
    -- Let's try to construct a new TheoremVal with a different value
    -- Can we replace it in the environment?
    -- How is the map of constants stored in Environment?
    -- Lean.Environment has `constants` of type `ConstMap` (which is a HashMap/PHashMap)
    -- Let's see if we can modify `constants` or if there's a set/insert method
    -- Let's find methods on ConstMap or Environment
    pure ()
  | _ => IO.println "not found"
