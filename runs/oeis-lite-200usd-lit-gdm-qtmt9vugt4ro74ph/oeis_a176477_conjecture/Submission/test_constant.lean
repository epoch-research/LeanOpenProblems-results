import Lean

opaque my_constant : False

open Lean

def check : MetaM Unit := do
  let env ← getEnv
  match env.find? `my_constant with
  | some (ConstantInfo.opaqueInfo v) =>
    IO.println s!"value: {v.value}"
  | some _ => IO.println s!"other constant info"
  | none => IO.println s!"not found"

#eval check
