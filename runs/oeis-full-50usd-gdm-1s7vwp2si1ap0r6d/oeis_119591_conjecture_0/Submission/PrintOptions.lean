import Lean

open Lean

def printOptions : CoreM Unit := do
  let decls ← getOptionDecls
  for (name, decl) in decls do
    IO.println s!"{name} : {decl.descr}"

#eval printOptions
