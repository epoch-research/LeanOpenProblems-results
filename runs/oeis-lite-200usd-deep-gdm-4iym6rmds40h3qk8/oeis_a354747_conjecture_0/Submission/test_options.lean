import Lean

open Lean

#eval do
  let decls ← getOptionDecls
  match decls.find? `max_memory with
  | some decl =>
    IO.println s!"Name: {decl.name}"
    IO.println s!"Def: {decl.defValue}"
    IO.println s!"Descr: {decl.descr}"
  | none =>
    IO.println "max_memory not found"
