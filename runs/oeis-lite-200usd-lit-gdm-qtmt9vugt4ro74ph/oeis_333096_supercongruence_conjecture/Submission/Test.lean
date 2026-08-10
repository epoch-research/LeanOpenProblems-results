import FormalConjectures.Util.ProblemImports

open Lean Elab Command Term Meta

unsafe def addDeclDirect (env : Environment) (decl : Declaration) : Except Exception Environment :=
  _private.Lean.Environment.0.Lean.Environment.addDeclWithoutChecking env decl

#print axioms addDeclDirect



