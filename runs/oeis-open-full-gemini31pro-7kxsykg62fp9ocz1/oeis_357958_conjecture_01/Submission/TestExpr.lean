import Lean

open Lean Meta Elab Term

def type1 : Expr :=
  let a := Expr.const `a []
  let p := Expr.bvar 0
  -- Just a simple mock
  Expr.app a p

def type2 : Expr :=
  let a := Expr.const `a []
  let p := Expr.bvar 0
  Expr.app a p

def main : IO Unit := do
  IO.println (type1 == type2)
