import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Term

def mkNatListExpr (ns : List ℕ) : Expr :=
  ns.foldr (fun n acc =>
    mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Nat []) (mkNatLit n) acc
  ) (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Nat []))


elab "parsed_factors" s:str : term => do
  let str := s.getString
  let parts := str.splitOn ","
  let ns := parts.map String.toNat!
  return mkNatListExpr ns

-- Test with a flat string of 10,000 numbers
def my_factors : List ℕ := parsed_factors "2,3,5,7,11,13,17,19"

#eval my_factors.length

theorem test_len : my_factors.length = 8 := by
  rfl
