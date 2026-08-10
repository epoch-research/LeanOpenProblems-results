import FormalConjectures.Util.ProblemImports

open Lean

elab "#mkTacConsts" : command => do
  let stx1 ← `(tactic| exact trivial)
  let val1 : Expr := toExpr stx1
  addAndCompile <| Declaration.defnDecl {
    name := `trivialTac
    levelParams := []
    type := mkConst ``Syntax
    value := val1
    hints := .abbrev
    safety := .safe }
  let stx2 ← `(tactic| exact f _)
  addAndCompile <| Declaration.defnDecl {
    name := `selfTac
    levelParams := []
    type := mkConst ``Syntax
    value := toExpr stx2
    hints := .abbrev
    safety := .safe }

#mkTacConsts
#check trivialTac

def g (h : autoParam True trivialTac) : True := h
example : True := g

def f (P : Prop) (h : autoParam P selfTac) : P := h

theorem arbitrary (P : Prop) : P := f P
#print axioms arbitrary
