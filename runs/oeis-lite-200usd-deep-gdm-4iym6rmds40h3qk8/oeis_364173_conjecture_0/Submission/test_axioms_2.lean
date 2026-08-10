import Mathlib

open Lean Meta

def getAxioms (declName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut axioms := #[]
  let mut visited : HashSet Name := {}
  let mut queue : List Name := [declName]
  while !queue.isEmpty do
    let curr :: rest := queue | break
    queue := rest
    if visited.contains curr then continue
    visited := visited.insert curr
    if let some constInfo := env.find? curr then
      if constInfo.isAxiom then
        axioms := axioms.push curr
      else
        let valueExpr? := constInfo.value?
        let typeExpr := constInfo.type
        let mut deps : HashSet Name := {}
        let collectDeps (e : Expr) : StateM (HashSet Name) Unit := do
          e.forEach fun f => do
            if f.isConst then
              modify (fun s => s.insert f.constName!)
        let (_, typeDeps) := collectDeps typeExpr {}
        let (_, valDeps) := match valueExpr? with
          | some val => collectDeps val {}
          | none => ({}, {})
        for dep in typeDeps.toArray ++ valDeps.toArray do
          if !visited.contains dep then
            queue := dep :: queue
  return axioms

#elab "print_axioms" id:ident : tactic => do
  let declName := id.getId
  let axioms ← getAxioms declName
  IO.println s!"Axioms of {declName}: {axioms}"

theorem test_thm : 2 + 2 = 4 := by rfl

example : True := by
  print_axioms test_thm
  trivial
