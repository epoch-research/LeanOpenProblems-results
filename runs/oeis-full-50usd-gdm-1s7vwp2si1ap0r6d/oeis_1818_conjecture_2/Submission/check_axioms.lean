import Submission.Spec
import Lean

open Lean Elab Command

def checkAxioms : CoreM Unit := do
  let env ← getEnv
  let constInfo ← env.get`oeis_1818_conjecture_2
  IO.println s!"Value: {constInfo.value?}"
  let axioms := env.find? `oeis_1818_conjecture_2
  IO.println s!"Axioms of oeis_1818_conjecture_2: {← collectAxioms `oeis_1818_conjecture_2}"

def collectAxioms (name : Name) : CoreM (List Name) := do
  let env ← getEnv
  let mut axioms := []
  -- We can collect transitive dependencies that are axioms
  let mut visited : NameSet := {}
  let mut toVisit := [name]
  while !toVisit.isEmpty do
    let curr := toVisit.head!
    toVisit := toVisit.tail
    if !visited.contains curr then
      visited := visited.insert curr
      if let some info := env.find? curr then
        if info.isAxiom then
          axioms := curr :: axioms
        else
          match info.value? with
          | some val =>
            -- Collect constants from the value expression
            let consts := val.getUsedConstants
            for c in consts do
              toVisit := c :: toVisit
          | none => pure ()
  return axioms.eraseDups

#eval checkAxioms
