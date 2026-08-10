import FormalConjectures.Util.ProblemImports

open Lean Meta

unsafe def startsWithList : List Char → List Char → Bool
| [], _ => true
| _, [] => false
| a::as, b::bs => a == b && startsWithList as bs

unsafe def containsList (needle hay : List Char) : Bool :=
  match hay with
  | [] => needle == []
  | _::xs => startsWithList needle hay || containsList needle xs

unsafe def hasSub (needle hay : String) : Bool := containsList needle.toList hay.toLower.toList

unsafe def nameSearch2 : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (hasSub "prime" s) && (hasSub "exists" s || hasSub "gap" s || hasSub "twin" s || hasSub "pair" s || hasSub "consecutive" s || hasSub "constellation" s || hasSub "tuple" s || hasSub "arith" s || hasSub "progression" s) then
      arr := arr.push (n, ci.type)
  logInfo m!"matches {arr.size}"
  for (n,t) in arr[:arr.size.min 500] do logInfo m!"MATCH {n}: {t}"

#eval! nameSearch2
