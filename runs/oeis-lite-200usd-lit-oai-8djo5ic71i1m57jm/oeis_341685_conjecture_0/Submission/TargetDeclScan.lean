import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

unsafe def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

unsafe def isAllowed (n : Name) : CoreM Bool := do
  let axs ← collectAxioms n
  return axs.all (allowedAxioms.contains ·)

partial def stripForallMeta (e : Expr) : Expr :=
  match e.consumeMData with
  | .forallE _ _ b _ => stripForallMeta b
  | .letE _ _ _ b _ => stripForallMeta b
  | x => x

def exprNamesString (e : Expr) : String :=
  String.intercalate " " ((e.getUsedConstants.map (·.toString)).qsort (· < ·)).toList

def containsAny (s : String) (needles : List String) : Bool := needles.any (fun n => s.contains n)

elab "#target_decl_scan" : command => unsafe do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 600 then
      let type := ci.type
      let concl := stripForallMeta type
      let names := exprNamesString type
      let cnames := exprNamesString concl
      if containsAny names ["IsAlgebraic", "Transcendental", "Algebra.IsAlgebraic", "Module.Finite", "FiniteDimensional", "Padic", "aeval", "Polynomial"] then
        if ← liftCoreM <| isAllowed n then
          if containsAny cnames ["IsAlgebraic", "Transcendental", "Algebra.IsAlgebraic", "Module.Finite", "FiniteDimensional", "False", "Injective", "Surjective", "Polynomial.aeval"] then
            logWarning m!"DECL {n} : {type} | CONCL {concl}"
            count := count + 1
  logWarning m!"printed {count}"

#target_decl_scan
#eval (3)
