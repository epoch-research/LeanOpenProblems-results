import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#scan_usable" : command => do
  liftTermElabM do
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      if n.toString.startsWith "_" then continue
      let ty := ci.type
      try
        forallTelescopeReducing ty fun xs body => do
          let body ← whnf body
          if body.isConstOf ``False then
            logInfo m!"FALSE {n} nargs={xs.size}\n  {ty}"
          if body.isFVar then
            let ldecl ← body.fvarId!.getDecl
            let k ← whnf ldecl.type
            if k.isSort then
              logInfo m!"ARB {n} nargs={xs.size}\n  {ty}"
      catch _ => pure ()

#scan_usable
