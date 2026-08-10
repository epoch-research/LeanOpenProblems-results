import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000


open Lean Meta Elab Command

elab "#scan_closed_false_like" : command => do
  liftTermElabM do
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      if n.toString.startsWith "_" then continue
      let ty := ci.type
      try
        forallTelescopeReducing ty fun xs body => do
          let body ← whnf body
          unless body.isConstOf ``False do return ()
          let mut ok := true
          for x in xs do
            let d ← x.fvarId!.getDecl
            if d.binderInfo == BinderInfo.default then
              ok := false
          if ok then
            logInfo m!"CLOSED_FALSE_LIKE {n} nargs={xs.size}\n  {ty}"
      catch _ => pure ()

#scan_closed_false_like
