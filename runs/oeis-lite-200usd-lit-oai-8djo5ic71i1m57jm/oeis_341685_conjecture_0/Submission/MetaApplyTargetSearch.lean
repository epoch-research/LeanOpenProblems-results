import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Tactic
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

set_option maxHeartbeats 0

partial def exprNameContains (subs : Array String) : Expr → Bool
| .const n _ => subs.any (fun s => n.toString.contains s)
| .app f a => exprNameContains subs f || exprNameContains subs a
| .forallE _ d b _ => exprNameContains subs d || exprNameContains subs b
| .lam _ d b _ => exprNameContains subs d || exprNameContains subs b
| .letE _ d v b _ => exprNameContains subs d || exprNameContains subs v || exprNameContains subs b
| .mdata _ e => exprNameContains subs e
| .proj _ _ e => exprNameContains subs e
| _ => false

def isCandidate (n : Name) (type : Expr) : Bool :=
  let ns := n.toString
  (ns.contains "IsAlgebraic" || ns.contains "Transcendental" || ns.contains "finite" || ns.contains "Finite" ||
   ns.contains "False" || ns.contains "false" || ns.contains "det" || ns.contains "rank" || ns.contains "finrank") ||
  exprNameContains #["IsAlgebraic", "Transcendental", "Module.Finite", "FiniteDimensional", "False"] type

elab "#try_candidates" : command => do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (n, ci) =>
    match ci with
    | .thmInfo ti => if isCandidate n ti.type then some n else none
    | .axiomInfo ai => if isCandidate n ai.type then some n else none
    | _ => none
  logInfo m!"candidates {candidates.length}"

#try_candidates

-- Run tactic search on targets using all candidate names as apply rules through aesop.
macro "big_aesop" : tactic => `(tactic| aesop (add unsafe 80% apply *))

example : IsAlgebraic ℚ xi_3 := by
  -- placeholder to make file parse; actual search below using try blocks by hand would be too broad
  fail_if_success big_aesop
  sorry
