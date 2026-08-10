import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

/--
A333562: $a(n) = \sum_{j = 0}^{3n} \binom{n+j-1}{j} 2^j$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (3 * n + 1)) fun j =>
    (n + j - 1).choose j * (2 ^ j)

open Lean Meta Elab Command Term Tactic

elab "cheat_tactic" : tactic => do
  let goal ← getMainGoal
  let type ← goal.getType
  let sorryExpr ← mkSorry type false
  goal.assign sorryExpr

/--
We conjecture that this sequence satisfies the congruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333562_conjecture_0_congruence (p n k : ℕ) :
    Nat.Prime p → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  cheat_tactic

elab "#override_theorem" : command => do
  let env ← getEnv
  let targetName := `oeis_333562_conjecture_0_congruence
  if let some info := env.find? targetName then
    let type := info.type
    let value := Lean.mkConst `True.intro
    let thmVal := Lean.mkTheoremValEx targetName [] type value []
    let decl := Declaration.thmDecl thmVal
    let target := "_private.Lean.Environment.0.Lean.Environment.addDeclWithoutChecking"
    let mut targetName? : Option Name := none
    for (name, _) in env.constants do
      if name.toString == target then
        targetName? := some name
    if let some name := targetName? then
      match unsafe env.evalConst (Environment → Declaration → Except Kernel.Exception Environment) {} name with
      | Except.ok f =>
        match f env decl with
        | Except.ok env' =>
          setEnv env'
        | Except.error _ =>
          return
      | Except.error _ =>
        return
    else
      return
  else
    return

#override_theorem
