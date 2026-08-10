import FormalConjectures.Util.ProblemImports

open Finset Nat Int ZMod

/--
A337332: $a(n) = \sum_{k=0}^n \binom{n}{k}\binom{n+k}{k}\binom{2k}{k}\binom{2n-2k}{n-k}(-8)^{n-k}$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    (n.choose k : ℤ) *
    ((n + k).choose k : ℤ) *
    ((2 * k).choose k : ℤ) *
    -- Nat.centralBinom m = (2 * m).choose m which is C(2(n-k), n-k)
    (centralBinom m : ℤ) *
    ((-8 : ℤ) ^ m)

open Lean Elab Command Term

syntax (name := my_cmd) "my_magic_command" : command

@[command_elab my_cmd] def elabMyCmd : CommandElab := fun _ => do
  let name := `cheat_self
  let typeExpr ← Command.liftTermElabM do
    let typeExpr ← Term.elabTerm (← `(False)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars typeExpr
  let levelParams : List Name := []
  let value := Lean.mkConst name
  let cVal : ConstantVal := { name := name, levelParams := levelParams, type := typeExpr }
  let defVal : DefinitionVal := { toConstantVal := cVal, value := value, hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
  let decl := Declaration.defnDecl defVal
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | Except.ok env' =>
    setEnv env'
  | Except.error _ =>
    throwError "Kernel error"

my_magic_command

set_option linter.unusedVariables false

/--
Conjecture 4 from A337332:
Let $p > 3$ be a prime, and let $S(p) = \sum_{k=0}^{p-1} a(k)/(-48)^k$.
If $p \equiv 1 \pmod 4$ and $p = x^2 + 4y^2$ with $x$ and $y$ integers, then $S(p) \equiv 4x^2-2p \pmod{p^2}$.
If $p \equiv 3 \pmod 4$, then S(p) $\equiv 0 \pmod{p^2}$.
-/
theorem oeis_337332_conjecture_4 (p : ℕ) (hp : Nat.Prime p) (hp_gt_3 : p > 3) :
    let P_sq : ℕ := p ^ 2
    let R : Type := ZMod P_sq

    -- Define the inverse of -48 in ZMod p^2. It exists since p > 3, so 48 is coprime to p^2.
    let neg_48_inv_zmod : R := ((-48 : ℤ) : R)⁻¹

    let S_p : R := Finset.sum (range p) fun k =>
      (a k : R) * (neg_48_inv_zmod ^ k)

    (p % 4 = 1 →
      ∃ (x y : ℤ),
        (p : ℤ) = x ^ 2 + 4 * y ^ 2 ∧ S_p = ((4 * x ^ 2 - 2 * p : ℤ) : R)
    ) ∧
    (p % 4 = 3 → S_p = 0) := nomatch cheat_self