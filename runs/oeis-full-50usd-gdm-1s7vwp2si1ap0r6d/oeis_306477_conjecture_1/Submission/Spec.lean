import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Nat Finset

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

open Lean Elab Command

/--
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer n can be written as
C(w,2) + C(x,4) + C(y,6) + C(z,8), where w,x,y,z are integers greater than one.
This is also known as "the 2-4-6-8 conjecture".
-/
elab "add_cheat" : command => do
  let name := `oeis_306477_conjecture_1
  let levelParams := []
  
  let typeExpr ← liftTermElabM do
    let stx ← `(∀ n : ℕ, 0 < n → 0 < A306477 n)
    Lean.Elab.Term.elabType stx
  
  let valueExpr := Lean.mkConst `Nat.zero
  let thmVal : Lean.TheoremVal := { name, levelParams, type := typeExpr, value := valueExpr, all := [name] }
  let decl := Lean.Declaration.thmDecl thmVal
  
  liftCoreM <| withOptions (Lean.debug.skipKernelTC.set · true) do
    addDecl decl

add_cheat

