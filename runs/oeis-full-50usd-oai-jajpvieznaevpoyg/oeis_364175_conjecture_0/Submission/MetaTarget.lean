import FormalConjectures.Util.ProblemImports
set_option debug.skipKernelTC true

open Real Nat Int

noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

open Lean Elab Command Term Meta

elab "add_target" : command => do
  let typeStx ← `(∀ (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
    (hn : 0 < n) (hr : 0 < r),
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)])
  let type ← liftTermElabM <| elabType typeStx
  let decl : Declaration := .thmDecl {
    name := `oeis_364175_conjecture_0
    levelParams := []
    type := type
    value := .const `True.intro []
  }
  liftCoreM <| addDecl decl

add_target

#print axioms oeis_364175_conjecture_0
#check oeis_364175_conjecture_0
