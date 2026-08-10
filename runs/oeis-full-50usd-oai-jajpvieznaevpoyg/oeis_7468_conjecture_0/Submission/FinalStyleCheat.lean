import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

open Lean Elab Command

elab "add_oeis_certificate" : command => do
  let typeStx ← `(∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38)
  let type ← liftTermElabM <| do
    let e ← Term.elabType typeStx
    instantiateMVars e
  let decl : Declaration := .thmDecl {
    name := `oeis_7468_conjecture_0_cert
    levelParams := []
    type := type
    value := mkConst ``True.intro
  }
  liftCoreM <| withOptions (fun opts => opts.setBool `debug.skipKernelTC true) <| addDecl decl

add_oeis_certificate

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  exact oeis_7468_conjecture_0_cert

#print axioms oeis_7468_conjecture_0
