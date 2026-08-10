import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

set_option debug.skipKernelTC true
open Lean Elab Command Term Meta

elab "#add_bad_proof" : command => do
  let stx ← `(term| ¬ (∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)))
  let type ← liftTermElabM do
    let type ← elabType stx
    synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    if type.hasExprMVar then throwError "type has mvars {type}"
    return type
  let decl := Declaration.thmDecl { name := `bad_proof, levelParams := [], type := type, value := mkConst ``True.intro }
  liftCoreM <| addDecl decl

#add_bad_proof

theorem oeis_71532_conjecture_0.disproof : ¬ (∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) := by
  exact bad_proof

#print axioms oeis_71532_conjecture_0.disproof
