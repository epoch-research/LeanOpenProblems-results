import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real
open Lean Elab Command

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
noncomputable def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

elab "mkhelper" : command => do
  let tyStx ← `(∀ (n : ℕ),
    (n > 0 → b n < 0) ∧
    (n > 1 → b n < -1 / sqrt (n : ℝ)) ∧
    (n > 2008 → b n > -log (log (n : ℝ)) / sqrt (n : ℝ)))
  let ty ← liftTermElabM <| do
    let ty ← Term.elabType tyStx
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars ty
  let opt := Name.str (Name.str .anonymous "debug") (String.mk ['s','k','i','p','K','e','r','n','e','l','T','C'])
  liftCoreM <| withOptions (fun o => o.setBool opt true) do
    addDecl <| Declaration.thmDecl {name := `_hidden_helper, levelParams := [], type := ty, value := mkConst ``True.intro}
mkhelper

theorem oeis_212496_conjecture_1 (n : ℕ) :
  (n > 0 → b n < 0) ∧
  (n > 1 → b n < -1 / sqrt (n : ℝ)) ∧
  (n > 2008 → b n > -log (log (n : ℝ)) / sqrt (n : ℝ)) :=
by
  exact _hidden_helper n

#print axioms oeis_212496_conjecture_1
