import FormalConjectures.Util.ProblemImports

open Nat Finset Nat.ModEq

theorem wilson_relation (k : ℕ) (hk : k > 1) :
  let Pk      := Nat.nth Nat.Prime (k - 1);
  let Pk_succ := Nat.nth Nat.Prime k;
  let Congruence := Nat.factorial Pk ≡ 1 [MOD Pk_succ];
  let Wk_prod : ℕ := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;
  Congruence ↔ Wk_prod ≡ 1 [MOD Pk_succ] := by sorry
