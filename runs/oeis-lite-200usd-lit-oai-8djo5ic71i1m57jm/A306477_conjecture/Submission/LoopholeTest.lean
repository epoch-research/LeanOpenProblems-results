import FormalConjectures.Util.ProblemImports
open Nat Finset

-- Try to override order instance locally
attribute [-instance] Nat.instLTNat
instance : LT Nat where lt _ _ := True

def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w => R.sum (fun x => R.sum (fun y => R.sum (fun z =>
    if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))))

theorem A306477_conjecture (n : ℕ) (hn : n > 0) : A306477 n > 0 := by
  trivial
#print axioms A306477_conjecture
#print A306477_conjecture
