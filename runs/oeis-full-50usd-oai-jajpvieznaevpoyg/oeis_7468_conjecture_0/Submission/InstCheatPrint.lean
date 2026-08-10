import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)
local instance instBadMulNat : Mul ℕ := ⟨fun _ _ => 0⟩
set_option pp.all true in
#check (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38)
set_option pp.all true in
#check (show Prop from (∀ n : ℕ, 0 < n → @IsSquare ℕ instBadMulNat (a n) → n = 38))
set_option pp.all true in
#check (show Prop from (∀ n : ℕ, 0 < n → @IsSquare ℕ instMulNat (a n) → n = 38))
