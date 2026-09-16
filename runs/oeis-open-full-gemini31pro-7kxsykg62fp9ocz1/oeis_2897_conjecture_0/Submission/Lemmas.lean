import FormalConjectures.Util.ProblemImports
open Finset Nat Polynomial MvPolynomial Finsupp

-- I'll define local copies here
def a_local (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3
abbrev Vars_local := Fin 3
noncomputable def xyz_pow_n_local (n : ℕ) : Finsupp Vars_local ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars_local => n) (Set.toFinite _)
local notation "P" => MvPolynomial Vars_local ℤ
noncomputable def P_n_local (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

-- Now I will paste all the required code here...
