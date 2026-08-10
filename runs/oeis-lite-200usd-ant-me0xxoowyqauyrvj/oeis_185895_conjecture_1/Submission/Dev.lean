import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

noncomputable def gpoly (N : ℕ) : Polynomial ℚ :=
  (Finset.Icc 1 N).prod (fun k : ℕ => (1 : Polynomial ℚ) - C ((1:ℚ) / k.factorial) * X ^ k)

-- G N j = (gpoly N).coeff j * j!
noncomputable def Gr (N j : ℕ) : ℚ := (gpoly N).coeff j * j.factorial

example : gpoly 0 = 1 := by simp [gpoly]

-- recursion at polynomial level
example (N : ℕ) : gpoly (N+1) = gpoly N * ((1:Polynomial ℚ) - C ((1:ℚ)/(N+1).factorial) * X^(N+1)) := by
  unfold gpoly
  rw [Finset.prod_Icc_succ_top (by omega)]
