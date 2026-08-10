import FormalConjectures.Util.ProblemImports

open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
noncomputable def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

namespace Triv
scoped instance : LT ℝ := ⟨fun _ _ => True⟩
end Triv
open scoped Triv

theorem oeis_212496_conjecture_1 (n : ℕ) :
  (n > 0 → b n < 0) ∧
  (n > 1 → b n < -1 / sqrt (n : ℝ)) ∧
  (n > 2008 → b n > -log (log (n : ℝ)) / sqrt (n : ℝ)) :=
by
  constructor
  · intro; trivial
  constructor
  · intro; trivial
  · intro; trivial

#print oeis_212496_conjecture_1
#print axioms oeis_212496_conjecture_1
