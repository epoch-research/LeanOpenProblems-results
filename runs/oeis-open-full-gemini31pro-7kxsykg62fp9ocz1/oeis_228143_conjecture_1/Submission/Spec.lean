import FormalConjectures.Util.ProblemImports

open BigOperators Matrix Nat PowerSeries

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

noncomputable def a (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  M.det.natAbs

noncomputable def OGF_A_scaled : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ) / (3 ^ n : ℚ)

theorem oeis_228143_conjecture_1 :
    ∃ C : PowerSeries ℤ,
      (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = OGF_A_scaled :=
  by sorry

theorem oeis_228143_conjecture_1.disproof : ¬ (type_of% @oeis_228143_conjecture_1) := sorry
