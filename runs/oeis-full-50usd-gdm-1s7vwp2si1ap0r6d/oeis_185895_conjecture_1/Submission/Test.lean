import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial.cast
  a_n_q.floor


def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

theorem is_tri_1 : is_triangular 1 := ⟨1, by rfl⟩

theorem test0 : A185895 0 = 1 := by
  unfold A185895
  simp

theorem test2 : A185895 2 = -1 := by
  unfold A185895
  simp only [Nat.ofNat_pos, ↓reduceDIte]
  rw [prod_Icc_succ_top (by decide)]
  simp only [Icc_self, prod_singleton]
  -- Now we have a polynomial product: (1 - X) * (1 - C (1/2) * X^2)
  -- Let's prove its coefficient of X^2 is -1/2.
  -- Px = (1 - X) * (1 - C (1/2) * X^2) = 1 - X - C (1/2) * X^2 + C (1/2) * X^3
  -- Let's evaluate Polynomial.coeff Px 2.
  -- Using Polynomial.coeff_mul:
  rw [Polynomial.coeff_mul]
  -- This is a sum over antidiagonal 2.
  -- Antidiagonal 2 has elements (0, 2), (1, 1), (2, 0).
  -- Let's expand the sum over antidiagonal 2.
  -- In Lean, Finset.sum over antidiagonal 2 can be simplified.
  -- Let's try to do it by dec_trivial or simp.
  sorry



















