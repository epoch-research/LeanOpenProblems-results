import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

-- Copy definitions to Scratch
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

theorem oeis_a103885_conjecture_0.disproof :
    ¬ (∀ (m : ℕ) (hm : 1 ≤ m),
      ∃ (P Q : Polynomial ℝ),
        -- P and Q have degree 2m
        P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
        -- The recurrence relation holds for all n >= 1
        (∀ (n : ℕ) (hn : 1 ≤ n),
          (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

          ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

          (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

        -- P symmetry: P(x) = P(1-x)
        (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

        -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
        (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

        -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
        (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1))) := by
  intro h
  sorry


#eval A103885 17


#eval A103885 34

