import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

lemma m1_conjecture :
    ∃ (P Q : Polynomial ℝ),
      P.degree = (2 * 1 : ℕ) ∧ Q.degree = (2 * 1 : ℕ) ∧
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus 1 n * P.eval (n : ℝ)) * (A103885_subsequence_real 1 (n + 1)) +
        ((-1 : ℝ) ^ 1 * prod_factor_minus 1 n * P.eval (-(n : ℝ))) * (A103885_subsequence_real 1 (n - 1)) =
        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real 1 n)) ∧
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) := by
  let P : Polynomial ℝ := 5 * X^2 - 5 * X + 1
  let Q : Polynomial ℝ := 220 * X^2 - 136 * X + 12
  use P, Q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hP : (5 * X^2 - 5 * X + 1 : ℝ[X]).natDegree = 2 := by
      decide
    sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
