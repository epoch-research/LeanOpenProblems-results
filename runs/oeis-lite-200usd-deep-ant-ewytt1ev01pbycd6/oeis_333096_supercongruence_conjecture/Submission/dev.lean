import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators Int

/-!
Development file for the OEIS A333096 supercongruence.
Strategy (see /memories/progress.md):
  a_gen m n = [x^n]((1+x)^{(m+2)n} G(x))  for m ≠ -1, where
  G(x) = (1+x)(1-x)^2/(1-x^3), coeffs g_0=1, g_j = 2 if 3|j else -1 (j≥1).
  This equals sum_{j=0}^n g_j * (generalized binom (m+2)n choose (n-j)).
  Supercongruence via Straub constant-term method: term-by-term v_p bound ≥ 3k.
  m=-1: period 6, even => trivial.
-/

-- Definitions copied from Spec.lean
def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    (r * num_choose) / denominator

def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k => generalized_catalan_coefficient r k

-- The weight sequence g_j
def gcoef (j : ℕ) : ℤ := if j = 0 then 1 else if j % 3 = 0 then 2 else -1

-- Generalized binomial (r choose s) for integer r (as a product / factorial, exact)
noncomputable def intChoose (r : ℤ) (s : ℕ) : ℤ :=
  (Finset.prod (Finset.range s) fun i => r - (i : ℤ)) / (s.factorial : ℤ)

-- Closed form (target lemma P1), m ≠ -1
theorem closed_form (m : ℤ) (hm : m ≠ -1) (n : ℕ) :
    a_gen m n = Finset.sum (range (n + 1)) fun j => gcoef j * intChoose ((m + 2) * n) (n - j) := by
  sorry
