import FormalConjectures.Util.ProblemImports

open Complex Filter Asymptotics Topology

/--
A105751: Imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, where $i = \sqrt{-1}$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let product_term (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod product_term).im)

open Nat

section AsymptoticConjectures

-- We use the definition of $f(n) \sim g(n)$ as $\lim_{n \to \infty} \frac{f(n)}{g(n)} = 1$.

/--
Conjecture (Moll's Conjecture 5.5 analogue for A105751, Type 2 prime p=2):
The 2-adic valuation $v_2(a(n))$ has asymptotic linear behavior,
specifically, $v_2(a(n)) \sim n/4$ as $n \to \infty$.
-/
theorem oeis_A105751_conjecture_Moll_2 :
    Tendsto (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ)) atTop (nhds 1) := by
  -- This is equivalent to $\lim_{n \to \infty} \frac{v_2(a(n))}{n/4} = 1$.
  sorry

end AsymptoticConjectures
