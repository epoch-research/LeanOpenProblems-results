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

/-- Integer real/imaginary part sequence of the Gaussian product
    `∏_{k=0}^{n} (1 + k·i)`.  We have `Aa n = Re`, `Bb n = Im`. -/
def AB : ℕ → ℤ × ℤ
| 0 => (1, 0)
| (n+1) => let p := AB n; (p.1 - (n+1) * p.2, p.2 + (n+1) * p.1)

def Aa (n : ℕ) : ℤ := (AB n).1
def Bb (n : ℕ) : ℤ := (AB n).2

/-- The complex product equals `Aa n + Bb n · i`. -/
lemma prod_eq (n : ℕ) :
    (Finset.range (n + 1)).prod (fun k => (1 : ℂ) + (k : ℂ) * I)
      = (Aa n : ℂ) + (Bb n : ℂ) * I := by
  induction n with
  | zero => simp [Aa, Bb, AB]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    simp only [Aa, Bb, AB]
    push_cast; ring_nf; rw [Complex.I_sq]; ring

/-- The OEIS entry `a n` is exactly the imaginary part `Bb n`. -/
lemma a_eq (n : ℕ) : a n = Bb n := by
  unfold a; simp only; rw [prod_eq n]; simp

/-- The squared norm `Aa n ^2 + Bb n ^2 = ∏_{k=1}^n (1 + k^2)`. -/
def NN : ℕ → ℤ
| 0 => 1
| (n+1) => (1 + (n+1)^2) * NN n

lemma norm_eq (n : ℕ) : (Aa n)^2 + (Bb n)^2 = NN n := by
  induction n with
  | zero => simp [Aa, Bb, AB, NN]
  | succ m ih =>
    simp only [Aa, Bb, AB, NN] at ih ⊢
    linear_combination (1 + ((m : ℤ) + 1) ^ 2) * ih

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
