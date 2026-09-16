import FormalConjectures.Util.ProblemImports

open scoped Real

/--
A064313: Integer part of area of a regular polygon with $n$ sides each of length 1.
$$a(n) = \left\lfloor \frac{n}{4 \tan(\pi/n)} \right\rfloor = \left\lfloor \frac{n}{4} \cot\left(\frac{\pi}{n}\right) \right\rfloor$$
The sequence is formally defined for $n \ge 2$. We return $0$ for $n < 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    let n_real : ℝ := n
    let area : ℝ := n_real / 4 * Real.cot (Real.pi / n_real)
    (Int.floor area).toNat
  else
    0

/--
Conjecture from OEIS A064313, entry %C:
Usually (perhaps always?) $\lfloor n^2/(4\pi) - \pi/12 \rfloor$ for a polygon of circumference $n$.
-/
theorem oeis_64313_conjecture_0 (n : ℕ) (hn : n ≥ 2) :
    a n = (Int.floor ((n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12)).toNat := by
  sorry

theorem oeis_64313_conjecture_0.disproof : ¬ (type_of% @oeis_64313_conjecture_0) := by
  sorry
