import FormalConjectures.Util.ProblemImports

open Nat Finset Complex Real

/--
A363414: $a(n) = (1/2) \cdot \operatorname{Im}\left( \prod_{k = 0}^{n} (1 + k\sqrt{-4}) \right)$.
The sequence values are integers.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Complex :=
    Finset.prod (range (n + 1))
    (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)

  Int.floor (P_n.im / 2)

open Filter Asymptotics ZMod Int


/--
The set of primes of type 2 for A363414 is conjecturally
$\mathbb{P}_2 = \{p \mid p \equiv 1 \pmod 4\}$.
-/
def type_two_primes_conjectured : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ (p : ZMod 4) = 1}

/--
Moll's conjecture 5.5 extends to this sequence:
for the primes of type 2, the p-adic valuation $\nu_p(a(n)) \sim n/(p - 1)$ as $n \to \infty$.
This is formalized using asymptotic equivalence (`~[atTop]`) for the p-adic valuation
(`padicValInt`) converted to a real number.
-/
theorem oeis_363414_conjecture_type2_asymptotics :
  ∀ p : ℕ, Nat.Prime p → p ∈ type_two_primes_conjectured →
  (fun n ↦ (padicValInt p (a n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) / ((p : ℝ) - 1)) := by sorry
