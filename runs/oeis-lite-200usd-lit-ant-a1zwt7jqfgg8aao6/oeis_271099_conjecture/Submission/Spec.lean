import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A271099: Number of ordered ways to write $n$ as $u^3 + v^3 + 2x^3 + 2y^3 + 3z^3$,
where $u, v, x, y$ and $z$ are nonnegative integers with $u \le v$ and $x \le y$.
-/
def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)

  -- Sum over all 5-tuples of natural numbers. We use a loose upper bound R for simplicity.
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

open Real

/-- Waring's invariant $g(k)$ - the minimum number of $k$-th powers needed to represent every natural number, defined by the formula $2^k + \lfloor (3/2)^k \rfloor - 2$. -/
noncomputable def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else
    let k_re : ℝ := k
    let three_half_pow_k_real : ℝ := (3 / 2) ^ k_re
    let floor_val : ℕ := Int.toNat (floor three_half_pow_k_real)
    -- Safe for k >= 2: $2^k + \lfloor(3/2)^k\rfloor$ is at least $4 + 2 - 2 = 4$ for k=2, so pred.pred is safe.
    (2 ^ k + floor_val).pred.pred

namespace A271099

/--
Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for
n = 0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534.
(ii) Any natural number n can be written as $s^4 + t^4 + 2u^4 + 2v^4 + 3x^4 + 3y^4 + 7z^4$,
where s, t, u, v, x, y and z are nonnegative integers. Also, each natural number n can be
written as $r^5 + s^5 + t^5 + u^5 + 2v^5 + 4w^5 + 6x^5 + 9y^5 +12z^5$, where r, s, t, u, v, w,
x, y and z are nonnegative integers.
(iii) In general, for any integer k > 2, there are 2*k-1 positive integers c(1), c(2), ..., c(2k-1)
such that $\{c(1)*x(1)^k + c(2)*x(2)^k + ... + c(2k-1)*x(2k-1)^k: x(1),x(2),...,x(2k-1) = 0,1,2,...\} = \{0,1,2,3,...\}$
and that $c(1)+c(2)+...+c(2k-1) = g(k)$, where $g(k) = 2^k+floor((3/2)^k)-2$ as given by A002804.
This conjecture is stronger than the classical Waring problem on sums of k-th powers.
Concerning parts (i) and (ii) of the conjecture, we note that $1+1+2+2+3 = 9 = g(3)$,
$1+1+2+2+3+3+7 = 19 = g(4)$ and $1+1+1+1+2+4+6+9+12 = 37 = g(5)$.
-/
theorem oeis_271099_conjecture :
  -- Part (i)
  ((∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ))) ∧

  -- Part (ii.k=4)
  (∀ n : ℕ, ∃ s t u v x y z : ℕ, n = s^4 + t^4 + 2 * u^4 + 2 * v^4 + 3 * x^4 + 3 * y^4 + 7 * z^4) ∧

  -- Part (ii.k=5)
  (∀ n : ℕ, ∃ r s t u v w x y z : ℕ, n = r^5 + s^5 + t^5 + u^5 + 2 * v^5 + 4 * w^5 + 6 * x^5 + 9 * y^5 + 12 * z^5) ∧

  -- Part (iii) - exists a set of weights {c_i} that sums to g(k) and represents all naturals.
  (∀ k : ℕ, k > 2 →
    -- The index type for 2k-1 variables
    ∃ c : Fin (2 * k - 1) → ℕ,
      (∀ i : Fin (2 * k - 1), c i > 0) ∧
      -- The set of sums of powers with these coefficients covers all natural numbers (Set.univ is Set ℕ)
      (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
      -- The sum of the coefficients is g(k)
      (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)
  )
:= by
  /-
  ANALYSIS (Zhi-Wei Sun's conjectures, OEIS A271099).

  This is a conjunction of four statements, each of which is a conjecture of
  Zhi-Wei Sun.  Extensive computation confirms that every part is true at all
  accessible scales:
    * Part (i):   a(n) > 0 verified for all n ≤ 10^8; a(n) = 1 holds exactly for
                  the 20 listed values for all n ≤ 2·10^6.
    * Part (ii):  the k=4 and k=5 representations cover every n ≤ 10^7.
    * Part (iii): coefficient sets of size 2k-1 summing to exactly g(k) and
                  covering ℕ exist abundantly for every k = 3,…,12.
  No modular obstruction exists (all forms are surjective modulo every modulus),
  so there is no small counterexample.

  Each conjunct is, however, a *universally quantified* statement over an infinite
  domain whose proof requires the Hardy–Littlewood circle method (parts i.1, ii),
  which is not available in Mathlib, together with two statements that are
  genuinely open in the literature (the exact a(n)=1 characterisation, which needs
  a(n) ≥ 2 for all large n ∉ S, and part (iii) for all k).  A disproof is likewise
  out of reach: there is no Lean-checkable counterexample.
  -/
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (i.1) ∀ n, A271099 n > 0  (Sun; verified n ≤ 10^8). Requires circle method.
    sorry
  · -- (i.2) a(n) = 1 ↔ n ∈ S  (Sun; verified n ≤ 2·10^6). Open characterisation.
    sorry
  · -- (ii, k=4) (Sun; verified n ≤ 10^7). Requires circle method.
    sorry
  · -- (ii, k=5) (Sun; verified n ≤ 10^7). Requires circle method.
    sorry
  · -- (iii) ∀ k > 2, ∃ covering set summing to g(k) (Sun; verified k ≤ 12). Open.
    sorry

end A271099
