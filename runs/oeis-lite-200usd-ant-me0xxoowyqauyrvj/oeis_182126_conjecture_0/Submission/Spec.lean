import FormalConjectures.Util.ProblemImports

open Nat
open Finset

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

/--
Let $C(v, x)$ be the number of times $v$ appears in the sequence $a(1), a(2), \ldots, a(x)$.
$C(v, x) = |\{ n \in \{1, \dots, x\} : a(n) = v \}|$.
-/
noncomputable def count_a (x v : ℕ) : ℕ :=
  -- The index set is {1, 2, ..., x}. We use range (x+1) which is {0, ..., x} and filter by 1 ≤ n.
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/--
A value $v₀$ is a most frequent value in $a(1), \ldots, a(x)$ if its count is greater
than or equal to the count of every other value $v$.
-/
def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

/--
The crux of the conjecture, isolated as a lemma.

For `x > 10^9`, the value `120` strictly out-occurs every value `v` that is **not**
a multiple of `120` among `a(1), …, a(x)`.

This is the genuine mathematical content of the OEIS A182126 conjecture.  It is a
statement comparing the counts of distinct prime *constellations*: writing
`a(n) = (p_{n+2}-p_{n+1})·(p_{n+2}-p_n)` (valid once `n` is large), the events
`a(n) = 120` and `a(n) = v` correspond to admissible prime triples of fixed shapes
(e.g. `a(n)=120` ⇐ triples `p, p+2, p+12`; `a(n)=72` ⇐ triples `p, p+6, p+12`),
whose asymptotic densities are governed by the Hardy–Littlewood prime `k`-tuple
conjecture.  Numerical evidence is overwhelming (value `120` leads with a growing
margin, and the entire top of the empirical distribution `120, 240, 360, …` consists
of multiples of `120`), and all "crossovers" with competing non-multiples such as
`72`, `96` occur well below `10^9`.  A *rigorous* proof, however, requires
unconditional lower bounds on counts of prime constellations, which are currently
out of reach (the parity obstruction in sieve theory). -/
theorem count_120_dominates
    (x : ℕ) (_hx : x > 10 ^ 9) (v : ℕ) (_hv : ¬ (120 ∣ v)) :
    count_a x v < count_a x 120 := by
  sorry

/--
Conjecture: for `x > 10^9`, the most frequent value in `a(n)`, `n = 1 … x`, has the
form `120 · k`.

The statement reduces, via `count_120_dominates`, to the density-dominance of the
value `120`: a maximizer that were *not* a multiple of `120` would be out-counted by
`120` itself, contradicting maximality. -/
theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by
  intro x hx v₀ hmf
  by_contra hnd
  -- A non-multiple of 120 is strictly out-counted by 120 …
  have hdom : count_a x v₀ < count_a x 120 := count_120_dominates x hx v₀ hnd
  -- … yet a maximizer's count is `≥` that of every value, in particular `120`.
  have h120 : count_a x v₀ ≥ count_a x 120 := hmf 120
  omega
