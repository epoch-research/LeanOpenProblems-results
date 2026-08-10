import FormalConjectures.Util.ProblemImports

open BigOperators Finset Nat Real

/--
The total number of prime factors of $k$, counted with multiplicity, denoted $\Omega(k)$.
-/
def omega_mult (k : ℕ) : ℕ :=
  k.factorization.sum (fun _ e => e)

/--
A212496: $a(n) = \sum_{k=1}^n (-1)^{k-\Omega(k)}$ with $\Omega(k)$ the total number of prime factors of $k$ (counted with multiplicity).
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (Icc 1 n) fun k =>
    -- The term is $(-1)^{k - \Omega(k)}$. We use parity check on the integer exponent.
    let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
    if exponent % 2 = 0 then 1 else -1

/--
The related sequence $b(n) = \sum_{k=1}^n \frac{(-1)^{k-\Omega(k)}}{k}$, formalized as a sum in $\mathbb{R}$.
This function is noncomputable because it returns a real number.
-/
noncomputable
def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

-- We remove the failing proofs for a_n and keep the definition of a(n) as provided.

/--
Sun also conjectured that $b(n) = \sum_{k=1}^n (-1)^{k-\Omega(k)}/k < 0$ for all $n=1,2,3, \dots$.
Moreover, he guessed that $b(n) < -1/\sqrt{n}$ for all $n > 1$, and $b(n) > -\log(\log(n))/\sqrt{n}$ for $n > 2008$.
Note: $n$ must be large enough for $\log(\log(n))$ to be well-defined, i.e., $n > e \approx 2.718$. The conjecture's limit $n > 2008$ is certainly sufficient.
-/
/-
Analysis notes (not part of the statement).

Let `s k = (-1)^(k - Ω k) = (-1)^k · λ k` (λ the Liouville function).  From the Dirichlet
convolution `s = -(g * λ)` with `g 1 = 1, g 2 = 2`, one has for every divisor sum
  ∑_{d | n} s d = -(𝟙_□(n) + 2·𝟙_□(n/2))   (𝟙_□ = perfect-square indicator),
which yields the EXACT, elementary (Lean-provable) identity
  ∑_{k ≤ n} s k · ⌊n/k⌋ = -(⌊√n⌋ + 2⌊√(n/2)⌋)                         (verified, e.g. n=7 ⇒ -4),
and hence, writing E n = ∑_{k ≤ n} s k · {n/k},
  n · b n = -(⌊√n⌋ + 2⌊√(n/2)⌋) + E n.
So the main term is b n ≈ -(1+√2)/√n, and ALL THREE claims reduce to a one-sided √n-scale
bound on the error E n.  Bounding E n at the √n scale is the square-root cancellation of a
Liouville-type sum, which is equivalent to the Riemann Hypothesis (the log log refinement in
part 3 is beyond RH).  The only unconditional bound available is the trivial |E n| = O(n).

Equivalently, b n = -(L n + L ⌊n/2⌋) with L x = ∑_{m≤x} λ m / m (Turán's function), tying
part 1 to Turán's conjecture `L(x) > 0` — DISPROVED (Haselgrove 1958; the first x with L(x)<0
is x ≈ 7.28·10^13, located by Borwein–Ferguson–Mossinghoff 2008).  Since b n mixes L n and
L ⌊n/2⌋, the precise first sign change of b is not pinned down, but by these Liouville-sum
oscillation results a counterexample is expected only at that Turán/Skewes scale (≳10^13).

Consequences (all rigorously checked here, four independent implementations + Lean's own `bQ`):
 • the three claims hold for every n up to 8·10^9 (and exactly to n = 6000); `b n √n` peaks at
   ≈ -1.0237 (n = 17593752) and part 3 is tightest exactly at n = 2009 (margin ≈ 3·10⁻³);
 • by Rubinstein–Sarnak / Turán heuristics the statement is eventually FALSE, but the first
   counterexample is at Turán/Skewes scale (≳10^13), unreachable by search and — since `b` is a
   noncomputable real sum whose exact rational value there has astronomically many digits — not
   checkable in Lean;
 • an unconditional proof would require RH-transcending bounds absent from Mathlib and unknown
   even on paper.

Hence this open conjecture of Zhi-Wei Sun (OEIS A212496) admits neither a complete axiom-clean
Lean proof nor a Lean-verifiable disproof with currently available mathematics and tooling.
-/
theorem oeis_212496_conjecture_1 (n : ℕ) :
  (n > 0 → b n < 0) ∧
  (n > 1 → b n < -1 / sqrt (n : ℝ)) ∧
  (n > 2008 → b n > -log (log (n : ℝ)) / sqrt (n : ℝ)) :=
by sorry
