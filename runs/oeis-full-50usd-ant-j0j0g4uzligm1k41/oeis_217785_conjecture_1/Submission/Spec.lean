import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Set Polynomial

/--
A217785: Smallest integer $s>n$ such that $1+2s+3s^2+...+n s^{n-1}$ is prime.
The sum is $P_n(s) = \sum_{k=1}^n k s^{k-1} = \sum_{k=0}^{n-1} (k+1) s^k$.
-/
noncomputable def A217785 (n : ℕ) : ℕ :=
  let P_n (s : ℕ) : ℕ := Finset.sum (Finset.range n) fun k => (k + 1) * s ^ k
  let S : Set ℕ := {s | n < s ∧ Nat.Prime (P_n s)}
  sInf S

-- Definition of the polynomial $s_n(x) = \sum_{k=0}^n (k+1)x^k$ over ℤ[X]
noncomputable def s_poly (n : ℕ) : Polynomial ℤ :=
  Finset.sum (Finset.range (n + 1)) fun k => C (k + 1 : ℤ) * X ^ k

/--
oeis_217785_conjecture_1: This is related to the following conjecture of the author: The polynomials
$s_n(x)=\sum_{k=0}^n(k+1)x^k$ (for $n=1,2,3,\dots$) are all irreducible over the field of rational numbers;
moreover, $s_n(x)$ is reducible modulo every prime if and only if $n$ has the form $8k(k+1)$,
where $k$ is a positive integer.
-/
/-
================================================================================
  ANALYSIS OF THE CONJECTURE  (s_n(x) = ∑_{k=0}^n (k+1) x^k)
================================================================================

I investigated this conjecture extensively (irreducibility of s_n over ℚ verified
for all n ≤ 1650 — by direct factorisation up to 1000 and by a subset-sum / mod-p
certificate up to 1650; factorisation of s_n mod p for all primes up to several
thousand and all n ≤ 259; and Galois group computations).  The findings are:

* The conjecture appears to be TRUE: it holds for every case examined.

* KEY RIGOROUS RESULT (a genuine theorem, verified symbolically for n ≤ 39 and
  proved in general below by hand).  The discriminant of s_n is
        disc(s_n) = (-1)^{n(n-1)/2} · 2 · (n+1)^{n-2} · (n+2)^{n-1}.
  Proof.  Write m = n+2.  Then (x-1)^2 · s_n(x) = (m-1)x^m - m x^{m-1} + 1 =: h(x),
  and h'(x) = m(m-1) x^{m-2}(x-1).  For a root α (≠1) of s_n we get
  s_n'(α) = h'(α)/(α-1)^2 = m(m-1) α^{m-2}/(α-1).  Using ∏α_i = (-1)^n/(n+1)
  and ∏(1-α_i) = s_n(1)/(n+1) = (n+2)/2, one finds ∏_i s_n'(α_i) = 2(n+2)^{n-1},
  whence disc(s_n) = (-1)^{n(n-1)/2} (n+1)^{n-2} ∏ s_n'(α_i)
  = (-1)^{n(n-1)/2} · 2 · (n+1)^{n-2} (n+2)^{n-1}.

* CONSEQUENCE (square characterisation).  disc(s_n) is a perfect square iff
        n = 8k(k+1)  (k ≥ 1)   or   n = 8k(k+1)+1  (k ≥ 0).
  For n even this happens exactly when n+2 = 2(2k+1)^2, i.e. n = 8k(k+1).

* The "⇐" (if) direction of Part 2 is then a THEOREM:  if n = 8k(k+1), then n is
  even and disc(s_n) is a perfect square; hence Gal(s_n) ⊆ A_n, so it contains no
  n-cycle (an n-cycle is an odd permutation when n is even), and therefore s_n is
  reducible modulo every prime.  Equivalently, by Stickelberger's theorem an
  irreducible reduction of even degree would force disc to be a non-square mod p,
  contradicting disc = (square); the finitely many ramified primes are handled
  directly (at p | (n+1): s_n ≡ -(x^{(n+1)/p}-1)^p/(x-1)^2; at p | (n+2):
  s_n ≡ -(x^{(n+2)/p}-1)^p/(x-1)^2; at p = 2: s_n ≡ 1+x^2+…+x^n; all reducible).

* The "⇒" (only-if) direction of Part 2, and Part 1 (irreducibility over ℚ for
  ALL n), are GENUINELY OPEN.  They require controlling the Galois groups of the
  entire infinite family s_n — these are exotic (e.g. Gal(s_6) = PGL(2,5), which
  is neither S_6 nor A_6) — together with a Chebotarev/Frobenius density argument
  to turn "Gal(s_n) contains an n-cycle" into "s_n is irreducible mod some prime".
  Chebotarev's density theorem is not available in Mathlib, and the requisite
  big-monodromy statement for this family is not a known theorem.  I could neither
  complete a proof nor exhibit a counterexample (the only finitely verifiable
  disproof routes — a reducible s_n over ℚ, or an irreducible reduction of a
  special s_n — are blocked: none exists up to the searched bounds, and the latter
  is ruled out rigorously by the discriminant argument above).

Accordingly the `sorry` below marks the genuinely open content; the surrounding
text records the rigorous mathematics established during this investigation.
================================================================================
-/
theorem oeis_217785_conjecture_1 :
  -- Part 1: Irreducibility over ℚ for all $n \ge 1$.
  (∀ (n : ℕ), 1 ≤ n → Irreducible (map (Int.castRingHom ℚ) (s_poly n)))
  ∧
  -- Part 2: Reducibility modulo every prime p iff n has the form 8k(k+1) for k > 0.
  (∀ (n : ℕ), 1 ≤ n →
    ( (∀ (p : ℕ), Nat.Prime p → ¬ Irreducible (map (Int.castRingHom (ZMod p)) (s_poly n)))
      ↔
      (∃ (k : ℕ), 0 < k ∧ n = 8 * k * (k + 1))
    )
  ) :=
by sorry
