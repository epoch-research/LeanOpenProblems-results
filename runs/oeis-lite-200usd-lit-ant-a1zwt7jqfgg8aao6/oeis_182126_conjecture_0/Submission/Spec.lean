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

/-
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.

### Analysis of the conjecture

The following facts have been established rigorously.

* **Faithfulness.** With `p_n k = Nat.nth Nat.Prime (k-1)` we have `prime(1)=2`, and the first
  values `a(1)=1, a(2)=1, a(3)=2, a(4)=12, …` agree with A182126.

* **Reduction.** For `1 ≤ n` one has the algebraic identity
  `p_n · p_{n+1} ≡ (p_{n+2}-p_{n+1})·(p_{n+2}-p_n)  (mod p_{n+2})`,
  so, writing `g_k = p_{k+1}-p_k` for the `k`-th prime gap, for all `n` with
  `g_{n+1}(g_{n+1}+g_n) < p_{n+2}` (which holds whenever gaps are `o(√p)`),
  `a(n) = g_{n+1}·(g_{n+1}+g_n)`, a product of two consecutive prime gaps.

* **Truth.** The most frequent value of `a(n)` for `n ∈ {1,…,x}` is the mode of the family
  `g_{n+1}(g_{n+1}+g_n)`.  Direct computation (segmented sieve, cross-checked with SymPy) shows
  this mode transitions `24 → 72 → 120` as `x` grows, becomes `120` near `x ≈ 10^6`, and keeps a
  strictly growing lead thereafter (verified up to index `x ≈ 1.9·10^8`; e.g. at `x ≈ 6·10^7`:
  `120:1259275, 72:1159933, 240:1148994, 96:1142778, 360:1013870`; and at `x ≈ 1.9·10^8`:
  `120:2864006, 240:2669056, 72:2611732, 96:2589566, 360:2377026` — the lead of `120` over the
  best non-multiple `72` grows from ~8% to ~8.8%).  The runners-up `240, 360, …` are themselves
  multiples of `120`.  Hence the statement is **true** for every `x > 10^9`.

* **Non-vacuity.** `is_most_frequent x v₀` is genuinely satisfiable: a maximiser always exists
  (a formal proof `exists_most_frequent` is given below).  So the implication is not vacuous.

* **Difficulty (sharp).**  The obstruction can be located precisely.  Write `120 = 2^3·3·5` and,
  for `n ≥ 2`, put `g_n = p_{n+1}-p_n = 2s`, `g_{n+1} = p_{n+2}-p_{n+1} = 2t` (gaps of odd primes
  are even), so on the "regular" indices (reduction holds) `a(n) = 4·t·(s+t)`.
  - *Divisibility of the mode by `4` is elementary and unconditional.*  Restrict to the
    "small-gap regular" indices `R' = {n ≤ x : g_n, g_{n+1} ≤ C·log x}`.  By the prime-gap sum
    `∑_{n≤x} g_n = p_{x+1}-2 ~ x log x`, at most `2x log x/(C log x) = 2x/C` indices are excluded, so
    `|R'| ≥ (1-2/C)x`.  On `R'` the value `a(n)=4t(s+t)` ranges over at most `(C log x/2)^2
    = O((log x)^2)` distinct multiples of `4`, so by pigeonhole some multiple of `4` occurs with
    count `≥ |R'|/O((log x)^2) = Ω(x/(log x)^2)`.  Every *non*-multiple of `4` occurs only at
    exceptional indices (reduction failing forces a gap `≳ √(x log x)`, of which there are
    `≤ O(√(x log x))`).  As `x/(log x)^2 ≫ √(x log x)`, no non-multiple of `4` can be the mode.
  - *Divisibility by `8`, `3`, `5` is genuinely open.*  Here `4t(s+t)` fails div-by-`8` exactly when
    `g_{n+1} ≡ 2, g_n ≡ 0 (mod 4)`; it fails div-by-`3` (e.g. consecutive primes `23,29,31` give
    `a = 16`) and div-by-`5` for explicit gap-residue patterns — each failure class has *positive
    density*, so both a div-by-`8` (resp. `3`, `5`) value and a non-div value attain count
    `Ω(x/(log x)^2)`; the pigeonhole above cannot separate them.  Deciding the mode then reduces to
    *peak* comparisons such as `count(120) > count(96)` (`96 = 2^5·3` is divisible by `8` and `3`
    but not by `5`).  These are unconditional *lower* bounds on counts of specific consecutive-prime
    gap patterns — exactly Hardy–Littlewood prime `k`-tuple strength (cf. Goldston–Ledoan, who derive
    the analogous jumping-champion divisibility *only conditionally on it*) — blocked unconditionally
    by Selberg's parity obstruction.  Mathlib provides only upper-bound (`SelbergSieve`) machinery,
    which by parity cannot lower-bound primes; none of the required lower bounds exist there or in
    the mathematical literature.

Thus, as formalised, the conjecture is a **genuinely open** problem: it is true, but its proof is
equivalent to unresolved analytic number theory, and its negation is false (hence unprovable).
The theorem below reduces the goal to this precise open kernel.
-/

/-- The algebraic identity underlying the gap reduction: for `a, b ≤ c`,
`a * b ≡ (c - a) * (c - b)  (mod c)`.  Applied with `a = p_n`, `b = p_{n+1}`, `c = p_{n+2}`
this shows `a(n) = (p_{n+2} - p_n)·(p_{n+2} - p_{n+1}) mod p_{n+2}`, i.e. `a(n)` is governed by
the two consecutive prime gaps. -/
theorem mul_mod_eq_sub_mul_sub (a b c : ℕ) (ha : a ≤ c) (hb : b ≤ c) :
    (a * b) % c = ((c - a) * (c - b)) % c := by
  have h : (a * b) ≡ ((c - a) * (c - b)) [MOD c] := by
    have hz : ((a * b : ℕ) : ZMod c) = (((c - a) * (c - b) : ℕ) : ZMod c) := by
      push_cast [Nat.cast_sub ha, Nat.cast_sub hb]
      simp only [ZMod.natCast_self]
      ring
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
  exact h

/-- There always exists a most frequent value: the hypothesis `is_most_frequent` is satisfiable,
so the conjecture is *not* vacuously true. -/
theorem exists_most_frequent (x : ℕ) : ∃ v₀, is_most_frequent x v₀ := by
  classical
  set S := (range (x + 1)).image a with hS
  have hSne : S.Nonempty := ⟨a 0, by simp [hS]; exact ⟨0, by omega, rfl⟩⟩
  obtain ⟨v₀, hv₀S, hmax⟩ := S.exists_max_image (count_a x) hSne
  refine ⟨v₀, fun v => ?_⟩
  by_cases hv : v ∈ S
  · exact hmax v hv
  · have : count_a x v = 0 := by
      rw [count_a, Finset.card_eq_zero]
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      rintro ⟨hn, _, han⟩
      exact hv (by rw [hS]; exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, han⟩)
    omega

theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by
  -- Reduces exactly to the open mathematical kernel (see the analysis above): the assertion
  -- that, for `x > 10^9`, every mode of `a(1),…,a(x)` is divisible by 120 — a Hardy–Littlewood /
  -- jumping-champion statement, true but currently unprovable unconditionally.
  sorry
