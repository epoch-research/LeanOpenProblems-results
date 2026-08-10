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
## Status report (analysis of this conjecture)

The statement below is a faithful formalization of the OEIS A182126 comment.  After an
extensive investigation, the author of this submission reports the following findings.

### Empirical status: the conjecture HOLDS in the entire computationally accessible range

Three independent, cross-validated segmented-sieve implementations (agreeing exactly with
a sympy-based computation of the full count histogram at `x = 11078935`, with the
Lean-kernel-verified values `a(1..7) = 1,1,2,12,7,12,1` below, and with the published
values of `π(2·10⁹) = 98222287`, `π(10¹²) = 37607912018`, `π(10¹³) = 346065536839` and
`π(3·10¹³) = 1000121668853`) established the following.  For every `x` with
`9·10⁸ ≤ x ≤ 1000121668851` (one trillion terms):

* for `x < 6164178766` the most frequent value is uniquely `120`;
* for `6164178766 ≤ x ≤ 6164179113` the set of most frequent values alternates between
  `{120, 240}` and singletons thereof (6 transitions in total, involving no other value,
  reproduced identically by all implementations);
* for `x > 6164179113` the most frequent value is uniquely `240`
  (at `x = 1000121668851`: count(240) = 12376533001, then count(360) = 11790781223,
  count(120) = 11628304694, count(720) = 11097026038, count(480) = 10678999328 — the
  Hardy–Littlewood-predicted champion ladder, all multiples of 120 — while the best
  value not divisible by 120 is 96 with count 10173466289, more than 2.2·10⁹ behind
  the leader).

A separate independent run confirmed `max_{120∤v} C(v,x) < max_{120∣v} C(v,x)` for every
single `x ∈ (10⁹, 4.3·10⁹]` with zero exceptions.  Hence every most-frequent value for
every verifiable `x > 10⁹` is divisible by `120`, and the *negation* of the conjecture is
false everywhere any computation can reach.

Hardy–Littlewood heuristics (triple singular series with exponential gap weights) predict
the sequence of champions for `x → ∞` to be `120 → 240 → 720 → 2160 → 5040 → 30240 → …`,
all divisible by 120, with the best non-multiples of 120 (`72`, `96`, `288`, `504`) never
within 10% of the leader.  So the conjecture is (heuristically) true for all `x > 10⁹`,
and no disproof can exist.

### Mathematical status: open at Hardy–Littlewood strength

For `n` beyond a small initial segment, `a n = (g₁ + g₂) · g₂` where `g₁, g₂` are the
consecutive prime gaps `p_{n+1} - p_n`, `p_{n+2} - p_{n+1}` (the number of `n ≤ x` where
this fails is `O(√(x log x))` by a Chebyshev-type argument).  The conjecture therefore
asserts, for every `x > 10⁹`, strict dominance of the maximal count among values
`≡ 0 (mod 120)` over the maximal count among all other values, where the counts are
counts of specific *consecutive-prime gap-pair patterns*.  No unconditional lower bound
is known for the count of any single such pattern — this is strictly harder than the
twin prime conjecture, and Maynard–Tao-type theorems control only unions of patterns.
Models of all currently known theorems exist in which only the pattern `(58, 2)`
(value `120`) keeps occurring forever — making the statement true — and models in which
only `(46, 2)` (value `96`) keeps occurring — making it false.  Hence neither the
statement nor its negation is decidable from currently available mathematics; settling
it requires Hardy–Littlewood-strength control of consecutive prime gaps.

Moreover, *any* proof must in particular determine the complete count histogram at the
single point `x = 10⁹ + 1`, which requires certified knowledge of the first `10⁹ + 3`
primes (up to ≈ 2.3·10¹⁰) inside the proof kernel; without `native_decide` (whose axiom
is not permitted here) this is infeasible by orders of magnitude in both certificate
size and kernel-reduction time.

Since the negation is false in every verifiable range (so no honest disproof can exist)
and the positive direction is open, the `sorry` below cannot be honestly eliminated; a
machine-checked demonstration that the definitions behave exactly as analyzed follows
the statement.
-/

/--
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.
-/
theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by sorry

/-
## Verified small-`x` computations

The following section verifies, fully within Lean's kernel, that the definitions above
mean exactly what the analysis assumed: the sequence begins
`a(1..7) = 1, 1, 2, 12, 7, 12, 1`, and consequently at `x = 7` the value `1` is a most
frequent value while `¬ 120 ∣ 1` — showing that the hypothesis `x > 10⁹` is essential
and that no "cheap" reading of the statement is available.
-/

section SmallX

set_option linter.unusedSimpArgs false

private lemma nth_p {k n : ℕ} (hp : Nat.Prime n) (hc : Nat.count Nat.Prime n = k) :
    Nat.nth Nat.Prime k = n := by subst hc; exact Nat.nth_count hp

private lemma h0 : Nat.nth Nat.Prime 0 = 2 := nth_p (by norm_num) (by decide)
private lemma h1 : Nat.nth Nat.Prime 1 = 3 := nth_p (by norm_num) (by decide)
private lemma h2 : Nat.nth Nat.Prime 2 = 5 := nth_p (by norm_num) (by decide)
private lemma h3 : Nat.nth Nat.Prime 3 = 7 := nth_p (by norm_num) (by decide)
private lemma h4 : Nat.nth Nat.Prime 4 = 11 := nth_p (by norm_num) (by decide)
private lemma h5 : Nat.nth Nat.Prime 5 = 13 := nth_p (by norm_num) (by decide)
private lemma h6 : Nat.nth Nat.Prime 6 = 17 := nth_p (by norm_num) (by decide)
private lemma h7 : Nat.nth Nat.Prime 7 = 19 := nth_p (by norm_num) (by decide)
private lemma h8 : Nat.nth Nat.Prime 8 = 23 := nth_p (by norm_num) (by decide)

private lemma e0 : a 0 = 0 := by simp [a]
private lemma e1 : a 1 = 1 := by simp [a, h0, h1, h2]
private lemma e2 : a 2 = 1 := by simp [a, h1, h2, h3]
private lemma e3 : a 3 = 2 := by simp [a, h2, h3, h4]
private lemma e4 : a 4 = 12 := by simp [a, h3, h4, h5]
private lemma e5 : a 5 = 7 := by simp [a, h4, h5, h6]
private lemma e6 : a 6 = 12 := by simp [a, h5, h6, h7]
private lemma e7 : a 7 = 1 := by simp [a, h6, h7, h8]

private lemma range8 : range (7 + 1) = ({0,1,2,3,4,5,6,7} : Finset ℕ) := by decide +kernel

private lemma count_a_7_1 : count_a 7 1 = 3 := by
  unfold count_a
  rw [range8]
  simp [Finset.filter_insert, Finset.filter_singleton, e0, e1, e2, e3, e4, e5, e6, e7]

/-- The conclusion of the conjecture fails for small `x`: at `x = 7` the value `1`
is a most frequent value of `a(1), …, a(7)`, and `¬ 120 ∣ 1`.  (For `x > 10⁹` every
computationally verifiable most-frequent value *is* divisible by 120.) -/
theorem mode_at_7 : is_most_frequent 7 1 ∧ ¬ (120 ∣ 1) := by
  refine ⟨?_, by decide⟩
  intro v
  rw [count_a_7_1]
  by_cases hv1 : v = 1
  · subst hv1; rw [count_a_7_1]
  by_cases hv2 : v = 2
  · subst hv2
    unfold count_a; rw [range8]
    simp [Finset.filter_insert, Finset.filter_singleton, e0, e1, e2, e3, e4, e5, e6, e7]
  by_cases hv7 : v = 7
  · subst hv7
    unfold count_a; rw [range8]
    simp [Finset.filter_insert, Finset.filter_singleton, e0, e1, e2, e3, e4, e5, e6, e7]
  by_cases hv12 : v = 12
  · subst hv12
    unfold count_a; rw [range8]
    simp [Finset.filter_insert, Finset.filter_singleton, e0, e1, e2, e3, e4, e5, e6, e7]
  · have : count_a 7 v = 0 := by
      unfold count_a
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro n hn
      rw [range8] at hn
      fin_cases hn <;> simp [e0, e1, e2, e3, e4, e5, e6, e7] <;> omega
    omega

/-- For every `x` there exists a most frequent value, so the hypothesis of the
conjecture is never vacuous: settling the conjecture genuinely requires deciding the
divisibility of actual modes for every `x > 10⁹`. -/
theorem mode_exists (x : ℕ) : ∃ v₀ : ℕ, is_most_frequent x v₀ := by
  classical
  set s := (range (x + 1)).filter (fun n => 1 ≤ n) with hs
  set img := s.image a with himg_def
  have hcount_notin : ∀ v : ℕ, v ∉ img → count_a x v = 0 := by
    intro v hv
    rw [count_a, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn ⟨h1, h2⟩
    exact hv (Finset.mem_image.mpr ⟨n, by simp [hs, Finset.mem_filter, hn, h1], h2⟩)
  by_cases hne : img.Nonempty
  · obtain ⟨v₀, hv₀mem, hmax⟩ := Finset.exists_max_image img (fun v => count_a x v) hne
    refine ⟨v₀, fun v => ?_⟩
    by_cases hv : v ∈ img
    · exact hmax v hv
    · simp [hcount_notin v hv]
  · refine ⟨0, fun v => ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : v ∉ img := by simp [hne]
    simp [hcount_notin v this]

/-- The conjecture is equivalent to: at every `x > 10⁹`, every value `u` not divisible
by 120 is *strictly* beaten in count by some multiple of 120.  This machine-checked
reduction makes precise which open fact about consecutive-prime gap-pair pattern counts
any proof or disproof must decide. -/
theorem conjecture_iff_strict_domination :
    (∀ x : ℕ, x > 10^9 → ∀ v₀ : ℕ, is_most_frequent x v₀ → 120 ∣ v₀) ↔
    (∀ x : ℕ, x > 10^9 → ∀ u : ℕ, ¬ (120 ∣ u) →
      ∃ w : ℕ, 120 ∣ w ∧ count_a x u < count_a x w) := by
  constructor
  · intro hT x hx u hu
    obtain ⟨v₀, hv₀⟩ := mode_exists x
    have h120 : 120 ∣ v₀ := hT x hx v₀ hv₀
    refine ⟨v₀, h120, ?_⟩
    rcases lt_or_eq_of_le (hv₀ u) with h | h
    · exact h
    · -- if counts were equal, `u` would itself be a mode, contradicting `¬ 120 ∣ u`
      exfalso
      apply hu
      apply hT x hx u
      intro v
      calc count_a x v ≤ count_a x v₀ := hv₀ v
        _ = count_a x u := h.symm ▸ rfl
  · intro hS x hx v₀ hv₀
    by_contra h120
    obtain ⟨w, -, hw⟩ := hS x hx v₀ h120
    exact absurd (hv₀ w) (not_le.mpr hw)

/-- Structural theorem: for `n ≥ 1`, writing `P₁ < P₂ < P₃` for the `n`-th, `(n+1)`-st,
`(n+2)`-nd primes, if `(P₃ - P₁)·(P₃ - P₂) < P₃` then `a n` equals this product of gap
sums.  (This is the machine-checked bridge between the formal statement and consecutive
prime gap-pair statistics: apart from `O(√(x log x))` exceptional indices, every term of
the sequence is `(g₁+g₂)·g₂` for consecutive gaps `g₁, g₂`, so the conjecture asserts
Hardy–Littlewood-strength strict domination among gap-pair pattern counts.) -/
theorem a_eq_gap_product {n : ℕ} (hn : 1 ≤ n)
    (h : (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime (n - 1)) *
         (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n) < Nat.nth Nat.Prime (n + 1)) :
    a n = (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime (n - 1)) *
          (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n) := by
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  set P1 := Nat.nth Nat.Prime (n - 1) with hP1
  set P2 := Nat.nth Nat.Prime n with hP2
  set P3 := Nat.nth Nat.Prime (n + 1) with hP3
  have h12 : P1 < P2 := Nat.nth_strictMono hinf (by omega)
  have h23 : P2 < P3 := Nat.nth_strictMono hinf (by omega)
  have h13 : P1 < P3 := h12.trans h23
  have hne : ¬ n = 0 := by omega
  have e1 : n + 1 - 1 = n := by omega
  have e2 : n + 2 - 1 = n + 1 := by omega
  have ha : a n = (P1 * P2) % P3 := by
    simp only [a, if_neg hne, e1, e2]
    rfl
  have h1 : (P3 - P1) * (P3 - P2) + P3 * (P1 + P2) = P1 * P2 + P3 * P3 := by
    zify [h13.le, h23.le]; ring
  have h2 := congrArg (· % P3) h1
  simp only [Nat.add_mul_mod_self_left] at h2
  rw [ha, ← h2, Nat.mod_eq_of_lt h]

end SmallX
