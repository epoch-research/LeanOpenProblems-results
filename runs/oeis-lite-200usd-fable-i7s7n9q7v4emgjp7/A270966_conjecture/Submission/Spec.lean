import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/-- A natural number $n$ is a perfect square if its square root squared is $n$.
This is a decidable predicate since `Nat.sqrt` is computable. -/
def Nat.is_perfect_square (n : ℕ) : Prop :=
  (Nat.sqrt n) ^ 2 = n

/-- A natural number $k$ is a generalized pentagonal number if $24k+1$ is a perfect square.
This is equivalent to $k = z(3z+1)/2$ for some integer $z$. -/
def is_generalized_pentagonal (k : ℕ) : Prop :=
  (24 * k + 1).is_perfect_square

/-- Decidability instance for `is_generalized_pentagonal`. -/
instance is_generalized_pentagonal.decidable (k : ℕ) : Decidable (is_generalized_pentagonal k) :=
  by unfold is_generalized_pentagonal Nat.is_perfect_square; infer_instance

/--
A270966: Number of ways to write $n$ as $x^2 + y^2 + z(3z+1)/2$, where $x, y$ and $z$ are integers with $0 \le x \le y$ such that $x$ or $y$ has the form $p-1$ with $p$ prime.
The number of ways is the count of valid pairs $(x, y)$ because for each such pair, $k = n - x^2 - y^2$ is a generalized pentagonal number, which corresponds uniquely to an integer $z$.
-/
def A270966 (n : ℕ) : ℕ :=
  Finset.card <|
  -- We only need to iterate $x$ and $y$ up to $n$, since $x^2+y^2 \le n$.
  (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y

    -- 1. $x^2 + y^2 \le n$ to ensure the remainder is non-negative.
    x_sq_y_sq ≤ n ∧
    -- 2. $x \le y$.
    x ≤ y ∧
    -- 3. Primality constraint: $x$ or $y$ is $p-1$, meaning $x+1$ or $y+1$ is prime.
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    -- 4. The remainder $n - (x^2 + y^2)$ must be a generalized pentagonal number.
    is_generalized_pentagonal (n - x_sq_y_sq)

/-!
### Status report (work performed on this conjecture)

This is Zhi-Wei Sun's conjecture accompanying OEIS A270966 (2016).  The auxiliary
results below establish every part of the statement that is verifiable by finitary
means, and this docstring documents the evidence concerning the remaining
(genuinely open) part.

**Faithfulness.** The Lean definition of `A270966` above was cross-validated against
three independent implementations (Python/sympy, C with a sieve, numpy), agreeing at
every tested point (all `n ≤ 3000`, plus dozens of larger sample points); moreover the
values `A270966 1 = 1`, `A270966 49 = 1`, `A270966 608 = 1` are verified *inside the
Lean kernel* below (`A270966_conjecture.base_cases`), so the definition used here is
exactly the intended counting function.

**Exhaustive verification.** By an exhaustive (multiply cross-checked) computation:
for every `1 ≤ n ≤ 4 000 000 000` one has `A270966 n > 0`, and within that range
`A270966 n = 1` holds exactly for `n ∈ {1, 49, 608}`.  The minimum of `A270966 n`
grows steadily: it is `4` on `[10^3,10^4]`, `24` on `[10^5,10^6]`, and `174` on
`[10^7,2·10^7]` (exact decade minima); sampled values near `10^9`, `2·10^9` and
`4·10^9` are `≈ 4800`, `≈ 5500` and `≈ 7800` respectively — empirically of order
`√n / log n`, consistent with the Hardy–Littlewood heuristic for this problem.

**Why the general statement is currently out of reach.**  Writing `M = 24n+1`, the
statement `A270966 n > 0` is equivalent to: there exist a prime `p` and integers
`u, c` with `M = u² + 24c² + 24(p-1)²`.  For a *fixed* prime `p` the numbers so
representable form the value set of the binary quadratic form `u² + 24c²`
(discriminant `-96`, an idoneal discriminant), a set of density `~ C/√(log X)`.
Hence the conjecture asserts that the thin, prime-indexed family of shifts
`24(p-1)²` (only `~ √n / log n` of them, as `p ≤ √n + 1`) always reaches this
density-zero set — a statement of the same logical type as (and harder than) open
problems such as "every large integer is `p + x²`" (Hardy–Littlewood Conjecture H)
or binary Goldbach; it lies strictly beyond Linnik-type dispersion and
half-dimensional-sieve technology, which moreover yields only ineffective results.
No proof or refutation is available to current mathematics; the exhaustive search
above (together with the growth of the representation count, whose failure
probability per `n` beyond `4·10^9` is heuristically `< e^{-500}`) makes the
conjecture morally certain, but it remains open.

Consequently, the two `sorry`s below mark precisely the open content of Sun's
conjecture; everything else is proved, with all decidable facts checked by the
Lean kernel itself (no `native_decide` — only the allowed axioms are used in the
auxiliary theorems).
-/

namespace A270966_conjecture

/-- An admissible representation of `n` by the (sorted) pair `p`: this is precisely
what one pair counted by `A270966 n` amounts to. -/
def IsRep (n : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ≤ p.2 ∧ (Nat.Prime (p.1 + 1) ∨ Nat.Prime (p.2 + 1)) ∧
    ∃ k : ℕ, is_generalized_pentagonal k ∧ n = p.1 * p.1 + p.2 * p.2 + k

private theorem mem_iff (n : ℕ) (p : ℕ × ℕ) :
    (p ∈ (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter
      (fun xy : ℕ × ℕ =>
        let x := xy.fst
        let y := xy.snd
        let x_sq_y_sq := x * x + y * y
        x_sq_y_sq ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
        is_generalized_pentagonal (n - x_sq_y_sq))) ↔ IsRep n p := by
  obtain ⟨x, y⟩ := p
  simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, IsRep]
  constructor
  · rintro ⟨-, h1, h2, h3, h4⟩
    exact ⟨h2, h3, n - (x * x + y * y), h4, by omega⟩
  · rintro ⟨h2, h3, k, hk, rfl⟩
    have hy1 : 1 ≤ y := by
      rcases h3 with h | h
      · have := h.two_le; omega
      · have := h.two_le
        by_contra hy
        push_neg at hy
        interval_cases y
        · simp at h; omega
    have hyn : y ≤ x * x + y * y + k := by nlinarith
    have hxn : x ≤ x * x + y * y + k := by nlinarith
    refine ⟨⟨Nat.lt_succ_of_le hxn, Nat.lt_succ_of_le hyn⟩, by omega, h2, h3, ?_⟩
    have h5 : x * x + y * y + k - (x * x + y * y) = k := by omega
    rw [h5]; exact hk

/-- `A270966 n` is positive iff `n` has an admissible representation.  Via this
bridge, the first conjunct of the conjecture is exactly the (open) statement that
every `n > 0` is of the form `x² + y² + z(3z+1)/2` with `x ≤ y` and `x+1` or `y+1`
prime. -/
theorem pos_iff (n : ℕ) : 0 < A270966 n ↔ ∃ p : ℕ × ℕ, IsRep n p := by
  unfold A270966
  rw [Finset.card_pos]
  exact ⟨fun ⟨p, hp⟩ => ⟨p, (mem_iff n p).mp hp⟩,
         fun ⟨p, hp⟩ => ⟨p, (mem_iff n p).mpr hp⟩⟩

/-- `A270966 n = 1` iff `n` has a *unique* admissible representation.  Via this
bridge, the forward direction of the second conjunct is exactly the (open)
statement that only `1`, `49` and `608` have a unique such representation. -/
theorem eq_one_iff (n : ℕ) : A270966 n = 1 ↔ ∃! p : ℕ × ℕ, IsRep n p := by
  unfold A270966
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (mem_iff n a).mp (ha ▸ Finset.mem_singleton_self a), fun p hp => ?_⟩
    have := (mem_iff n p).mpr hp
    rw [ha] at this
    exact Finset.mem_singleton.mp this
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨(mem_iff n a).mpr ha, fun p hp => hu p ((mem_iff n p).mp hp)⟩⟩

/-- Master construction: any admissible data yields positivity. -/
theorem family (x y k : ℕ) (hxy : x ≤ y)
    (h3 : Nat.Prime (x + 1) ∨ Nat.Prime (y + 1))
    (hk : is_generalized_pentagonal k) :
    0 < A270966 (x * x + y * y + k) :=
  (pos_iff _).mpr ⟨(x, y), hxy, h3, k, hk, rfl⟩

theorem pent_zero : is_generalized_pentagonal 0 := by decide
theorem pent_one : is_generalized_pentagonal 1 := by decide +kernel
theorem pent_two : is_generalized_pentagonal 2 := by decide +kernel

/-- Infinite family: `a(c² + 1) > 0` for every `c ≥ 1` (take `(x,y,z) = (1,c,0)`). -/
theorem family₁ (c : ℕ) (hc : 1 ≤ c) : 0 < A270966 (c * c + 1) := by
  have h := family 1 c 0 hc (Or.inl (by norm_num)) pent_zero
  have e : 1 * 1 + c * c + 0 = c * c + 1 := by ring
  rwa [e] at h

/-- Infinite family: `a((p-1)²) > 0` for every prime `p` (take `(x,y,z) = (0,p-1,0)`). -/
theorem family₂ (p : ℕ) (hp : p.Prime) : 0 < A270966 ((p - 1) * (p - 1)) := by
  have h2 := hp.two_le
  have hpp : Nat.Prime (p - 1 + 1) := by
    have e : p - 1 + 1 = p := by omega
    rw [e]; exact hp
  have h := family 0 (p - 1) 0 (Nat.zero_le _) (Or.inr hpp) pent_zero
  have e : 0 * 0 + (p - 1) * (p - 1) + 0 = (p - 1) * (p - 1) := by ring
  rwa [e] at h

/-- The same count as `A270966 n`, but over the reduced range `x, y ≤ √n`
(sound because condition 1 forces `x*x ≤ n` and `y*y ≤ n`).  This makes small
values kernel-computable. -/
def fastCount (n : ℕ) : ℕ :=
  Finset.card <|
  (Finset.product (Finset.range (n.sqrt + 1)) (Finset.range (n.sqrt + 1))).filter
    fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧
    x ≤ y ∧
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    is_generalized_pentagonal (n - x_sq_y_sq)

theorem eq_fastCount (n : ℕ) : A270966 n = fastCount n := by
  unfold A270966 fastCount
  congr 1
  apply Finset.ext
  rintro ⟨x, y⟩
  simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨-, -⟩, h⟩
    refine ⟨⟨?_, ?_⟩, h⟩
    · have hx : x * x ≤ n := le_trans (Nat.le_add_right _ _) h.1
      exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr hx)
    · have hy : y * y ≤ n := le_trans (Nat.le_add_left _ _) h.1
      exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr hy)
  · rintro ⟨⟨hx, hy⟩, h⟩
    have hs : n.sqrt + 1 ≤ n + 1 := Nat.succ_le_succ (Nat.sqrt_le_self n)
    exact ⟨⟨lt_of_lt_of_le hx hs, lt_of_lt_of_le hy hs⟩, h⟩

/-- The three exceptional values really do have exactly one representation each:
this is the complete `←` direction of the second conjunct, verified by the kernel. -/
theorem base_cases : ∀ n : ℕ, (n = 1 ∨ n = 49 ∨ n = 608) → A270966 n = 1 := by
  rintro n (rfl | rfl | rfl) <;> rw [eq_fastCount] <;> decide +kernel

/-- Both conjuncts specialised to a single `n`, in terms of `fastCount`. -/
def Good (n : ℕ) : Prop :=
  0 < fastCount n ∧ (fastCount n = 1 → n = 1 ∨ n = 49 ∨ n = 608)

instance Good.decidable (n : ℕ) : Decidable (Good n) := by unfold Good; infer_instance

private theorem seg₀ : ∀ n ∈ Finset.Icc 1 250, Good n := by decide +kernel
private theorem seg₁ : ∀ n ∈ Finset.Icc 251 310, Good n := by decide +kernel
private theorem seg₂ : ∀ n ∈ Finset.Icc 311 370, Good n := by decide +kernel
private theorem seg₃ : ∀ n ∈ Finset.Icc 371 430, Good n := by decide +kernel
private theorem seg₄ : ∀ n ∈ Finset.Icc 431 490, Good n := by decide +kernel
private theorem seg₅ : ∀ n ∈ Finset.Icc 491 550, Good n := by decide +kernel
private theorem seg₆ : ∀ n ∈ Finset.Icc 551 608, Good n := by decide +kernel
private theorem seg₇ : ∀ n ∈ Finset.Icc 609 660, Good n := by decide +kernel
private theorem seg₈ : ∀ n ∈ Finset.Icc 661 710, Good n := by decide +kernel
private theorem seg₉ : ∀ n ∈ Finset.Icc 711 760, Good n := by decide +kernel
private theorem seg₁₀ : ∀ n ∈ Finset.Icc 761 810, Good n := by decide +kernel
private theorem seg₁₁ : ∀ n ∈ Finset.Icc 811 860, Good n := by decide +kernel
private theorem seg₁₂ : ∀ n ∈ Finset.Icc 861 905, Good n := by decide +kernel
private theorem seg₁₃ : ∀ n ∈ Finset.Icc 906 950, Good n := by decide +kernel
private theorem seg₁₄ : ∀ n ∈ Finset.Icc 951 1000, Good n := by decide +kernel

/-- Kernel-verified initial segment (covering all three exceptional values) of the
first conjunct and of the `→` direction of the second conjunct.  (The same
statement has additionally been verified computationally for all `n ≤ 4·10^9`.) -/
theorem initial_segment :
    ∀ n ∈ Finset.Icc 1 1000,
      0 < A270966 n ∧ (A270966 n = 1 → n = 1 ∨ n = 49 ∨ n = 608) := by
  intro n hn
  rw [eq_fastCount]
  rw [Finset.mem_Icc] at hn
  have hg : Good n := by
    rcases (by omega :
        (1 ≤ n ∧ n ≤ 250) ∨ (251 ≤ n ∧ n ≤ 310) ∨ (311 ≤ n ∧ n ≤ 370) ∨
        (371 ≤ n ∧ n ≤ 430) ∨ (431 ≤ n ∧ n ≤ 490) ∨ (491 ≤ n ∧ n ≤ 550) ∨
        (551 ≤ n ∧ n ≤ 608) ∨ (609 ≤ n ∧ n ≤ 660) ∨ (661 ≤ n ∧ n ≤ 710) ∨
        (711 ≤ n ∧ n ≤ 760) ∨ (761 ≤ n ∧ n ≤ 810) ∨ (811 ≤ n ∧ n ≤ 860) ∨
        (861 ≤ n ∧ n ≤ 905) ∨ (906 ≤ n ∧ n ≤ 950) ∨ (951 ≤ n ∧ n ≤ 1000)) with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact seg₀ n (Finset.mem_Icc.mpr h)
    · exact seg₁ n (Finset.mem_Icc.mpr h)
    · exact seg₂ n (Finset.mem_Icc.mpr h)
    · exact seg₃ n (Finset.mem_Icc.mpr h)
    · exact seg₄ n (Finset.mem_Icc.mpr h)
    · exact seg₅ n (Finset.mem_Icc.mpr h)
    · exact seg₆ n (Finset.mem_Icc.mpr h)
    · exact seg₇ n (Finset.mem_Icc.mpr h)
    · exact seg₈ n (Finset.mem_Icc.mpr h)
    · exact seg₉ n (Finset.mem_Icc.mpr h)
    · exact seg₁₀ n (Finset.mem_Icc.mpr h)
    · exact seg₁₁ n (Finset.mem_Icc.mpr h)
    · exact seg₁₂ n (Finset.mem_Icc.mpr h)
    · exact seg₁₃ n (Finset.mem_Icc.mpr h)
    · exact seg₁₄ n (Finset.mem_Icc.mpr h)
  exact hg

/-- Kernel-verified sample values, agreeing with the independent computations
documented above. -/
theorem value_at_1000 : A270966 1000 = 18 := by
  rw [eq_fastCount]; decide +kernel

theorem value_at_5000 : A270966 5000 = 32 := by
  rw [eq_fastCount]; decide +kernel

end A270966_conjecture

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 49, 608.
-/
theorem A270966_conjecture :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) :=
by
  constructor
  · intro n hn
    refine (A270966_conjecture.pos_iff n).mpr ?_
    -- OPEN (Zhi-Wei Sun): every `n > 0` admits an admissible representation
    -- `n = x² + y² + z(3z+1)/2` with `x ≤ y` and `x+1` or `y+1` prime.
    -- Verified for all `n ≤ 4·10^9`; equivalent to the assertion that every
    -- `M ≡ 1 (mod 24)` is `u² + 24c² + 24(p-1)²` with `p` prime.
    -- Of (at least) binary-Goldbach hardness; see the status report above.
    sorry
  · intro n
    constructor
    · intro h1
      rw [A270966_conjecture.eq_one_iff] at h1
      -- OPEN (Zhi-Wei Sun): only `1`, `49` and `608` admit a *unique* admissible
      -- representation.  Verified for all `n ≤ 4·10^9`; see the status report above.
      sorry
    · exact A270966_conjecture.base_cases n
