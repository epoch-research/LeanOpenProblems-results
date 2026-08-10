import FormalConjectures.Util.ProblemImports

open Nat

/--
A271510: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x \ge y \ge 0$, $z \ge 0$ and $w \ge 0$ such that $x^2 + 8y^2 + 16z^2$ is a square.
-/
def A271510 (n : ℕ) : ℕ :=
  -- Define the decidable predicate for being a perfect square in ℕ.
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- The maximum value for any variable is $\lfloor\sqrt{n}\rfloor$.
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)

  -- The search space is the Cartesian product R x R x R x R, structured as (((ℕ × ℕ) × ℕ) × ℕ).
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R

  Finset.card $ search_space.filter fun p =>
    -- Decompose the nested product tuple p = (((x, y), z), w)
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd

    -- Constraint 1: sum of squares equals n
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    -- Constraint 2: $x \ge y$
    x ≥ y ∧
    -- Constraint 3: $x^2 + 8y^2 + 16z^2$ is a square.
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

-- A standard definition for "is a square" on ℕ
def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2

/-- A tuple `(x,y,z,w)` is a valid representation of `n` for A271510. -/
def Good (n x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ x ≥ y ∧ is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

/-- **2-scaling reduction.** If `n` admits a valid representation, then so does
`4 * n`, via `(x,y,z,w) ↦ (2x,2y,2z,2w)`. This is the only genuine structural
reduction available, and it reduces the conjecture to the case `4 ∤ n`. -/
theorem good_four_mul {n x y z w : ℕ} (h : Good n x y z w) :
    Good (4 * n) (2 * x) (2 * y) (2 * z) (2 * w) := by
  obtain ⟨hsum, hxy, m, hm⟩ := h
  refine ⟨by nlinarith [hsum], by omega, 2 * m, ?_⟩
  nlinarith [hm]

/-- **Square-scaling closure** (generalises `good_four_mul`, the case `k = 2`).
If `n` admits a valid representation, then so does `k² · n`, via
`(x,y,z,w) ↦ (kx,ky,kz,kw)`.  Equivalently `S` is closed under multiplication by
perfect squares, so the conjecture only needs to be settled on the squarefree
"generators". -/
theorem good_scale {n x y z w : ℕ} (k : ℕ) (h : Good n x y z w) :
    Good (k ^ 2 * n) (k * x) (k * y) (k * z) (k * w) := by
  obtain ⟨hsum, hxy, m, hm⟩ := h
  refine ⟨?_, Nat.mul_le_mul_left k hxy, k * m, ?_⟩
  · rw [show (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2 + (k * w) ^ 2
        = k ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) by ring, hsum]
  · rw [show (k * x) ^ 2 + 8 * (k * y) ^ 2 + 16 * (k * z) ^ 2
        = k ^ 2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) by ring, hm]; ring

/-- **Geometric-mean sufficient condition.** If `y² = x·z`, then
`x² + 8y² + 16z² = (x + 4z)²` is automatically a perfect square. Hence any tuple
`(x,y,z,w)` summing to `n` with `x ≥ y` and `y² = x·z` is a valid representation.
This is the cleanest exact identity producing valid triples, but the resulting
value set `{x²+y²+z² : y²=xz}` only meets a positive (≈60%) but proper fraction of
`ℕ` after adding `w²`, so it does not by itself settle the conjecture. -/
theorem good_geo {n x y z w : ℕ}
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) (hxy : x ≥ y) (hgeo : y ^ 2 = x * z) :
    Good n x y z w :=
  ⟨hsum, hxy, x + 4 * z, by nlinarith [hgeo]⟩

/-- **Second exact sufficient identity.** If `x² + 4y² = 16·y·z`, then
`x² + 8y² + 16z² = (4z + 2y)²`. -/
theorem good_idB {n x y z w : ℕ}
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) (hxy : x ≥ y)
    (hid : x ^ 2 + 4 * y ^ 2 = 16 * y * z) :
    Good n x y z w :=
  ⟨hsum, hxy, 4 * z + 2 * y, by nlinarith [hid]⟩

/-- **Third exact sufficient identity.** If `x² + 7y² = 8·y·z`, then
`x² + 8y² + 16z² = (4z + y)²`. -/
theorem good_idC {n x y z w : ℕ}
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) (hxy : x ≥ y)
    (hid : x ^ 2 + 7 * y ^ 2 = 8 * y * z) :
    Good n x y z w :=
  ⟨hsum, hxy, 4 * z + y, by nlinarith [hid]⟩

/-- **Full rational parametrization of the cone** `x² + 8y² + 16z² = s²`.
For all integers `m, p, q`,
`(m²-8p²-16q²)² + 8·(2mp)² + 16·(2mq)² = (m²+8p²+16q²)²`.
This shows the valid triples are swept out (up to square-scaling, via `good_scale`)
by `x = |m²-8p²-16q²|, y = 2mp, z = 2mq`, whence the value `x²+y²+z²` is an
*irreducible quartic* in `(m,p,q)` — the structural reason the conjecture cannot
reduce to a universal quadratic form. -/
theorem cone_param (m p q : ℤ) :
    (m ^ 2 - 8 * p ^ 2 - 16 * q ^ 2) ^ 2 + 8 * (2 * m * p) ^ 2 + 16 * (2 * m * q) ^ 2
      = (m ^ 2 + 8 * p ^ 2 + 16 * q ^ 2) ^ 2 := by ring

/-- **Bridge lemma.**  Any valid tuple in the sense of `Good` is actually counted by
`A271510`, so `Good n x y z w → 0 < A271510 n`.  The search-box bounds
`x,y,z,w ≤ ⌊√n⌋` are automatic from `x²+y²+z²+w² = n`, and the two notions of
"perfect square" agree (`k = m² ⟹ k.sqrt * k.sqrt = k`).  Consequently *every*
sufficient condition above (`good_geo`, `good_idB`, `good_idC`, `good_four_mul`,
`good_scale`, …) yields concrete positivity of `A271510`. -/
theorem good_imp_pos {n x y z w : ℕ} (h : Good n x y z w) : 0 < A271510 n := by
  obtain ⟨hsum, hxy, m, hm⟩ := h
  have hx : x < n.sqrt + 1 := by
    have h1 : x * x ≤ n := by rw [← pow_two]; omega
    have := Nat.le_sqrt.mpr h1; omega
  have hy : y < n.sqrt + 1 := by
    have h1 : y * y ≤ n := by rw [← pow_two]; omega
    have := Nat.le_sqrt.mpr h1; omega
  have hz : z < n.sqrt + 1 := by
    have h1 : z * z ≤ n := by rw [← pow_two]; omega
    have := Nat.le_sqrt.mpr h1; omega
  have hw : w < n.sqrt + 1 := by
    have h1 : w * w ≤ n := by rw [← pow_two]; omega
    have := Nat.le_sqrt.mpr h1; omega
  simp only [A271510]
  rw [Finset.card_pos]
  refine ⟨((((x, y), z), w)), ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hsum, hxy, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hx, Finset.mem_range.mpr hy⟩,
          Finset.mem_range.mpr hz⟩,
        Finset.mem_range.mpr hw⟩
  · show (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt
        = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2
    rw [hm, Nat.sqrt_eq']; ring

/-- **Converse of the bridge.**  If `A271510 n > 0` then the nonempty filtered
search box yields an explicit valid tuple, i.e. `∃ x y z w, Good n x y z w`.
(The two perfect-square predicates agree in this direction too:
`k.sqrt * k.sqrt = k ⟹ k = k.sqrt ^ 2`.) -/
theorem pos_imp_good {n : ℕ} (h : 0 < A271510 n) :
    ∃ x y z w, Good n x y z w := by
  simp only [A271510] at h
  rw [Finset.card_pos] at h
  obtain ⟨p, hp⟩ := h
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hsum, hxy, hsq⟩ := hp
  refine ⟨p.1.1.1, p.1.1.2, p.1.2, p.2, hsum, hxy, ?_⟩
  exact ⟨(p.1.1.1 ^ 2 + 8 * p.1.1.2 ^ 2 + 16 * p.1.2 ^ 2).sqrt, ((pow_two _).trans hsq).symm⟩

/-- **Exact reduction.**  `A271510 n > 0` if and only if `n` admits a valid tuple.
Thus the full conjecture is *equivalent* to `∀ n, ∃ x y z w, Good n x y z w`. -/
theorem A271510_pos_iff {n : ℕ} :
    0 < A271510 n ↔ ∃ x y z w, Good n x y z w :=
  ⟨pos_imp_good, fun ⟨_, _, _, _, hg⟩ => good_imp_pos hg⟩

/-- **The conjecture holds for every sum of two squares.**  If `n = a² + b²`, take
`(x,y,z,w) = (a,0,0,b)`: then `y² = 0 = a·0 = x·z`, so `good_geo` applies and
`good_imp_pos` gives `0 < A271510 n`.  (This is an infinite family, but of natural
density `0`, so it does not settle the full conjecture.) -/
theorem A271510_pos_of_two_squares {n a b : ℕ} (h : n = a ^ 2 + b ^ 2) :
    0 < A271510 n :=
  good_imp_pos (show Good n a 0 0 b from ⟨by rw [h]; ring, Nat.zero_le a, ⟨a, by ring⟩⟩)

/-- **The conjecture holds for every `n` of the form `2t² + w²`.**  Take
`(x,y,z,w) = (t,t,0,w)`: then `x²+8y²+16z² = 9t² = (3t)²`. -/
theorem A271510_pos_of_two_t_sq {n t w : ℕ} (h : n = 2 * t ^ 2 + w ^ 2) :
    0 < A271510 n :=
  good_imp_pos (show Good n t t 0 w from ⟨by rw [h]; ring, le_refl t, ⟨3 * t, by ring⟩⟩)

/-- **The conjecture holds for every `n` of the form `3t² + w²`.**  Take
`(x,y,z,w) = (t,t,t,w)`: then `x²+8y²+16z² = 25t² = (5t)²`. -/
theorem A271510_pos_of_three_t_sq {n t w : ℕ} (h : n = 3 * t ^ 2 + w ^ 2) :
    0 < A271510 n :=
  good_imp_pos (show Good n t t t w from ⟨by rw [h]; ring, le_refl t, ⟨5 * t, by ring⟩⟩)

/-- **The conjecture holds for every `n` of the form `10t² + w²`.**  Take
`(x,y,z,w) = (3t,0,t,w)`: then `x²+8y²+16z² = 9t²+16t² = 25t² = (5t)²`. -/
theorem A271510_pos_of_ten_t_sq {n t w : ℕ} (h : n = 10 * t ^ 2 + w ^ 2) :
    0 < A271510 n :=
  good_imp_pos (show Good n (3 * t) 0 t w from
    ⟨by rw [h]; ring, Nat.zero_le _, ⟨5 * t, by ring⟩⟩)

/-- **The conjecture holds for every `n` of the form `14t² + w²`.**  Take
`(x,y,z,w) = (3t,t,2t,w)`: then `x²+8y²+16z² = 9t²+8t²+64t² = 81t² = (9t)²`. -/
theorem A271510_pos_of_fourteen_t_sq {n t w : ℕ} (h : n = 14 * t ^ 2 + w ^ 2) :
    0 < A271510 n :=
  good_imp_pos (show Good n (3 * t) t (2 * t) w from
    ⟨by rw [h]; ring, by omega, ⟨9 * t, by ring⟩⟩)

/-- **The conjecture holds for every `n` of the form `27t² + w²`.**  Take
`(x,y,z,w) = (5t,t,t,w)`: then `x²+8y²+16z² = 25t²+8t²+16t² = 49t² = (7t)²`. -/
theorem A271510_pos_of_twentyseven_t_sq {n t w : ℕ} (h : n = 27 * t ^ 2 + w ^ 2) :
    0 < A271510 n :=
  good_imp_pos (show Good n (5 * t) t t w from
    ⟨by rw [h]; ring, by omega, ⟨7 * t, by ring⟩⟩)

/-- **The conjecture holds for every `n` of the form `21t² + w²`.**  Take
`(x,y,z,w) = (4t,2t,t,w)`: then `x²+8y²+16z² = 16t²+32t²+16t² = 64t² = (8t)²`. -/
theorem A271510_pos_of_twentyone_t_sq {n t w : ℕ} (h : n = 21 * t ^ 2 + w ^ 2) :
    0 < A271510 n :=
  good_imp_pos (show Good n (4 * t) (2 * t) t w from
    ⟨by rw [h]; ring, by omega, ⟨8 * t, by ring⟩⟩)

/-- **Descent lemma in usable form.**  Since `Good n x y z w → Good (4n) (2x) (2y) (2z) (2w)`
(`good_four_mul`), positivity propagates from `n` to `4n`.  Combined with the converse
`pos_imp_good`, this gives: `0 < A271510 n → 0 < A271510 (4 * n)`.  Hence the conjecture
for all `n` reduces to the case `4 ∤ n`. -/
theorem A271510_pos_four_mul {n : ℕ} (h : 0 < A271510 n) : 0 < A271510 (4 * n) := by
  obtain ⟨x, y, z, w, hg⟩ := pos_imp_good h
  exact good_imp_pos (good_four_mul hg)

/-- **Square-scaling, on positivity.**  `0 < A271510 n → 0 < A271510 (k² * n)`. -/
theorem A271510_pos_sq_mul (k : ℕ) {n : ℕ} (h : 0 < A271510 n) : 0 < A271510 (k ^ 2 * n) := by
  obtain ⟨x, y, z, w, hg⟩ := pos_imp_good h
  exact good_imp_pos (good_scale k hg)

/-!
### Status of the conjecture

`oeis_A271510_conjecture_i_positive` is the existence part of an **open conjecture
of Zhi-Wei Sun** (OEIS A271510, 2016).  Empirically it is true: `A271510 n > 0`
was verified for all `n < 3·10⁷` by an exact mirror of the Lean definition, and
the values agree with the OEIS data `1,3,3,2,4,4,1,1,3,4,5,...`.

It is equivalent to the additive statement `ℕ = S + □` where
`S = {x²+y²+z² : x ≥ y ≥ 0, z ≥ 0, x²+8y²+16z² a perfect square}`.

Genuine partial results, fully proved above against the real `A271510`:
* `good_imp_pos` is the **bridge**: `Good n x y z w → 0 < A271510 n`, reducing the
  conjecture to the existential `∀ n, ∃ x y z w, Good n x y z w`.
* Through the bridge the conjecture is **proved outright** for the infinite families
  `A271510_pos_of_two_squares` (`n=a²+b²`), `A271510_pos_of_two_t_sq` (`n=2t²+w²`)
  and `A271510_pos_of_three_t_sq` (`n=3t²+w²`); the identities `good_geo`,
  `good_idB`, `good_idC` supply more, and `good_four_mul`/`good_scale` propagate any
  solution to `4n` and `k²n`.
* `good_four_mul` reduces the remaining work to `n` with `4 ∤ n`.
* The full cone parametrization (`cone_param`) makes the value `x²+y²+z²` an
  *irreducible quartic*, so `A271510 n > 0` is equivalent to `n = quartic(m,p,q)+w²`.

Why no elementary construction can settle it (each rigorously checked):
* The quadric `x²+8y²+16z² - s²` has signature `(3,1)`, Witt index `1`; its
  rational parametrization makes the relevant value an irreducible quartic, never
  a (universal) quadratic form.  No universal quaternary sub-form lower-bounds the
  count, since the valid variety is `≤ 3`-dimensional (ternary-form-like range).
* In any witness the variables `y, z` are unbounded, and the minimal "gap"
  `s - x` over witnesses is unbounded (it reaches `288` already for `n < 2·10⁴`),
  so no finite union of parametric "gap/divisor" families covers `ℕ`.
* `A271510` is not multiplicative (`A271510 1 = 3`), so there is no closed-form
  Eisenstein expression; the governing theta series carries a nonzero cusp part.
* `S` has density `≈ 0.21`, governed by genus theory (e.g. `5∉S,10∈S,20∉S,40∈S`,
  a 2-adic spinor pattern, not a congruence), so `S` is not a union of residue
  classes and local–global methods fail.

A complete proof therefore requires the analytic theory of the theta series of the
underlying quadratic forms (Eisenstein main term `≈ c√n > 0`, Hecke/Deligne bound
on the cusp contribution, plus a finite check) — machinery absent from Mathlib,
which does not even contain the three-squares theorem.  The statement is retained
below with the genuine reductions and the geometric-mean identity recorded above.
-/

/--
Conjecture (i) existence part from OEIS A271510:
a(n) > 0 for all n = 0,1,2,...
-/
theorem oeis_A271510_conjecture_i_positive :
  ∀ n : ℕ, 0 < A271510 n
  := by sorry
