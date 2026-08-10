import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The $x$-th pentagonal number, $\frac{x(3x-1)}{2}$, for $x \ge 0$.
-/
private def pentagonal_first (x : ℕ) : ℕ := (x * (3 * x - 1)) / 2

/--
The $y$-th "second pentagonal number", $\frac{y(3y+1)}{2}$, for $y \ge 0$.
-/
private def pentagonal_second (y : ℕ) : ℕ := (y * (3 * y + 1)) / 2

/--
The generalized decagonal number $m(4m-3)$ is calculated implicitly here.
The number of $\mathbb{Z}$ indices $m$ such that $m(4m-3)=r$. This is 1 if $r$ is a
generalized decagonal number (i.e., $16r+9$ is a perfect square), and 0 otherwise.
-/
private def count_generalized_decagonal_index (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

/--
A253187: Number of ordered ways to write $n$ as the sum of a pentagonal number, a second pentagonal number and a generalized decagonal number.
$$a(n) = \# \{ (x, y, m) \in \mathbb{N} \times \mathbb{N} \times \mathbb{Z} \mid n = \frac{x(3x-1)}{2} + \frac{y(3y+1)}{2} + m(4m-3) \}$$
-/
def A253187 (n : ℕ) : ℕ :=
  -- Iterate x and y up to n, which is a sufficient bound.
  (range (n + 1)).sum fun x =>
    (range (n + 1)).sum fun y =>
      let sum_pent := pentagonal_first x + pentagonal_second y
      if sum_pent <= n then
        count_generalized_decagonal_index (n - sum_pent)
      else
        0

-- Generalized polygonal number formula, $\frac{(k-2)z^2 - (k-4)z}{2}$, for $z \in \mathbb{Z}$.
def polygonal_num_val (k : ℕ) (z : ℤ) : ℤ :=
  if k ≥ 3 then
    let k' : ℤ := k
    -- The numerator is always even when k >= 3, so division is exact integer division.
    ((k' - 2) * z * z - (k' - 4) * z) / 2
  else 0

-- The k-gonal number (first type), index $x \in \mathbb{N}$.
-- Since $x \ge 0$ and $k \ge 3$, the result of polygonal_num_val is $\ge 0$.
def P_k_first (k : ℕ) (x : ℕ) : ℕ :=
  (polygonal_num_val k (x : ℤ)).toNat

-- The second k-gonal number, index $y \in \mathbb{N}$.
-- For $y \in \mathbb{N}$ and $k \ge 3$, $P_k(-(y:\mathbb{Z}))$ is always non-negative.
def P_k_second (k : ℕ) (y : ℕ) : ℕ :=
  (polygonal_num_val k (-(y : ℤ))).toNat

-- The set of pairs (k,m) in the conjecture.
private noncomputable def C_pairs : Set (ℕ × ℕ) :=
  {(5, 7), (5, 9), (5, 13), (6, 5), (6, 7), (7, 5)}

/-!
### Reduction of the conjecture to ternary quadratic form representation.

Each clause of the conjecture is an instance of the statement that a fixed
positive‑definite diagonal **ternary quadratic form** represents every value of a
fixed arithmetic progression. Using
`8a·P_k(x) + (a-2)^2 = (2ax-(a-2))^2` (with `a = k-2`) one shows, for `(k,m)`,
that `n = P_k(x) + P_k(-y) + P_m(z)` is solvable iff the form
`(m-2)·A^2 + (m-2)·B^2 + (k-2)·C^2` represents `N(n) := 8(k-2)(m-2)·n + c`
(with the appropriate congruences on `A,B,C`):

* part 1  `(k,m)=(5,10)` : `8A²+8B²+3C² = 192n+124`  (genus has **1** class)
* `(5,7)`  : `5A²+5B²+3C²  = 120n+37`   (genus has **2** classes)
* `(5,9)`  : `7A²+7B²+3C²  = 168n+89`   (genus has **1** class)
* `(5,13)` : `11A²+11B²+3C² = 264n+265` (genus has **2** classes)
* `(6,5)`  : `3A²+3B²+4C²  = 96n+28`    (genus has **1** class)
* `(6,7)`  : `5A²+5B²+4C²  = 160n+76`   (genus has **2** classes)
* `(7,5)`  : `3A²+3B²+5C²  = 120n+59`   (genus has **2** classes)

These facts are exactly the deep number‑theoretic content. The one‑class forms
require the genus local–global principle (Hasse–Minkowski), and the four
two‑class forms require spinor‑genus / analytic (modular form) methods; none of
this machinery is presently available in Mathlib. They are isolated below as the
irreducible lemmas `A253187.pos` and `A253187.rep_*`.
-/

/-- Part 1: every `n` is a pentagonal + second pentagonal + generalized decagonal
number (the `(5,10)` ternary form `8A²+8B²+3C²` represents `192n+124`). -/
theorem A253187.pos : ∀ n : ℕ, A253187 n > 0 := by sorry

theorem A253187.rep_5_7 : ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
    (P_k_first 5 x) + (P_k_second 5 y) + (polygonal_num_val 7 z).toNat = n := by sorry

theorem A253187.rep_5_9 : ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
    (P_k_first 5 x) + (P_k_second 5 y) + (polygonal_num_val 9 z).toNat = n := by sorry

theorem A253187.rep_5_13 : ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
    (P_k_first 5 x) + (P_k_second 5 y) + (polygonal_num_val 13 z).toNat = n := by sorry

theorem A253187.rep_6_5 : ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
    (P_k_first 6 x) + (P_k_second 6 y) + (polygonal_num_val 5 z).toNat = n := by sorry

theorem A253187.rep_6_7 : ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
    (P_k_first 6 x) + (P_k_second 6 y) + (polygonal_num_val 7 z).toNat = n := by sorry

theorem A253187.rep_7_5 : ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
    (P_k_first 7 x) + (P_k_second 7 y) + (polygonal_num_val 5 z).toNat = n := by sorry

/--
A253187 Conjecture: a(n) > 0 for all n. Also, for any ordered pair (k,m) among (5,7), (5,9), (5,13), (6,5), (6,7), (7,5), each nonnegative integer n can be written as the sum of a k-gonal number, a second k-gonal number and a generalized m-gonal number.
-/
theorem A253187.universal_sum_conjecture :
  (∀ n : ℕ, A253187 n > 0) ∧
  ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n := by
  refine ⟨A253187.pos, ?_⟩
  intro k m h n
  simp only [C_pairs, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨hk, hm⟩ | ⟨hk, hm⟩ | ⟨hk, hm⟩ | ⟨hk, hm⟩ | ⟨hk, hm⟩ | ⟨hk, hm⟩ <;>
    subst hk <;> subst hm
  · exact A253187.rep_5_7 n
  · exact A253187.rep_5_9 n
  · exact A253187.rep_5_13 n
  · exact A253187.rep_6_5 n
  · exact A253187.rep_6_7 n
  · exact A253187.rep_7_5 n
