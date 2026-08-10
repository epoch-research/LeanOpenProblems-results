import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A272979: Number of ways to write $n$ as $x^2 + 2y^2 + 3z^3 + 4w^4$ with $x,y,z,w$ nonnegative integers.
-/
def A272979 (n : ℕ) : ℕ :=
  -- The cardinality of the set of tuples (x, y, z, w) in ℕ^4 that satisfy the equation.
  -- We use n+1 as a loose but safe bound for all variables, as x^k <= n implies x <= n.
  -- This is guaranteed to be a finite set.
  (Finset.range (n + 1)).sum fun x =>
    (Finset.range (n + 1)).sum fun y =>
      (Finset.range (n + 1)).sum fun z =>
        (Finset.range (n + 1)).sum fun w =>
          if x^2 + 2 * y^2 + 3 * z^3 + 4 * w^4 = n then 1 else 0

-- Definition of the predicate for representing a number n
def is_representable (a b c d n : ℕ) : Prop :=
  ∃ x y z w : ℕ, a * x^2 + b * y^2 + c * z^3 + d * w^4 = n

/--
A quadruple $(a,b,c,d)$ represents all natural numbers if every $n \in \mathbb{N}$ can be written
as $a x^2 + b y^2 + c z^3 + d w^4$ for $x,y,z,w \in \mathbb{N}$.
-/
def represents_all_naturals (a b c d : ℕ) : Prop :=
  ∀ n : ℕ, is_representable a b c d n

open List

/--
The list of 49 quadruples conjectured by Zhi-Wei Sun to represent all natural numbers
in the form $a x^2 + b y^2 + c z^3 + d w^4$.
-/
def sun_49_quadruples : List (ℕ × ℕ × ℕ × ℕ) :=
  [
    (1,2,1,1), (1,3,1,1), (1,6,1,1), (2,3,1,1), (2,4,1,1),
    (1,1,2,1), (1,4,2,1), (1,2,3,1), (1,2,4,1), (1,2,12,1),
    (1,1,1,2), (1,2,1,2), (1,3,1,2), (1,4,1,2), (1,5,1,2), (1,11,1,2), (1,12,1,2),
    (2,4,1,2), (3,5,1,2), (1,1,4,2),
    (1,1,1,3), (1,2,1,3), (1,3,1,3), (1,2,4,3),
    (1,2,1,4), (1,3,1,4), (2,3,1,4), (1,1,2,4), (1,2,2,4), (1,8,2,4), (1,2,3,4),
    (1,1,1,5), (1,2,1,5), (2,3,1,5), (2,4,1,5), (1,3,2,5),
    (1,1,1,6), (1,3,1,6), (1,1,2,6),
    (1,2,1,8), (1,2,4,8),
    (1,2,1,10), (1,1,2,10),
    (1,2,1,11), (2,4,1,11),
    (1,2,1,12), (1,1,2,13), (1,2,1,14), (1,2,1,15)
  ]

/-
oeis_272979_conjecture_0: Conjecture: For positive integers a,b,c,d, any natural number can be written as
a*x^2 + b*y^2 + c*z^3 + d*w^4 with x,y,z,w nonnegative integers, if and only if
(a,b,c,d) is among the following 49 quadruples: (1,2,1,1), (1,3,1,1), ..., (1,2,1,15).

This conjecture is FALSE as stated. The form `a*x^2 + b*y^2 + c*z^3 + d*w^4` is symmetric
in the two square variables `x` and `y`: swapping `x` with `y` shows that `(a,b,c,d)` and
`(b,a,c,d)` represent exactly the same set of natural numbers, so
`represents_all_naturals a b c d ↔ represents_all_naturals b a c d`.

However the list `sun_49_quadruples` is *not* closed under swapping the first two coordinates:
for instance `(1,2,1,1)` is in the list but `(2,1,1,1)` is not. These two quadruples represent
the same naturals, so they cannot both satisfy the claimed biconditional (membership differs
while `represents_all_naturals` agrees). This yields a counterexample no matter whether these
particular forms are universal or not.
-/

/-- Swapping the roles of `x` and `y` shows the representation problem is symmetric in `a` and `b`. -/
theorem represents_all_naturals_swap (a b c d : ℕ) :
    represents_all_naturals a b c d → represents_all_naturals b a c d := by
  intro h n
  obtain ⟨x, y, z, w, hxyzw⟩ := h n
  exact ⟨y, x, z, w, by rw [← hxyzw]; ring⟩

theorem oeis_272979_conjecture_0.disproof :
    ¬ (∀ (a b c d : ℕ),
        (a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) →
        (represents_all_naturals a b c d ↔
          (a, b, c, d) ∈ sun_49_quadruples)) := by
  intro h
  -- The biconditional at `(1,2,1,1)` and at `(2,1,1,1)`.
  have h1 := h 1 2 1 1 (by decide)
  have h2 := h 2 1 1 1 (by decide)
  -- `(1,2,1,1)` is in the list, `(2,1,1,1)` is not.
  have mem1 : ((1, 2, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∈ sun_49_quadruples := by decide
  have nmem2 : ((2, 1, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∉ sun_49_quadruples := by decide
  -- From the biconditional, `(1,2,1,1)` represents all naturals.
  have rep1 : represents_all_naturals 1 2 1 1 := h1.mpr mem1
  -- By the swap symmetry, so does `(2,1,1,1)`.
  have rep2 : represents_all_naturals 2 1 1 1 := represents_all_naturals_swap 1 2 1 1 rep1
  -- But then the biconditional forces `(2,1,1,1)` into the list, a contradiction.
  exact nmem2 (h2.mp rep2)
