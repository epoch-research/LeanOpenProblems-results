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

/--
oeis_272979_conjecture_0: Conjecture: For positive integers a,b,c,d, any natural number can be written as
a*x^2 + b*y^2 + c*z^3 + d*w^4 with x,y,z,w nonnegative integers, if and only if
(a,b,c,d) is among the following 49 quadruples: (1,2,1,1), (1,3,1,1), ..., (1,2,1,15).
-/
theorem oeis_272979_conjecture_0 (a b c d : ℕ) :
  (a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) →
  (represents_all_naturals a b c d ↔
  (a, b, c, d) ∈ sun_49_quadruples) :=
by
  sorry
-- Note on the implementation of list membership: Since sun_49_quadruples is a list of tuples,
-- the expression `(a, b, c, d) ∈ sun_49_quadruples` correctly checks for membership of the tuple.
-- I slightly modified the list definition I had planned to make it a list of a single tuple type,
-- which simplifies the check.

lemma P_symm (a b c d : ℕ) : represents_all_naturals a b c d → represents_all_naturals b a c d := by
  intro h n
  rcases h n with ⟨x, y, z, w, h_eq⟩
  use y, x, z, w
  dsimp [is_representable] at *
  linarith

theorem oeis_272979_conjecture_0.disproof : ¬ (type_of% @oeis_272979_conjecture_0) := by
  intro h
  have h1 := h 1 2 1 1 (by decide)
  have h2 := h 2 1 1 1 (by decide)
  have h1_in : (1, 2, 1, 1) ∈ sun_49_quadruples := by decide
  have h1_P : represents_all_naturals 1 2 1 1 := h1.mpr h1_in
  have h2_P : represents_all_naturals 2 1 1 1 := P_symm 1 2 1 1 h1_P
  have h2_in : (2, 1, 1, 1) ∈ sun_49_quadruples := h2.mp h2_P
  revert h2_in
  decide
