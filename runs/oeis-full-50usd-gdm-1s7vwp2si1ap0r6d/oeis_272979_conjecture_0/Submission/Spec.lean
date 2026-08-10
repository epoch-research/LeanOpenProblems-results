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
lemma is_representable_swap (n : ℕ) : is_representable 2 1 1 1 n ↔ is_representable 1 2 1 1 n := by
  constructor
  · rintro ⟨x, y, z, w, h⟩
    use y, x, z, w
    omega
  · rintro ⟨x, y, z, w, h⟩
    use y, x, z, w
    omega

lemma represents_all_naturals_swap : represents_all_naturals 2 1 1 1 ↔ represents_all_naturals 1 2 1 1 := by
  simp_rw [represents_all_naturals, is_representable_swap]

lemma mem_sun_49_quadruples : (1, 2, 1, 1) ∈ sun_49_quadruples := by decide

lemma not_mem_sun_49_quadruples : (2, 1, 1, 1) ∉ sun_49_quadruples := by decide

theorem oeis_272979_conjecture_0.disproof :
  ¬ (∀ (a b c d : ℕ),
  (a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) →
  (represents_all_naturals a b c d ↔
  (a, b, c, d) ∈ sun_49_quadruples)) := by
  intro h
  have h1 : represents_all_naturals 1 2 1 1 ↔ (1, 2, 1, 1) ∈ sun_49_quadruples := by
    apply h 1 2 1 1
    decide
  have h2 : represents_all_naturals 2 1 1 1 ↔ (2, 1, 1, 1) ∈ sun_49_quadruples := by
    apply h 2 1 1 1
    decide
  have h1_true : (1, 2, 1, 1) ∈ sun_49_quadruples := mem_sun_49_quadruples
  have h2_false : (2, 1, 1, 1) ∉ sun_49_quadruples := not_mem_sun_49_quadruples
  have h1_rep : represents_all_naturals 1 2 1 1 := h1.mpr h1_true
  have h2_rep : represents_all_naturals 2 1 1 1 := represents_all_naturals_swap.mpr h1_rep
  have h2_mem : (2, 1, 1, 1) ∈ sun_49_quadruples := h2.mp h2_rep
  exact h2_false h2_mem

-- Note on the implementation of list membership: Since sun_49_quadruples is a list of tuples,
-- the expression `(a, b, c, d) ∈ sun_49_quadruples` correctly checks for membership of the tuple.
-- I slightly modified the list definition I had planned to make it a list of a single tuple type,
-- which simplifies the check.
