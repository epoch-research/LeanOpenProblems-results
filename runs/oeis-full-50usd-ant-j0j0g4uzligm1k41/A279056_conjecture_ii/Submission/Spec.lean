import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A279056: Number of ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ with $w$ a positive integer
and $x,y,z$ nonnegative integers such that $x^3 + 4yz(y-z)$ is a square.
-/
def A279056 (n : ℕ) : ℕ :=
  if n = 0 then 0 else

  -- The bound is $\lfloor\sqrt{n}\rfloor + 1$, which is sufficient to contain all solutions.
  let B : ℕ := n.sqrt + 1
  let R : Finset ℕ := range B

  -- The search space has type ℕ × ℕ × ℕ × ℕ, representing $(w, x, y, z)$.
  let S := ((R.product R).product R).product R

  Finset.card $ S.filter fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd

    -- The cubic expression condition, evaluated in ℤ.
    let square_cond : Prop :=
      let val : ℤ := (x : ℤ)^3 + 4 * (y : ℤ) * (z : ℤ) * ((y : ℤ) - (z : ℤ))
      IsSquare val

    -- w > 0 and the sum of squares equals n.
    w > 0 ∧
    w^2 + x^2 + y^2 + z^2 = n ∧
    square_cond

/--
Define the count for part (ii) of the conjecture:
Number of ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ with $w$ a positive integer
and $x,y,z$ nonnegative integers such that $x^3 + 8yz(2y-z)$ is a square.
-/
def B_A279056 (n : ℕ) : ℕ :=
  if n = 0 then 0 else

  let B : ℕ := n.sqrt + 1
  let R : Finset ℕ := range B
  let S := ((R.product R).product R).product R

  Finset.card $ S.filter fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd

    -- The cubic expression condition for part (ii), evaluated in ℤ.
    -- x^3 + 8*y*z*(2*y - z)
    let square_cond : Prop :=
      let val : ℤ := (x : ℤ)^3 + 8 * (y : ℤ) * (z : ℤ) * (2 * (y : ℤ) - (z : ℤ))
      IsSquare val

    -- w > 0 and the sum of squares equals n.
    w > 0 ∧
    w^2 + x^2 + y^2 + z^2 = n ∧
    square_cond

/-- A nonnegative integer whose square is `≤ n` is `< n.sqrt + 1`, hence lies in the
search range `range (n.sqrt + 1)` used in the definition of `B_A279056`. -/
private theorem bound_of_sq_le {a n : ℕ} (h : a ^ 2 ≤ n) : a < n.sqrt + 1 := by
  have : a ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    simpa [pow_two] using h
  omega

/-- Reduction lemma: to show `0 < B_A279056 n` it suffices to exhibit a single witness
`(w, x, y, z)` with `w > 0`, `w² + x² + y² + z² = n` and `x³ + 8yz(2y - z)` a square.
The range bounds required by the definition of `B_A279056` are derived automatically from
the sum constraint, since each squared component is at most `n`. -/
private theorem exists_witness_imp (n : ℕ) (hn : n > 0)
    (w x y z : ℕ)
    (hw : w > 0)
    (hsum : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n)
    (hsq : IsSquare ((x : ℤ) ^ 3 + 8 * (y : ℤ) * (z : ℤ) * (2 * (y : ℤ) - (z : ℤ)))) :
    0 < B_A279056 n := by
  have hb : w < n.sqrt + 1 := bound_of_sq_le (by omega)
  have hx : x < n.sqrt + 1 := bound_of_sq_le (by omega)
  have hy : y < n.sqrt + 1 := bound_of_sq_le (by omega)
  have hz : z < n.sqrt + 1 := bound_of_sq_le (by omega)
  unfold B_A279056
  rw [if_neg hn.ne']
  simp only
  rw [Finset.card_pos]
  refine ⟨(((w, x), y), z), ?_⟩
  rw [Finset.mem_filter]
  constructor
  · refine Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr hb
    · exact Finset.mem_range.mpr hx
    · exact Finset.mem_range.mpr hy
    · exact Finset.mem_range.mpr hz
  · dsimp only
    exact ⟨by exact_mod_cast hw, by exact_mod_cast hsum, hsq⟩

/-- The core arithmetic content of the conjecture: every positive integer `n` admits a
representation `n = w² + x² + y² + z²` with `w > 0` and `x³ + 8yz(2y - z)` a perfect
square. -/
private theorem A279056_witness (n : ℕ) (hn : n > 0) :
    ∃ w x y z : ℕ, w > 0 ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n ∧
      IsSquare ((x : ℤ) ^ 3 + 8 * (y : ℤ) * (z : ℤ) * (2 * (y : ℤ) - (z : ℤ))) := by
  sorry

/--
Conjecture (ii) from A279056: Any positive integer n can be written as
$w^2 + x^2 + y^2 + z^2$ with $w$ a positive integer and $x,y,z$ nonnegative integers
such that $x^3 + 8yz(2y-z)$ is a square.
This is equivalent to $B\_A279056(n) > 0$ for all $n > 0$.
-/
theorem A279056_conjecture_ii (n : ℕ) (hn : n > 0) : 0 < B_A279056 n := by
  obtain ⟨w, x, y, z, hw, hsum, hsq⟩ := A279056_witness n hn
  exact exists_witness_imp n hn w x y z hw hsum hsq
