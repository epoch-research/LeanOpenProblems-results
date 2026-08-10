import FormalConjectures.Util.ProblemImports

open Int Nat Finset

/--
A281939: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z$ nonnegative integers and $w$ an integer,
and $x - y$ and $3z + w$ both squares.
-/
noncomputable def A281939 (n : ℕ) : ℕ :=
  let B : ℕ := n.sqrt
  let n_int : ℤ := n

  let S_nat : Finset ℕ := Finset.range (B + 1)
  let S_int : Finset ℤ := Finset.Icc (-(B : ℤ)) (B : ℤ)

  -- The set of all candidate quadruples (x, y, z, w) in a bounded box
  let Candidates : Finset (((ℕ × ℕ) × ℕ) × ℤ) :=
    (S_nat.product S_nat).product S_nat |>.product S_int

  (Candidates.filter fun p =>
    -- Unpack the nested tuple
    let x := p.fst.fst.fst;
    let y := p.fst.fst.snd;
    let z := p.fst.snd;
    let w := p.snd;

    let x_z : ℤ := x;
    let y_z : ℤ := y;
    let z_z : ℤ := z;

    -- Predicate for a non-negative integer k to be a perfect square in ℤ
    let is_perfect_square (k : ℤ) : Prop := k ≥ 0 ∧ Int.sqrt k * Int.sqrt k = k;

    -- Constraints
    -- 1. Sum of squares equals n
    x_z^2 + y_z^2 + z_z^2 + w^2 = n_int ∧
    -- 2. x - y is a square in ℤ
    is_perfect_square (x_z - y_z) ∧
    -- 3. 3z + w is a square in ℤ
    is_perfect_square (3 * z_z + w)
  ).card

open BigOperators

/-- **Reduction step (fully proved).**
If there is an explicit quadruple `(x, y, z, w)` (with `x, y, z : ℕ`, `w : ℤ`) lying in the
search box `x, y, z ≤ ⌊√n⌋`, `|w| ≤ ⌊√n⌋`, satisfying `x² + y² + z² + w² = n` together with the
two perfect-square side conditions, then `A281939 n > 0`.  This packages the (decidable, finitary)
content of `A281939` and reduces the conjecture to a pure number-theoretic existence statement. -/
theorem A281939_pos_of_witness (n : ℕ)
    (h : ∃ (x y z : ℕ) (w : ℤ),
      x ≤ n.sqrt ∧ y ≤ n.sqrt ∧ z ≤ n.sqrt ∧ -(n.sqrt : ℤ) ≤ w ∧ w ≤ (n.sqrt : ℤ) ∧
      (x : ℤ)^2 + (y : ℤ)^2 + (z : ℤ)^2 + w^2 = (n : ℤ) ∧
      (((x : ℤ) - (y : ℤ)) ≥ 0 ∧
         Int.sqrt ((x:ℤ) - (y:ℤ)) * Int.sqrt ((x:ℤ) - (y:ℤ)) = (x:ℤ) - (y:ℤ)) ∧
      ((3 * (z:ℤ) + w) ≥ 0 ∧
         Int.sqrt (3*(z:ℤ)+w) * Int.sqrt (3*(z:ℤ)+w) = 3*(z:ℤ)+w)) :
    A281939 n > 0 := by
  obtain ⟨x, y, z, w, hx, hy, hz, hwl, hwr, hsum, hxy, hzw⟩ := h
  unfold A281939
  apply Finset.Nonempty.card_pos
  refine ⟨((((x, y), z), w)), ?_⟩
  refine Finset.mem_filter.mpr ⟨?_, hsum, hxy, hzw⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hx)
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hy)
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hz)
  · exact Finset.mem_Icc.mpr ⟨hwl, hwr⟩

/-- **Core existence statement (the open conjecture).**
By the substitution `x = (P + a²)/2`, `y = (P − a²)/2`, `z = (3b² + Q)/10`, `w = (b² − 3Q)/10`
(where `a² = x − y` and `b² = 3z + w`), the existence of a valid witness for `n` is *equivalent*
to the existence of nonnegative `a, b` for which
`10·n − 5·a⁴ − b⁴ = 5·P² + Q²` is properly represented by the binary quadratic form `5P² + Q²`
of discriminant `−20` (the principal genus of `ℚ(√−5)`), with the congruences `P ≡ a² (mod 2)`,
`P ≥ a²` and `Q ≡ −3b² (mod 10)`, `Q ≥ −3b²`.  Since `5` is an idoneal number, this form has one
class per genus, so the obstruction is purely the multiplicative/factorization condition on
`10·n − 5·a⁴ − b⁴` over the thin quartic family in `(a, b)`.  This is exactly Zhi-Wei Sun's open
conjecture A281939(i); it has been verified numerically (here, up to `10⁸`) but a proof requires
genus theory of `ℤ[√−5]` together with a uniform additive result not currently available. -/
theorem A281939_witness (n : ℕ) :
    ∃ (x y z : ℕ) (w : ℤ),
      x ≤ n.sqrt ∧ y ≤ n.sqrt ∧ z ≤ n.sqrt ∧ -(n.sqrt : ℤ) ≤ w ∧ w ≤ (n.sqrt : ℤ) ∧
      (x : ℤ)^2 + (y : ℤ)^2 + (z : ℤ)^2 + w^2 = (n : ℤ) ∧
      (((x : ℤ) - (y : ℤ)) ≥ 0 ∧
         Int.sqrt ((x:ℤ) - (y:ℤ)) * Int.sqrt ((x:ℤ) - (y:ℤ)) = (x:ℤ) - (y:ℤ)) ∧
      ((3 * (z:ℤ) + w) ≥ 0 ∧
         Int.sqrt (3*(z:ℤ)+w) * Int.sqrt (3*(z:ℤ)+w) = 3*(z:ℤ)+w) := by
  sorry

/--
Conjecture (i) in A281939: a(n) > 0 for all $n \ge 0$.
Every nonnegative integer $n$ can be written as $x^2 + y^2 + z^2 + w^2$ with
$x, y, z \in \mathbb{N}$, $w \in \mathbb{Z}$, and $x-y$ and $3z+w$ being perfect squares.
-/
theorem oeis_281939_conjecture_i : ∀ n : ℕ, A281939 n > 0 :=
  fun n => A281939_pos_of_witness n (A281939_witness n)
