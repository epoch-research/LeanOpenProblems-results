import FormalConjecturesUtil

/-!
# A finite arithmetic obstruction to exact quadratic graphs

Let `R` be a finite set of natural-number indices, with integer values `n i`,
integer complementary factors `m i`, and distinct natural prime bases `p i`.
Suppose `n i = m i * (p i : ℤ) ^ 2` and
`B0 * n i = A * (p i : ℤ) ^ 2 + B * (p i : ℤ) + C` on `R`, with `B0 ≠ 0`.

Every base divides `C`; if `C = 0`, every base divides `B`. If `B = C = 0`,
then `B0 * m i = A`, so injective complementary factors force `R.card ≤ 1`.
Consequently, when `2 ≤ R.card`, a nonzero coefficient `E ∈ {B, C}` is divisible
by the product of the distinct prime bases. Under `2 ≤ H`, `H < p i`, and
`B.natAbs, C.natAbs ≤ H ^ K`, this gives `R.card ≤ K`.

There is no bound on `A` or `B0`, no positivity assumption on `m` or `n`, and no
injectivity assumption on `n`. This is a necessary condition for an exact graph,
not an inverse theorem producing such graphs and not a squarefree-gap theorem.

The final section also gives an explicit four-point determinant expansion and
congruences modulo a base and its square, together with determinant vanishing
on exact quadratic graphs. These identities do not assume primality.
-/

open Finset

namespace QuadraticGraph

/-- Reduction modulo a base: primality, nonvanishing, and a nonzero denominator
are not needed for divisibility of the constant coefficient. -/
theorem base_dvd_constant (n m : ℤ) (p : ℕ) (B0 A B C : ℤ)
    (hrep : n = m * (p : ℤ) ^ 2)
    (hgraph : B0 * n = A * (p : ℤ) ^ 2 + B * (p : ℤ) + C) :
    (p : ℤ) ∣ C := by
  rw [hrep] at hgraph
  refine ⟨(B0 * m - A) * (p : ℤ) - B, ?_⟩
  linear_combination -hgraph

/-- After the constant vanishes, cancel one nonzero base to see that it divides
the linear coefficient. Primality is still unnecessary. -/
theorem base_dvd_linear_of_constant_eq_zero
    (n m : ℤ) (p : ℕ) (B0 A B C : ℤ) (hp : p ≠ 0)
    (hrep : n = m * (p : ℤ) ^ 2)
    (hgraph : B0 * n = A * (p : ℤ) ^ 2 + B * (p : ℤ) + C)
    (hC : C = 0) :
    (p : ℤ) ∣ B := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  refine ⟨B0 * m - A, ?_⟩
  apply mul_right_cancel₀ hpZ
  rw [hrep, hC] at hgraph
  linear_combination -hgraph

/-- If both lower coefficients vanish, the complementary factor satisfies an
exact linear equality with the leading coefficient and denominator. -/
theorem mul_cofactor_eq_of_coefficients_eq_zero
    (n m : ℤ) (p : ℕ) (B0 A B C : ℤ) (hp : p ≠ 0)
    (hrep : n = m * (p : ℤ) ^ 2)
    (hgraph : B0 * n = A * (p : ℤ) ^ 2 + B * (p : ℤ) + C)
    (hB : B = 0) (hC : C = 0) :
    B0 * m = A := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  apply mul_right_cancel₀ (pow_ne_zero 2 hpZ)
  rw [hrep, hB, hC] at hgraph
  simpa only [zero_mul, add_zero, mul_assoc] using hgraph

/-- The division form of the degenerate graph. Integer division is exact here;
no field casts or sign assumption on `B0` are involved. -/
theorem cofactor_eq_div_of_coefficients_eq_zero
    (n m : ℤ) (p : ℕ) (B0 A B C : ℤ) (hB0 : B0 ≠ 0) (hp : p ≠ 0)
    (hrep : n = m * (p : ℤ) ^ 2)
    (hgraph : B0 * n = A * (p : ℤ) ^ 2 + B * (p : ℤ) + C)
    (hB : B = 0) (hC : C = 0) :
    m = A / B0 := by
  have hmul := mul_cofactor_eq_of_coefficients_eq_zero n m p B0 A B C
    hp hrep hgraph hB hC
  rw [← hmul, Int.mul_ediv_cancel_left _ hB0]

/-- Injective complementary factors allow at most one point on a degenerate
quadratic graph. Distinct bases and primality are not required for this step. -/
theorem card_le_one_of_coefficients_eq_zero
    (R : Finset ℕ) (n m : ℕ → ℤ) (p : ℕ → ℕ) (B0 A B C : ℤ)
    (hB0 : B0 ≠ 0) (hp : ∀ i ∈ R, p i ≠ 0)
    (hrep : ∀ i ∈ R, n i = m i * (p i : ℤ) ^ 2)
    (hminj : Set.InjOn m (R : Set ℕ))
    (hgraph : ∀ i ∈ R, B0 * n i = A * (p i : ℤ) ^ 2 + B * (p i : ℤ) + C)
    (hB : B = 0) (hC : C = 0) :
    R.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply hminj hi hj
  apply mul_left_cancel₀ hB0
  exact (mul_cofactor_eq_of_coefficients_eq_zero (n i) (m i) (p i) B0 A B C
    (hp i hi) (hrep i hi) (hgraph i hi) hB hC).trans
    (mul_cofactor_eq_of_coefficients_eq_zero (n j) (m j) (p j) B0 A B C
      (hp j hj) (hrep j hj) (hgraph j hj) hB hC).symm

/-- With at least two distinct complementary factors, one of the two lower
coefficients is nonzero and divisible by every base. -/
theorem exists_nonzero_coefficient
    (R : Finset ℕ) (n m : ℕ → ℤ) (p : ℕ → ℕ) (B0 A B C : ℤ)
    (hR : 2 ≤ R.card) (hB0 : B0 ≠ 0) (hp : ∀ i ∈ R, p i ≠ 0)
    (hrep : ∀ i ∈ R, n i = m i * (p i : ℤ) ^ 2)
    (hminj : Set.InjOn m (R : Set ℕ))
    (hgraph : ∀ i ∈ R, B0 * n i = A * (p i : ℤ) ^ 2 + B * (p i : ℤ) + C) :
    ∃ E : ℤ, E ∈ ({B, C} : Finset ℤ) ∧ E ≠ 0 ∧ ∀ i ∈ R, (p i : ℤ) ∣ E := by
  by_cases hC : C = 0
  · have hB : B ≠ 0 := by
      intro hB
      have hsmall := card_le_one_of_coefficients_eq_zero R n m p B0 A B C
        hB0 hp hrep hminj hgraph hB hC
      omega
    refine ⟨B, by simp, hB, ?_⟩
    intro i hi
    exact base_dvd_linear_of_constant_eq_zero (n i) (m i) (p i) B0 A B C
      (hp i hi) (hrep i hi) (hgraph i hi) hC
  · refine ⟨C, by simp, hC, ?_⟩
    intro i hi
    exact base_dvd_constant (n i) (m i) (p i) B0 A B C (hrep i hi) (hgraph i hi)

/-- Distinct natural prime bases dividing an integer have product dividing its
absolute value. This also handles negative integers and the empty product. -/
theorem prod_primes_dvd_natAbs (R : Finset ℕ) (p : ℕ → ℕ) (E : ℤ)
    (hp : ∀ i ∈ R, (p i).Prime) (hpinj : Set.InjOn p (R : Set ℕ))
    (hdiv : ∀ i ∈ R, (p i : ℤ) ∣ E) :
    (∏ i ∈ R, p i) ∣ E.natAbs := by
  apply Finset.prod_dvd_of_isRelPrime ?_ (fun i hi => Int.natCast_dvd.mp (hdiv i hi))
  intro i hi j hj hij
  apply Nat.coprime_iff_isRelPrime.mp
  exact (Nat.coprime_primes (hp i hi) (hp j hj)).mpr
    (fun he => hij (hpinj hi hj he))

/-- The arithmetic obstruction: the full product of the distinct prime bases
divides the absolute value of a nonzero coefficient among `B` and `C`. -/
theorem exists_nonzero_coefficient_prod_dvd
    (R : Finset ℕ) (n m : ℕ → ℤ) (p : ℕ → ℕ) (B0 A B C : ℤ)
    (hR : 2 ≤ R.card) (hB0 : B0 ≠ 0) (hp : ∀ i ∈ R, (p i).Prime)
    (hrep : ∀ i ∈ R, n i = m i * (p i : ℤ) ^ 2)
    (hpinj : Set.InjOn p (R : Set ℕ)) (hminj : Set.InjOn m (R : Set ℕ))
    (hgraph : ∀ i ∈ R, B0 * n i = A * (p i : ℤ) ^ 2 + B * (p i : ℤ) + C) :
    ∃ E : ℤ, E ∈ ({B, C} : Finset ℤ) ∧ E ≠ 0 ∧
      (∀ i ∈ R, (p i : ℤ) ∣ E) ∧ (∏ i ∈ R, p i) ∣ E.natAbs := by
  obtain ⟨E, hE, hE0, hdiv⟩ := exists_nonzero_coefficient R n m p B0 A B C
    hR hB0 (fun i hi => (hp i hi).ne_zero) hrep hminj hgraph
  exact ⟨E, hE, hE0, hdiv, prod_primes_dvd_natAbs R p E hp hpinj hdiv⟩

/-- A nonzero common multiple of distinct prime bases has at least exponential
absolute value when all the bases exceed `H`. -/
theorem pow_card_le_natAbs (R : Finset ℕ) (p : ℕ → ℕ) (H : ℕ) (E : ℤ)
    (hE : E ≠ 0) (hp : ∀ i ∈ R, (p i).Prime)
    (hlarge : ∀ i ∈ R, H < p i) (hpinj : Set.InjOn p (R : Set ℕ))
    (hdiv : ∀ i ∈ R, (p i : ℤ) ∣ E) :
    H ^ R.card ≤ E.natAbs := by
  calc
    H ^ R.card = ∏ _i ∈ R, H := (prod_const H).symm
    _ ≤ ∏ i ∈ R, p i := prod_le_prod' (fun i hi => (hlarge i hi).le)
    _ ≤ E.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hE)
      (prod_primes_dvd_natAbs R p E hp hpinj hdiv)

/-- Height bound for an exact quadratic graph containing at least two points.
Only the two lower coefficients are bounded; `A` and nonzero `B0` are arbitrary. -/
theorem card_le_of_height
    (R : Finset ℕ) (n m : ℕ → ℤ) (p : ℕ → ℕ) (B0 A B C : ℤ) (H K : ℕ)
    (hR : 2 ≤ R.card) (hB0 : B0 ≠ 0) (hH : 2 ≤ H)
    (hB : B.natAbs ≤ H ^ K) (hC : C.natAbs ≤ H ^ K)
    (hp : ∀ i ∈ R, (p i).Prime) (hlarge : ∀ i ∈ R, H < p i)
    (hrep : ∀ i ∈ R, n i = m i * (p i : ℤ) ^ 2)
    (hpinj : Set.InjOn p (R : Set ℕ)) (hminj : Set.InjOn m (R : Set ℕ))
    (hgraph : ∀ i ∈ R, B0 * n i = A * (p i : ℤ) ^ 2 + B * (p i : ℤ) + C) :
    R.card ≤ K := by
  obtain ⟨E, hE, hE0, hdiv⟩ := exists_nonzero_coefficient R n m p B0 A B C
    hR hB0 (fun i hi => (hp i hi).ne_zero) hrep hminj hgraph
  have hheight : E.natAbs ≤ H ^ K := by
    simp only [mem_insert, mem_singleton] at hE
    rcases hE with rfl | rfl
    · exact hB
    · exact hC
  apply (Nat.pow_le_pow_iff_right (show 1 < H by omega)).mp
  exact (pow_card_le_natAbs R p H E hE0 hp hlarge hpinj hdiv).trans hheight

/-- Unconditional-size version: a graph is either a singleton (or empty), or
has at most `K` points. In particular the safe bound is `max 1 K`, even at `K = 0`. -/
theorem card_le_max_one_of_height
    (R : Finset ℕ) (n m : ℕ → ℤ) (p : ℕ → ℕ) (B0 A B C : ℤ) (H K : ℕ)
    (hB0 : B0 ≠ 0) (hH : 2 ≤ H)
    (hB : B.natAbs ≤ H ^ K) (hC : C.natAbs ≤ H ^ K)
    (hp : ∀ i ∈ R, (p i).Prime) (hlarge : ∀ i ∈ R, H < p i)
    (hrep : ∀ i ∈ R, n i = m i * (p i : ℤ) ^ 2)
    (hpinj : Set.InjOn p (R : Set ℕ)) (hminj : Set.InjOn m (R : Set ℕ))
    (hgraph : ∀ i ∈ R, B0 * n i = A * (p i : ℤ) ^ 2 + B * (p i : ℤ) + C) :
    R.card ≤ max 1 K := by
  by_cases hR : 2 ≤ R.card
  · exact (card_le_of_height R n m p B0 A B C H K hR hB0 hH hB hC
      hp hlarge hrep hpinj hminj hgraph).trans (le_max_right _ _)
  · exact (show R.card ≤ 1 by omega).trans (le_max_left _ _)

/- Four-point identities. -/

/-- The four-point determinant with rows `(1, p i, (p i)^2, n i)`.
Integer bases are allowed in the determinant identities below. -/
def fourPointDet (p n : Fin 4 → ℤ) : ℤ :=
  Matrix.det (fun i : Fin 4 => ![1, p i, (p i) ^ 2, n i])

/-- Explicit Vandermonde-cofactor expansion of the actual four-by-four determinant. -/
theorem fourPointDet_eq (p n : Fin 4 → ℤ) :
    fourPointDet p n =
      -n 0 * (p 2 - p 1) * (p 3 - p 1) * (p 3 - p 2) +
      n 1 * (p 2 - p 0) * (p 3 - p 0) * (p 3 - p 2) -
      n 2 * (p 1 - p 0) * (p 3 - p 0) * (p 3 - p 1) +
      n 3 * (p 1 - p 0) * (p 2 - p 0) * (p 2 - p 1) := by
  unfold fourPointDet
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  change
    (-1 : ℤ) ^ 0 * 1 *
      (p 1 * (p 2) ^ 2 * n 3 - p 1 * n 2 * (p 3) ^ 2 -
        (p 1) ^ 2 * p 2 * n 3 + (p 1) ^ 2 * n 2 * p 3 +
        n 1 * p 2 * (p 3) ^ 2 - n 1 * (p 2) ^ 2 * p 3) +
    (-1 : ℤ) ^ 1 * p 0 *
      (1 * (p 2) ^ 2 * n 3 - 1 * n 2 * (p 3) ^ 2 -
        (p 1) ^ 2 * 1 * n 3 + (p 1) ^ 2 * n 2 * 1 +
        n 1 * 1 * (p 3) ^ 2 - n 1 * (p 2) ^ 2 * 1) +
    (-1 : ℤ) ^ 2 * (p 0) ^ 2 *
      (1 * p 2 * n 3 - 1 * n 2 * p 3 - p 1 * 1 * n 3 +
        p 1 * n 2 * 1 + n 1 * 1 * p 3 - n 1 * p 2 * 1) +
    (-1 : ℤ) ^ 3 * n 0 *
      (1 * p 2 * (p 3) ^ 2 - 1 * (p 2) ^ 2 * p 3 -
        p 1 * 1 * (p 3) ^ 2 + p 1 * (p 2) ^ 2 * 1 +
        (p 1) ^ 2 * 1 * p 3 - (p 1) ^ 2 * p 2 * 1) = _
  ring

/-- Four points on an exact quadratic graph have zero determinant. No distinctness
of the bases or prime-square representations is required for this implication. -/
theorem fourPointDet_eq_zero_of_graph (p n : Fin 4 → ℤ) (B0 A B C : ℤ)
    (hB0 : B0 ≠ 0)
    (hgraph : ∀ i, B0 * n i = A * (p i) ^ 2 + B * p i + C) :
    fourPointDet p n = 0 := by
  apply (mul_eq_zero.mp (show B0 * fourPointDet p n = 0 from ?_)).resolve_left hB0
  rw [fourPointDet_eq]
  linear_combination
    -(p 2 - p 1) * (p 3 - p 1) * (p 3 - p 2) * hgraph 0 +
    (p 2 - p 0) * (p 3 - p 0) * (p 3 - p 2) * hgraph 1 -
    (p 1 - p 0) * (p 3 - p 0) * (p 3 - p 1) * hgraph 2 +
    (p 1 - p 0) * (p 2 - p 0) * (p 2 - p 1) * hgraph 3

/-- An explicit four-point congruence, even modulo the square of the first base.
This is the first-row cofactor expansion with the two square-divisible terms
removed. It requires neither primality nor distinctness nor an exact graph. -/
theorem fourPointDet_modEq_square (p m : Fin 4 → ℤ) :
    fourPointDet p (fun i => m i * (p i) ^ 2) ≡
      p 1 * p 2 * p 3 *
        (m 1 * p 1 * (p 3 - p 2) - m 2 * p 2 * (p 3 - p 1) +
          m 3 * p 3 * (p 2 - p 1)) -
      p 0 * ((m 3 - m 2) * (p 2) ^ 2 * (p 3) ^ 2 -
        (m 3 - m 1) * (p 1) ^ 2 * (p 3) ^ 2 +
        (m 2 - m 1) * (p 1) ^ 2 * (p 2) ^ 2) [ZMOD (p 0) ^ 2] := by
  rw [Int.modEq_iff_dvd, fourPointDet_eq]
  refine ⟨m 0 * (p 2 - p 1) * (p 3 - p 1) * (p 3 - p 2) -
    (m 1 * (p 1) ^ 2 * (p 3 - p 2) - m 2 * (p 2) ^ 2 * (p 3 - p 1) +
      m 3 * (p 3) ^ 2 * (p 2 - p 1)), ?_⟩
  dsimp
  ring

/-- The simpler first-base congruence. On an exact quadratic graph the left
side is zero by `fourPointDet_eq_zero_of_graph`, giving an arithmetic obstruction. -/
theorem fourPointDet_modEq (p m : Fin 4 → ℤ) :
    fourPointDet p (fun i => m i * (p i) ^ 2) ≡
      p 1 * p 2 * p 3 *
        (m 1 * p 1 * (p 3 - p 2) - m 2 * p 2 * (p 3 - p 1) +
          m 3 * p 3 * (p 2 - p 1)) [ZMOD p 0] := by
  rw [Int.modEq_iff_dvd, fourPointDet_eq]
  refine ⟨(m 3 - m 2) * (p 2) ^ 2 * (p 3) ^ 2 -
    (m 3 - m 1) * (p 1) ^ 2 * (p 3) ^ 2 +
    (m 2 - m 1) * (p 1) ^ 2 * (p 2) ^ 2 +
    p 0 * (m 0 * (p 2 - p 1) * (p 3 - p 1) * (p 3 - p 2) -
      (m 1 * (p 1) ^ 2 * (p 3 - p 2) - m 2 * (p 2) ^ 2 * (p 3 - p 1) +
        m 3 * (p 3) ^ 2 * (p 2 - p 1))), ?_⟩
  dsimp
  ring

/- Axiom audit. -/

#print axioms base_dvd_constant
#print axioms base_dvd_linear_of_constant_eq_zero
#print axioms mul_cofactor_eq_of_coefficients_eq_zero
#print axioms cofactor_eq_div_of_coefficients_eq_zero
#print axioms card_le_one_of_coefficients_eq_zero
#print axioms exists_nonzero_coefficient
#print axioms prod_primes_dvd_natAbs
#print axioms exists_nonzero_coefficient_prod_dvd
#print axioms pow_card_le_natAbs
#print axioms card_le_of_height
#print axioms card_le_max_one_of_height
#print axioms fourPointDet
#print axioms fourPointDet_eq
#print axioms fourPointDet_eq_zero_of_graph
#print axioms fourPointDet_modEq_square
#print axioms fourPointDet_modEq

end QuadraticGraph
