import FormalConjecturesUtil

/-!
# The algebraic characteristic obstruction for a complete quadrangle

Development only. These identities do not supply an unrestricted extremal
estimate, and do not settle the conjecture in `Spec.lean`.
-/

open Matrix


set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Erdos713

/-- The diagonal intersections of a complete quadrangle have determinant equal
to minus twice the product of its four vertex-triple determinants. -/
theorem quadrangle_diagonal_identity {R : Type*} [CommRing R]
    (a b c d : Fin 3 → R) :
    ((a ⨯₃ b) ⨯₃ (c ⨯₃ d)) ⬝ᵥ
      (((a ⨯₃ c) ⨯₃ (b ⨯₃ d)) ⨯₃ ((a ⨯₃ d) ⨯₃ (b ⨯₃ c))) =
      -2 * (a ⬝ᵥ (b ⨯₃ c)) * (a ⬝ᵥ (b ⨯₃ d)) *
        (a ⬝ᵥ (c ⨯₃ d)) * (b ⬝ᵥ (c ⨯₃ d)) := by
  simp only [cross_apply, vec3_dotProduct]
  dsimp
  ring

/-- In characteristic two the three diagonal intersections are collinear,
expressed by the vanishing scalar triple product of homogeneous coordinates. -/
theorem quadrangle_diagonal_charTwo {R : Type*} [CommRing R] [CharP R 2]
    (a b c d : Fin 3 → R) :
    ((a ⨯₃ b) ⨯₃ (c ⨯₃ d)) ⬝ᵥ
      (((a ⨯₃ c) ⨯₃ (b ⨯₃ d)) ⨯₃ ((a ⨯₃ d) ⨯₃ (b ⨯₃ c))) = 0 := by
  rw [quadrangle_diagonal_identity]
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  simp [htwo]

/-- Away from degenerate vertex triples, the diagonal determinant is nonzero
exactly when the field does not have characteristic two. -/
theorem quadrangle_diagonal_nonzero_iff {K : Type*} [Field K]
    (a b c d : Fin 3 → K)
    (habc : a ⬝ᵥ (b ⨯₃ c) ≠ 0) (habd : a ⬝ᵥ (b ⨯₃ d) ≠ 0)
    (hacd : a ⬝ᵥ (c ⨯₃ d) ≠ 0) (hbcd : b ⬝ᵥ (c ⨯₃ d) ≠ 0) :
    ((a ⨯₃ b) ⨯₃ (c ⨯₃ d)) ⬝ᵥ
      (((a ⨯₃ c) ⨯₃ (b ⨯₃ d)) ⨯₃ ((a ⨯₃ d) ⨯₃ (b ⨯₃ c))) ≠ 0 ↔
      (2 : K) ≠ 0 := by
  rw [quadrangle_diagonal_identity]
  simp [habc, habd, hacd, hbcd]

theorem exists_smul_cross_of_orthogonal {K : Type*} [Field K]
    (u v w : Fin 3 → K) (huv : u ⨯₃ v ≠ 0)
    (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0) :
    ∃ r : K, w = r • (u ⨯₃ v) := by
  have hzero : (u ⨯₃ v) ⨯₃ w = 0 := by
    rw [cross_cross_eq_smul_sub_smul, huw, hvw]
    simp
  have hdep : ¬ LinearIndependent K ![u ⨯₃ v, w] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, hzero]
    simp
  rw [LinearIndependent.pair_iff' huv] at hdep
  push_neg at hdep
  obtain ⟨r, hr⟩ := hdep
  exact ⟨r, hr.symm⟩

/-- The incidence table of the non-Fano configuration, with seven point roles
and nine line roles, independent of any chosen projective-plane implementation. -/
def homogeneousNonFanoLinePoints : Fin 9 → Finset (Fin 7) :=
  ![{0, 1, 4}, {2, 3, 4}, {0, 2, 5}, {1, 3, 5}, {0, 3, 6}, {1, 2, 6},
    {4, 5}, {4, 6}, {5, 6}]

theorem cross_cross_common_left {R : Type*} [CommRing R]
    (u v w : Fin 3 → R) :
    (u ⨯₃ v) ⨯₃ (u ⨯₃ w) = (u ⬝ᵥ (v ⨯₃ w)) • u := by
  ext i
  fin_cases i <;> simp only [cross_apply, vec3_dotProduct] <;> dsimp <;> ring

/-- The non-Fano incidence table cannot be represented by pairwise distinct
projective points and pairwise distinct projective lines in characteristic two.
Distinctness is expressed without choosing a projective-space quotient: the
cross product of the homogeneous vectors of any two roles must be nonzero. -/
theorem homogeneousNonFano_not_charTwo {K : Type*} [Field K] [CharP K 2]
    (p : Fin 7 → Fin 3 → K) (l : Fin 9 → Fin 3 → K)
    (hp : ∀ i j, i ≠ j → p i ⨯₃ p j ≠ 0)
    (hl : ∀ i j, i ≠ j → l i ⨯₃ l j ≠ 0)
    (hinc : ∀ i j, j ∈ homogeneousNonFanoLinePoints i → p j ⬝ᵥ l i = 0) :
    False := by
  obtain ⟨a0, ha0⟩ := exists_smul_cross_of_orthogonal
    (p 0) (p 1) (l 0) (hp 0 1 (by decide))
    (hinc 0 0 (by decide)) (hinc 0 1 (by decide))
  obtain ⟨a1, ha1⟩ := exists_smul_cross_of_orthogonal
    (p 2) (p 3) (l 1) (hp 2 3 (by decide))
    (hinc 1 2 (by decide)) (hinc 1 3 (by decide))
  obtain ⟨a2, ha2⟩ := exists_smul_cross_of_orthogonal
    (p 0) (p 2) (l 2) (hp 0 2 (by decide))
    (hinc 2 0 (by decide)) (hinc 2 2 (by decide))
  obtain ⟨a3, ha3⟩ := exists_smul_cross_of_orthogonal
    (p 1) (p 3) (l 3) (hp 1 3 (by decide))
    (hinc 3 1 (by decide)) (hinc 3 3 (by decide))
  obtain ⟨a4, ha4⟩ := exists_smul_cross_of_orthogonal
    (p 0) (p 3) (l 4) (hp 0 3 (by decide))
    (hinc 4 0 (by decide)) (hinc 4 3 (by decide))
  obtain ⟨a5, ha5⟩ := exists_smul_cross_of_orthogonal
    (p 1) (p 2) (l 5) (hp 1 2 (by decide))
    (hinc 5 1 (by decide)) (hinc 5 2 (by decide))
  obtain ⟨a6, ha6⟩ := exists_smul_cross_of_orthogonal
    (p 4) (p 5) (l 6) (hp 4 5 (by decide))
    (hinc 6 4 (by decide)) (hinc 6 5 (by decide))
  obtain ⟨a7, ha7⟩ := exists_smul_cross_of_orthogonal
    (p 4) (p 6) (l 7) (hp 4 6 (by decide))
    (hinc 7 4 (by decide)) (hinc 7 6 (by decide))
  obtain ⟨x0, hx0⟩ := exists_smul_cross_of_orthogonal
    (l 0) (l 1) (p 4) (hl 0 1 (by decide))
    (by simpa only [dotProduct_comm] using hinc 0 4 (by decide))
    (by simpa only [dotProduct_comm] using hinc 1 4 (by decide))
  obtain ⟨x1, hx1⟩ := exists_smul_cross_of_orthogonal
    (l 2) (l 3) (p 5) (hl 2 3 (by decide))
    (by simpa only [dotProduct_comm] using hinc 2 5 (by decide))
    (by simpa only [dotProduct_comm] using hinc 3 5 (by decide))
  obtain ⟨x2, hx2⟩ := exists_smul_cross_of_orthogonal
    (l 4) (l 5) (p 6) (hl 4 5 (by decide))
    (by simpa only [dotProduct_comm] using hinc 4 6 (by decide))
    (by simpa only [dotProduct_comm] using hinc 5 6 (by decide))
  have hdiag : p 4 ⬝ᵥ (p 5 ⨯₃ p 6) = 0 := by
    simp [hx0, hx1, hx2, ha0, ha1, ha2, ha3, ha4, ha5,
      map_smul, smul_dotProduct, dotProduct_smul, quadrangle_diagonal_charTwo]
  apply hl 6 7 (by decide)
  simp [ha6, ha7, map_smul, cross_cross_common_left, hdiag]

/-- The diagonal collinearity conclusion needs only the six sidelines, not
projective distinctness of the three added diagonal-line roles. -/
theorem homogeneousNonFano_diagonal_zero {K : Type*} [Field K] [CharP K 2]
    (p : Fin 7 → Fin 3 → K) (l : Fin 9 → Fin 3 → K)
    (hp : ∀ i j, i ≠ j → p i ⨯₃ p j ≠ 0)
    (h01 : l 0 ⨯₃ l 1 ≠ 0) (h23 : l 2 ⨯₃ l 3 ≠ 0) (h45 : l 4 ⨯₃ l 5 ≠ 0)
    (hinc : ∀ i j, j ∈ homogeneousNonFanoLinePoints i → p j ⬝ᵥ l i = 0) :
    p 4 ⬝ᵥ (p 5 ⨯₃ p 6) = 0 := by
  obtain ⟨a0, ha0⟩ := exists_smul_cross_of_orthogonal
    (p 0) (p 1) (l 0) (hp 0 1 (by decide))
    (hinc 0 0 (by decide)) (hinc 0 1 (by decide))
  obtain ⟨a1, ha1⟩ := exists_smul_cross_of_orthogonal
    (p 2) (p 3) (l 1) (hp 2 3 (by decide))
    (hinc 1 2 (by decide)) (hinc 1 3 (by decide))
  obtain ⟨a2, ha2⟩ := exists_smul_cross_of_orthogonal
    (p 0) (p 2) (l 2) (hp 0 2 (by decide))
    (hinc 2 0 (by decide)) (hinc 2 2 (by decide))
  obtain ⟨a3, ha3⟩ := exists_smul_cross_of_orthogonal
    (p 1) (p 3) (l 3) (hp 1 3 (by decide))
    (hinc 3 1 (by decide)) (hinc 3 3 (by decide))
  obtain ⟨a4, ha4⟩ := exists_smul_cross_of_orthogonal
    (p 0) (p 3) (l 4) (hp 0 3 (by decide))
    (hinc 4 0 (by decide)) (hinc 4 3 (by decide))
  obtain ⟨a5, ha5⟩ := exists_smul_cross_of_orthogonal
    (p 1) (p 2) (l 5) (hp 1 2 (by decide))
    (hinc 5 1 (by decide)) (hinc 5 2 (by decide))
  obtain ⟨x0, hx0⟩ := exists_smul_cross_of_orthogonal
    (l 0) (l 1) (p 4) h01
    (by simpa only [dotProduct_comm] using hinc 0 4 (by decide))
    (by simpa only [dotProduct_comm] using hinc 1 4 (by decide))
  obtain ⟨x1, hx1⟩ := exists_smul_cross_of_orthogonal
    (l 2) (l 3) (p 5) h23
    (by simpa only [dotProduct_comm] using hinc 2 5 (by decide))
    (by simpa only [dotProduct_comm] using hinc 3 5 (by decide))
  obtain ⟨x2, hx2⟩ := exists_smul_cross_of_orthogonal
    (l 4) (l 5) (p 6) h45
    (by simpa only [dotProduct_comm] using hinc 4 6 (by decide))
    (by simpa only [dotProduct_comm] using hinc 5 6 (by decide))
  simp [hx0, hx1, hx2, ha0, ha1, ha2, ha3, ha4, ha5,
    map_smul, smul_dotProduct, dotProduct_smul, quadrangle_diagonal_charTwo]

end Erdos713

#print axioms Erdos713.quadrangle_diagonal_identity
#print axioms Erdos713.quadrangle_diagonal_charTwo
#print axioms Erdos713.quadrangle_diagonal_nonzero_iff
#print axioms Erdos713.homogeneousNonFano_not_charTwo

#print axioms Erdos713.homogeneousNonFano_diagonal_zero
