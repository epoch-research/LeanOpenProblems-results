import FormalConjecturesUtil

/-!
A valid local ingredient for norm-evaluation codes: a nonconstant affine line
has at most the extension degree many points of any fixed norm. This is not
a common-neighbor bound for arbitrary rows and does not settle Erdős 714.
-/
noncomputable section
open Polynomial Module Finset
namespace Erdos714NormLine
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- A monic characteristic polynomial controls norms along an affine scalar line. -/
lemma norm_shift_charpoly (p r : E) (hr : r ≠ 0) (t : F) :
    ((Algebra.leftMulMatrix (Module.finBasis F E) (-p/r)).charpoly).eval t =
      Algebra.norm F (p+t • r) / Algebra.norm F r := by
  let b := Module.finBasis F E
  have hs : Matrix.scalar (Fin (finrank F E)) t =
      (Algebra.leftMulMatrix b) (algebraMap F E t) := by
    rw [AlgHom.commutes]
    rfl
  rw [Matrix.eval_charpoly, hs]
  have hm : (Algebra.leftMulMatrix b) (algebraMap F E t) -
      (Algebra.leftMulMatrix b) (-p/r) =
      (Algebra.leftMulMatrix b) (algebraMap F E t+p/r) := by
    rw [← map_sub]
    congr 1
    ring
  rw [hm, ← Algebra.norm_eq_matrix_det]
  have hrn : Algebra.norm F r ≠ 0 := Algebra.norm_ne_zero_iff.mpr hr
  apply (eq_div_iff hrn).mpr
  rw [← map_mul]
  congr 1
  rw [Algebra.smul_def]
  field_simp
  ring

/-- The degree bound is uniform in the norm value, including zero. -/
theorem fixed_norm_line_bound (p r : E) (hr : r ≠ 0) (c : F) (S : Finset F)
    (hS : ∀ t ∈ S, Algebra.norm F (p+t • r) = c) : S.card ≤ finrank F E := by
  classical
  let M := Algebra.leftMulMatrix (Module.finBasis F E) (-p/r)
  let P : F[X] := M.charpoly-C (c/Algebra.norm F r)
  have hd : P.natDegree = finrank F E := by
    simp only [P, natDegree_sub_C, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hpos : 0 < finrank F E := Module.finrank_pos
  have hp : P ≠ 0 := by intro hp; have hz := hd; rw [hp, natDegree_zero] at hz; omega
  have hs : S ⊆ P.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    simp only [IsRoot.def, P, eval_sub, eval_C, M, norm_shift_charpoly p r hr, hS t ht, sub_self]
  calc
    S.card ≤ P.roots.toFinset.card := card_le_card hs
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' _
    _ = _ := hd

/-- Four distinct scalars with equal cubic norms force a zero direction. -/
theorem cubic_direction_zero (hd : finrank F E = 3) (p r : E) (c : F)
    (t : Fin 4 ↪ F) (ht : ∀ i, Algebra.norm F (p+t i • r) = c) : r = 0 := by
  classical
  by_contra hr
  have h := fixed_norm_line_bound p r hr c (Finset.univ.map t) (by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
    exact ht i)
  simp only [card_map, card_univ, Fintype.card_fin, hd] at h
  omega

/-- In a cubic polynomial quotient, four equal norm evaluations on an affine
polynomial line force the direction polynomial to be divisible by the modulus.
The statement concerns the actual quotient-field norm, not an unproved resultant identity. -/
theorem polynomial_direction_dvd (P R Q : F[X]) (hQ : Irreducible Q)
    (hdQ : Q.natDegree = 3) (c : F) (t : Fin 4 ↪ F)
    (ht : ∀ i, Algebra.norm F ((AdjoinRoot.mk Q) (P+C (t i)*R)) = c) : Q ∣ R := by
  letI : Fact (Irreducible Q) := ⟨hQ⟩
  letI : FiniteDimensional F (AdjoinRoot Q) := (AdjoinRoot.powerBasis hQ.ne_zero).finite
  have hd : finrank F (AdjoinRoot Q) = 3 := by
    rw [(AdjoinRoot.powerBasis hQ.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdQ]
  apply AdjoinRoot.mk_eq_zero.mp
  apply cubic_direction_zero hd ((AdjoinRoot.mk Q) P) ((AdjoinRoot.mk Q) R) c t
  intro i
  simpa only [map_add, map_mul, AdjoinRoot.mk_C, Algebra.smul_def] using ht i

/-- Distinct monic cubic coordinate polynomials cannot both divide a nonzero
polynomial direction of degree at most three. Thus an affine line of four
quartic rows has at most one common coordinate in the norm-evaluation code. -/
theorem cubic_coordinate_bound (P R : F[X]) (hR : R ≠ 0) (hdR : R.natDegree ≤ 3)
    (t : Fin 4 ↪ F) (S : Finset F[X])
    (hS : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.natDegree = 3 ∧
      ∃ c : F, ∀ i, Algebra.norm F ((AdjoinRoot.mk Q) (P+C (t i)*R)) = c) :
    S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro Q hQ U hU
  obtain ⟨hmQ, hiQ, hdQ, cQ, hcQ⟩ := hS Q hQ
  obtain ⟨hmU, hiU, hdU, cU, hcU⟩ := hS U hU
  have haQ := Polynomial.associated_of_dvd_of_natDegree_le
    (polynomial_direction_dvd P R Q hiQ hdQ cQ t hcQ) hR (by rwa [hdQ])
  have haU := Polynomial.associated_of_dvd_of_natDegree_le
    (polynomial_direction_dvd P R U hiU hdU cU t hcU) hR (by rwa [hdU])
  exact Polynomial.eq_of_monic_of_associated hmQ hmU (haQ.trans haU.symm)

#print axioms norm_shift_charpoly
#print axioms fixed_norm_line_bound
#print axioms cubic_direction_zero
#print axioms polynomial_direction_dvd
#print axioms cubic_coordinate_bound
end Erdos714NormLine
