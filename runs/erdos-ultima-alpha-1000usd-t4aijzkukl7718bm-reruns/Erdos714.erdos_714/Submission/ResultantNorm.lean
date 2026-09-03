import Submission.NormLineBound

/-!
The actual polynomial resultant equals the norm of evaluation in an irreducible
monic polynomial quotient over a perfect field. This connects the local
norm-line bound to resultant evaluation; it is not a global freeness theorem.
-/
noncomputable section
open Polynomial
namespace Erdos714ResultantNorm
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The norm of a polynomial in a separable power-basis generator is a resultant. -/
theorem powerBasis_norm_aeval [Algebra.IsSeparable F E]
    (b : PowerBasis F E) (P : F[X]) :
    Algebra.norm F (aeval b.gen P) = (minpoly F b.gen).resultant P := by
  classical
  letI : FiniteDimensional F E := b.finite
  let L := AlgebraicClosure F
  let f := algebraMap F L
  let Q := minpoly F b.gen
  have hQ : Q.Monic := minpoly.monic b.isIntegral_gen
  have hsep : Q.Separable := Algebra.IsSeparable.isSeparable F b.gen
  apply f.injective
  rw [Algebra.norm_eq_prod_embeddings F L]
  have hp : (∏ σ : E →ₐ[F] L, σ (aeval b.gen P)) =
      ((Q.map f).roots.map (P.map f).eval).prod := by
    rw [Fintype.prod_equiv b.liftEquiv' (fun σ => σ (aeval b.gen P))
      (fun x => (P.map f).eval x) (by
        intro σ
        simp only [PowerBasis.liftEquiv'_apply_coe, eval_map]
        exact (aeval_algHom_apply σ b.gen P).symm)]
    rw [Finset.prod_mem_multiset _ _ (fun x => (P.map f).eval x) (by intro x; rfl),
      Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr (nodup_roots hsep.map)]
  rw [hp]
  change _ = f (Q.resultant P)
  rw [← resultant_map_map, ← natDegree_map f,
    resultant_eq_prod_eval _ _ _ (natDegree_map_le.trans le_rfl) (IsAlgClosed.splits _),
    (hQ.map f).leadingCoeff, one_pow, one_mul]

/-- Quotient-field interpretation, with the ordering `Res(Q,P)`. -/
theorem quotient_norm [PerfectField F] (P Q : F[X]) (hQ : Irreducible Q)
    (hmQ : Q.Monic) :
    Algebra.norm F ((AdjoinRoot.mk Q) P) = Q.resultant P := by
  letI : Fact (Irreducible Q) := ⟨hQ⟩
  let b := AdjoinRoot.powerBasis hQ.ne_zero
  letI : FiniteDimensional F (AdjoinRoot Q) := b.finite
  have hb : b.gen = AdjoinRoot.root Q := AdjoinRoot.powerBasis_gen _
  have hmin : minpoly F b.gen = Q := by
    rw [hb, AdjoinRoot.minpoly_root hQ.ne_zero, hmQ.leadingCoeff]
    simp
  have h := powerBasis_norm_aeval b P
  rw [hmin, hb, AdjoinRoot.aeval_eq] at h
  exact h

/-- Reversing the resultant introduces no sign for an even-degree row. -/
theorem quotient_norm_even [PerfectField F] (P Q : F[X]) (hQ : Irreducible Q)
    (hmQ : Q.Monic) (hP : Even P.natDegree) :
    Algebra.norm F ((AdjoinRoot.mk Q) P) = P.resultant Q := by
  rw [quotient_norm P Q hQ hmQ, resultant_comm Q P,
    (hP.mul_left Q.natDegree).neg_one_pow, one_mul]

/-- Direct resultant version of the norm-line root bound. The resultant is
ordered with the fixed coordinate polynomial first, so no degree-parity
assumption is needed on the varying rows. -/
theorem fixed_resultant_line_bound [PerfectField F] (P R Q : F[X])
    (hQ : Irreducible Q) (hmQ : Q.Monic) (hR : ¬ Q ∣ R)
    (c : F) (S : Finset F)
    (hS : ∀ t ∈ S, Q.resultant (P+C t*R) = c) : S.card ≤ Q.natDegree := by
  letI : Fact (Irreducible Q) := ⟨hQ⟩
  letI : FiniteDimensional F (AdjoinRoot Q) := (AdjoinRoot.powerBasis hQ.ne_zero).finite
  have hnR : (AdjoinRoot.mk Q) R ≠ 0 := by
    rwa [ne_eq, AdjoinRoot.mk_eq_zero]
  have h := Erdos714NormLine.fixed_norm_line_bound ((AdjoinRoot.mk Q) P)
    ((AdjoinRoot.mk Q) R) hnR c S (by
      intro t ht
      have hnorm := (quotient_norm (P+C t*R) Q hQ hmQ).trans (hS t ht)
      simpa only [map_add, map_mul, AdjoinRoot.mk_C, Algebra.smul_def] using hnorm)
  rwa [(AdjoinRoot.powerBasis hQ.ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h

/-- Four affine-line quartic rows agree at at most one monic irreducible cubic
coordinate in the actual resultant code. This handles the line case only;
it makes no claim about four affinely independent rows. -/
theorem quartic_line_coordinate_bound [PerfectField F] (P R : F[X])
    (hdP : P.natDegree = 4) (hR : R ≠ 0) (hdR : R.natDegree ≤ 3)
    (t : Fin 4 ↪ F) (S : Finset F[X])
    (hS : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.natDegree = 3 ∧
      ∃ c : F, ∀ i, (P+C (t i)*R).resultant Q = c) : S.card ≤ 1 := by
  apply Erdos714NormLine.cubic_coordinate_bound P R hR hdR t S
  intro Q hQS
  obtain ⟨hmQ, hiQ, hdQ, c, hc⟩ := hS Q hQS
  refine ⟨hmQ, hiQ, hdQ, c, fun i => ?_⟩
  have hdeg : (P+C (t i)*R).natDegree = 4 := by
    rw [natDegree_add_eq_left_of_natDegree_lt, hdP]
    exact (natDegree_C_mul_le _ R).trans_lt (by omega)
  rw [quotient_norm_even _ Q hiQ hmQ (by rw [hdeg]; decide)]
  exact hc i

#print axioms powerBasis_norm_aeval
#print axioms quotient_norm
#print axioms quotient_norm_even
#print axioms fixed_resultant_line_bound
#print axioms quartic_line_coordinate_bound
end Erdos714ResultantNorm
