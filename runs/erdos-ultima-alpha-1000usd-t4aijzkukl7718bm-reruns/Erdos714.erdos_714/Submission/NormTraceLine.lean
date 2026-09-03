import Submission.NormLineBound

/-!
A scalar-line common-neighbor bound for the additive norm-times-trace lift.
This does not handle arbitrary rows and does not settle Erdős 714.
-/
noncomputable section
open Polynomial Module Finset
namespace Erdos714NormTraceLine

section PolynomialRecovery
variable {F : Type*} [Field F]

/-- The linear trace factor makes the norm polynomial recoverable from a
shift profile, including its otherwise invisible constant coefficient. -/
theorem profile_recovery (d : ℕ) (hd : 0 < d)
    (hdF : (d : F) ≠ 0) (hd1F : (d + 1 : F) ≠ 0)
    (P Q : F[X]) (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hPtop : P.coeff d = 1) (hQtop : Q.coeff d = 1)
    (b c : F) (t : Fin (d+1) ↪ F)
    (h : ∀ i,
      P.eval (t i) * (P.coeff (d-1) + d*t i) - b =
      Q.eval (t i) * (Q.coeff (d-1) + d*t i) - c) : P = Q ∧ b = c := by
  let A : F[X] := C (P.coeff (d-1)) + C (d : F) * X
  let B : F[X] := C (Q.coeff (d-1)) + C (d : F) * X
  let R : F[X] := P*A-Q*B-C (b-c)
  have hA : A.natDegree ≤ 1 := by
    dsimp only [A]
    compute_degree!
  have hB : B.natDegree ≤ 1 := by
    dsimp only [B]
    compute_degree!
  have hR : R.natDegree ≤ d+1 := by
    dsimp only [R]
    exact natDegree_sub_C.le.trans <| (natDegree_sub_le _ _).trans
      (max_le (natDegree_mul_le.trans (Nat.add_le_add hP hA))
        (natDegree_mul_le.trans (Nat.add_le_add hQ hB)))
  have hRt : R.coeff (d+1) = 0 := by
    have hp : P.coeff (d+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hq : Q.coeff (d+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [R, A, B, mul_add, ← mul_assoc, coeff_sub, coeff_add,
      coeff_mul_C, coeff_mul_X, hp, hq, hPtop, hQtop, zero_mul, one_mul,
      zero_add, sub_self, coeff_C, if_neg (show d+1 ≠ 0 by omega)]
  have hRdeg : R.natDegree ≤ d := by
    simpa only [Nat.add_sub_cancel] using natDegree_le_pred hR hRt
  have hRzero : R = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero R t.injective
    · intro i
      have hi := h i
      dsimp [R, A, B]
      simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X]
      linear_combination hi
    · simpa using (Nat.lt_succ_of_le hRdeg)
  have htrace : P.coeff (d-1) = Q.coeff (d-1) := by
    have he := congrArg (fun p : F[X] => p.coeff d) hRzero
    have hd' : d = (d-1)+1 := by omega
    have hm (p : F[X]) : (p * C (d : F) * X).coeff d = p.coeff (d-1) * d := by
      conv_lhs => rw [hd']
      rw [coeff_mul_X, coeff_mul_C, ← hd']
    simp only [R, A, B, mul_add, ← mul_assoc, coeff_sub, coeff_add,
      coeff_mul_C, hm, hPtop, hQtop, one_mul, coeff_zero,
      coeff_C, if_neg (show d ≠ 0 by omega), sub_zero] at he
    apply (mul_eq_zero.mp (show (d+1 : F) * (P.coeff (d-1)-Q.coeff (d-1)) = 0 by
      linear_combination he)).resolve_left hd1F |> sub_eq_zero.mp
  have hAB : A = B := by simp only [A, B, htrace]
  have hbc : b = c := by
    have he := congrArg (Polynomial.eval (-P.coeff (d-1)/(d : F))) hRzero
    have hz : (P.coeff (d-1) + (d : F) * (-P.coeff (d-1)/d)) = 0 := by
      field_simp
      ring
    simp only [R, ← hAB, eval_sub, eval_mul, eval_zero, A,
      eval_add, eval_C, eval_X, hz, mul_zero, sub_self, zero_sub] at he
    exact sub_eq_zero.mp (neg_eq_zero.mp he)
  have hAzero : A ≠ 0 := by
    intro he
    have hh := congrArg (fun p : F[X] => p.coeff 1) he
    simp only [A, coeff_add, coeff_C, coeff_C_mul_X, if_true,
      if_neg (show (1 : ℕ) ≠ 0 by decide), zero_add, coeff_zero] at hh
    exact hdF hh
  refine ⟨?_, hbc⟩
  have he : (P-Q)*A = 0 := by
    simpa only [R, ← hAB, hbc, sub_self, C_0, sub_zero, ← sub_mul] using hRzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hAzero)
end PolynomialRecovery

section FieldNorm
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- The norm polynomial on base-field shifts of `x`. -/
def shiftPoly (x : E) : F[X] :=
  (Algebra.leftMulMatrix (Module.finBasis F E) (-x)).charpoly

lemma shiftPoly_monic (x : E) : (shiftPoly (F := F) x).Monic := Matrix.charpoly_monic _

lemma shiftPoly_degree (x : E) : (shiftPoly (F := F) x).natDegree = finrank F E := by
  simp [shiftPoly, Matrix.charpoly_natDegree_eq_dim]

lemma shiftPoly_eval (x : E) (t : F) :
    (shiftPoly (F := F) x).eval t = Algebra.norm F (x+algebraMap F E t) := by
  simpa [shiftPoly, Algebra.smul_def] using
    Erdos714NormLine.norm_shift_charpoly (F := F) x 1 one_ne_zero t

lemma shiftPoly_next (x : E) :
    (shiftPoly (F := F) x).coeff (finrank F E - 1) = Algebra.trace F E x := by
  letI : Nonempty (Fin (finrank F E)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  have h := Matrix.trace_eq_neg_charpoly_coeff
    (Algebra.leftMulMatrix (Module.finBasis F E) (-x))
  rw [← Algebra.trace_eq_matrix_trace, map_neg] at h
  simpa [shiftPoly] using neg_injective h.symm

lemma shiftPoly_root (x : E) : aeval (-x) (shiftPoly (F := F) x) = 0 := by
  apply (injective_iff_map_eq_zero (G := E)
    (Algebra.leftMulMatrix (Module.finBasis F E))).mp
    (Algebra.leftMulMatrix_injective (Module.finBasis F E))
  rw [← Polynomial.aeval_algHom_apply]
  exact Matrix.aeval_self_charpoly _

/-- The actual field norm times the actual field trace. -/
def value (x : E) : F := Algebra.norm F x * Algebra.trace F E x

lemma value_shift (x : E) (t : F) :
    value (F := F) (x+algebraMap F E t) =
      (shiftPoly (F := F) x).eval t *
        ((shiftPoly (F := F) x).coeff (finrank F E-1)+(finrank F E : F)*t) := by
  rw [value, (Algebra.trace F E).map_add, Algebra.trace_algebraMap,
    ← shiftPoly_eval, shiftPoly_next]
  simp only [nsmul_eq_mul]

/-- Equal additive shift profiles force equal characteristic polynomials and
weights. Neither a finite base field nor a Galois hypothesis is needed. -/
theorem norm_trace_recovery
    (hd : (finrank F E : F) ≠ 0) (hd1 : (finrank F E + 1 : F) ≠ 0)
    (x y : E) (b c : F) (t : Fin (finrank F E+1) ↪ F)
    (h : ∀ i, value (F := F) (x+algebraMap F E (t i))-b =
      value (F := F) (y+algebraMap F E (t i))-c) :
    shiftPoly (F := F) x = shiftPoly (F := F) y ∧ b = c := by
  apply profile_recovery (finrank F E) Module.finrank_pos hd hd1
    (shiftPoly x) (shiftPoly y) (shiftPoly_degree x).le (shiftPoly_degree y).le
  · rw [← shiftPoly_degree x]
    exact (shiftPoly_monic x).coeff_natDegree
  · rw [← shiftPoly_degree y]
    exact (shiftPoly_monic y).coeff_natDegree
  · simpa only [value_shift] using h

/-- The scalar-line rows have at most the extension degree many common
columns. A column is the entire pair `(point, weight)`, not just its point. -/
theorem scalar_line_columns_bound
    (hd : (finrank F E : F) ≠ 0) (hd1 : (finrank F E+1 : F) ≠ 0)
    (t : Fin (finrank F E+1) ↪ F) (c : Fin (finrank F E+1) → F)
    (S : Finset (E × F))
    (hS : ∀ z ∈ S, ∀ i, c i + z.2 = value (F := F) (z.1+algebraMap F E (t i))) :
    S.card ≤ finrank F E := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · simp
  have hrec (z : E × F) (hz : z ∈ S) :
      shiftPoly (F := F) z.1 = shiftPoly (F := F) z₀.1 ∧ z.2 = z₀.2 := by
    apply norm_trace_recovery hd hd1 z.1 z₀.1 z.2 z₀.2 t
    intro i
    rw [← hS z hz i, ← hS z₀ hz₀ i]
    ring
  let P : E[X] := (shiftPoly (F := F) z₀.1).map (algebraMap F E)
  have hp : P ≠ 0 := ((shiftPoly_monic z₀.1).map (algebraMap F E)).ne_zero
  have hs : S.image (fun z => -z.1) ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hp]
    dsimp only [P]
    rw [IsRoot.def, eval_map, ← (hrec z hz).1]
    exact shiftPoly_root z.1
  have hi : Set.InjOn (fun z : E × F => -z.1) (S : Set (E × F)) := by
    intro z hz w hw hzw
    exact Prod.ext (neg_injective hzw) ((hrec z hz).2.trans (hrec w hw).2.symm)
  calc
    S.card = (S.image (fun z => -z.1)).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hs
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' _
    _ ≤ (shiftPoly (F := F) z₀.1).natDegree := Polynomial.natDegree_map_le
    _ = finrank F E := shiftPoly_degree z₀.1

/-- The fourth-case specialization, with its characteristic restrictions explicit. -/
theorem cubic_scalar_line_bound (hdim : finrank F E = 3)
    (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0)
    (t : Fin 4 ↪ F) (c : Fin 4 → F) (S : Finset (E × F))
    (hS : ∀ z ∈ S, ∀ i, c i + z.2 = value (F := F) (z.1+algebraMap F E (t i))) :
    S.card ≤ 3 := by
  have h := scalar_line_columns_bound (F := F) (E := E)
  rw [hdim] at h
  exact h h3 (by convert h4 using 1; norm_num) t c S hS

end FieldNorm
#print axioms profile_recovery
#print axioms norm_trace_recovery
#print axioms scalar_line_columns_bound
#print axioms cubic_scalar_line_bound
end Erdos714NormTraceLine
