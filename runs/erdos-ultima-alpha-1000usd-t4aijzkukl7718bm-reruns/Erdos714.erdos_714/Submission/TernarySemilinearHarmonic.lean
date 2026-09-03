import Submission.HarmonicRoth

/-!
An exact row-configuration restriction for the ternary semilinear matrix host.
The trace equation gives a quartic with zero quadratic coefficient. Four
solutions are therefore harmonic. This does not assert graph freeness.
-/
noncomputable section
open Classical Polynomial Finset Matrix
set_option maxHeartbeats 3000000
namespace Erdos714TernarySemilinear
open Erdos714Harmonic
variable {F : Type*} [Field F]

/-- Vieta's second relation with all four distinct roots supplied explicitly. -/
lemma quartic_second_coefficient (A B C₀ : F) (t : Fin 4 → F)
    (ht : Function.Injective t)
    (hr : ∀ i, t i^4+A*t i^3+B*t i+C₀=0) :
    t 0*t 1+t 0*t 2+t 0*t 3+t 1*t 2+t 1*t 3+t 2*t 3=0 := by
  let P : F[X] := X^4+C A*X^3+C B*X+C C₀
  let Q : F[X] := ∏ i : Fin 4, (X-C (t i))
  have hm : P.Monic := by dsimp [P]; monicity!
  have hd : P.natDegree=4 := by dsimp [P]; compute_degree!
  have hdiv : Q∣P := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C ht hij
    · intro i _
      apply Polynomial.dvd_iff_isRoot.mpr
      simpa [P,Polynomial.IsRoot] using hr i
  have hQ : Q.Monic := Polynomial.monic_prod_X_sub_C t univ
  have hfac : P=Q := by
    have h := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hQ hdiv
      (by simp [Q,hd])
    simpa [hm.leadingCoeff] using h
  have hQexp : Q = X^4-C (t 0+t 1+t 2+t 3)*X^3+
      C (t 0*t 1+t 0*t 2+t 0*t 3+t 1*t 2+t 1*t 3+t 2*t 3)*X^2-
      C (t 0*t 1*t 2+t 0*t 1*t 3+t 0*t 2*t 3+t 1*t 2*t 3)*X+
      C (t 0*t 1*t 2*t 3) := by
    norm_num [Q,Fin.prod_univ_succ,map_add,map_mul,Fin.succ]
    ring!
  have h := congrArg (fun p : F[X] => p.coeff 2) hfac
  rw [hQexp] at h
  norm_num only [P,coeff_add,coeff_sub,coeff_C_mul,coeff_C,coeff_X_pow,coeff_X,
    ite_true,ite_false,one_mul,zero_mul,mul_zero,mul_one,add_zero,zero_add,sub_zero] at h
  exact h.symm

variable [CharP F 3]

lemma quartic_roots_harmonic (A B C₀ : F) (t : Fin 4 → F)
    (ht : Function.Injective t)
    (hr : ∀ i, t i^4+A*t i^3+B*t i+C₀=0) :
    Harmonic (t 0) (t 1) (t 2) (t 3) := by
  have h := quartic_second_coefficient A B C₀ t ht hr
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  dsimp [Harmonic]
  linear_combination -h+(t 0*t 2+t 1*t 3)*h3

abbrev Mat := Matrix (Fin 2) (Fin 2) F

def sigma (M : Mat (F := F)) : Mat (F := F) := fun i j => (frobenius F 3) (M i j)
def unipotent (T : F) : Mat (F := F) := !![1,T;0,1]

def trace2 (M : Mat (F := F)) : F := Matrix.trace (M*sigma M)

omit [CharP F 3] in
lemma unipotent_inv_mul (T : F) (M : Mat (F := F)) :
    unipotent (-T)*M =
      !![M 0 0-T*M 1 0, M 0 1-T*M 1 1; M 1 0, M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent,Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]

lemma trace2_entries (M : Mat (F := F)) :
    trace2 M=M 0 0^4+M 0 1*M 1 0^3+M 1 0*M 0 1^3+M 1 1^4 := by
  simp only [trace2,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    sigma,frobenius_def]
  ring

/-- The correct sign corresponds to the inverse of [[1,T],[0,1]]. -/
lemma shifted_trace (T : F) (M : Mat (F := F)) :
    trace2 (unipotent (-T)*M) =
      M 1 0^4*T^4-(M 0 0*M 1 0^3+M 1 0*M 1 1^3)*T^3-
      (M 1 0*M 0 0^3+M 1 1*M 1 0^3)*T+trace2 M := by
  rw [unipotent_inv_mul,trace2_entries,trace2_entries]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  linear_combination (-M 0 0^3*T*M 1 0+2*M 0 0^2*T^2*M 1 0^2-
    M 0 0*T^3*M 1 0^3-M 0 1^2*T*M 1 0*M 1 1+
    M 0 1*T^2*M 1 0*M 1 1^2)*h3

/-- Four unipotent rows sharing a nontriangular column must be harmonic. -/
theorem common_column_harmonic (M : Mat (F := F)) (hc : M 1 0≠0)
    (v : F) (t : Fin 4 → F) (ht : Function.Injective t)
    (h : ∀ i, trace2 (unipotent (-t i)*M)=v) :
    Harmonic (t 0) (t 1) (t 2) (t 3) := by
  apply quartic_roots_harmonic
    (-(M 0 0*M 1 0^3+M 1 0*M 1 1^3)/M 1 0^4)
    (-(M 1 0*M 0 0^3+M 1 1*M 1 0^3)/M 1 0^4)
    ((trace2 M-v)/M 1 0^4) t ht
  intro i
  have hi := h i
  rw [shifted_trace] at hi
  apply (mul_right_injective₀ (pow_ne_zero 4 hc))
  field_simp
  linear_combination hi

/-- Ordered semilinear norm; no commutativity of matrix factors is assumed. -/
def semiNorm (M : Mat (F := F)) : ℕ → Mat (F := F)
  | 0 => 1
  | n+1 => M*sigma (semiNorm M n)

lemma semiNorm_triangular (M : Mat (F := F)) (hc : M 1 0=0) (n : ℕ) :
    semiNorm M n 1 0=0 := by
  induction n with
  | zero => simp [semiNorm]
  | succ n hn => simp [semiNorm,Matrix.mul_apply,Fin.sum_univ_two,hc,sigma,hn]

omit [CharP F 3] in
lemma triangular_discr_square (M : Mat (F := F)) (hc : M 1 0=0) :
    IsSquare ((Matrix.trace M)^2-4*Matrix.det M) := by
  refine ⟨M 0 0-M 1 1,?_⟩
  rw [Matrix.trace_fin_two,Matrix.det_fin_two,hc]
  ring

/-- The elliptic semilinear-norm filter supplies precisely the nontriangular hypothesis. -/
theorem elliptic_common_column_harmonic (M : Mat (F := F)) (n : ℕ)
    (hell : ¬IsSquare ((Matrix.trace (semiNorm M n))^2-4*Matrix.det (semiNorm M n)))
    (v : F) (t : Fin 4 → F) (ht : Function.Injective t)
    (h : ∀ i, trace2 (unipotent (-t i)*M)=v) :
    Harmonic (t 0) (t 1) (t 2) (t 3) := by
  apply common_column_harmonic M _ v t ht h
  intro hc
  exact hell (triangular_discr_square _ (semiNorm_triangular M hc n))

/-- A harmonic-free row restriction bounds the degree inside every unipotent pencil
by three. This is a local statement, not global K44-freeness. -/
theorem no_four_selected_parameters {S : Set F} (hS : HarmonicFree S)
    (M : Mat (F := F)) (hc : M 1 0≠0) (v : F)
    (t : Fin 4 → F) (ht : Function.Injective t) (hmem : ∀ i, t i∈S)
    (h : ∀ i, trace2 (unipotent (-t i)*M)=v) : False := by
  have hh := common_column_harmonic M hc v t ht h
  rcases hS (hmem 0) (hmem 1) (hmem 2) (hmem 3) hh with h | h | h | h | h | h
  all_goals have he := congrArg Fin.val (ht h); norm_num at he

#print axioms quartic_second_coefficient
#print axioms quartic_roots_harmonic
#print axioms shifted_trace
#print axioms common_column_harmonic
#print axioms no_four_selected_parameters
#print axioms elliptic_common_column_harmonic
end Erdos714TernarySemilinear
