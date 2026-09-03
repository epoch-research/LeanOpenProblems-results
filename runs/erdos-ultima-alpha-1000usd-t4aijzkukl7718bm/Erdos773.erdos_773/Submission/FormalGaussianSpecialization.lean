import Submission.FormalGaussianSidon

/-!
A verified specialization failure for the exact formal Gaussian-Eisenstein
family. This is a counterexample to a transfer rule, not to Erdős 773.
-/
namespace Erdos773.FormalGaussianSpecialization
open Polynomial Finset FormalGaussianSidon
noncomputable section
set_option maxHeartbeats 2000000

lemma prime_base : Nat.Prime 1439 := by decide +kernel

/-- The lower coefficients, before multiplying by six and adjoining X^19. -/
def parameter (j : Fin 4) : ℤ[X] := ![
  1+4*X+8*X^2+6*X^3+21*X^4+3*X^5+10*X^6+24*X^7+20*X^8+
    63*X^9+5*X^10+22*X^11+40*X^12+28*X^13+105*X^14+
    12*X^15+36*X^16+60*X^17+12*X^18,
  1+6*X+8*X^2+4*X^3+21*X^4+5*X^5+28*X^6+40*X^7+22*X^8+
    105*X^9+3*X^10+20*X^11+24*X^12+10*X^13+63*X^14+
    12*X^15+60*X^16+36*X^17+12*X^18,
  1+6*X+8*X^2+4*X^3+21*X^4+3*X^5+20*X^6+24*X^7+10*X^8+
    63*X^9+5*X^10+28*X^11+40*X^12+22*X^13+105*X^14+
    12*X^15+60*X^16+36*X^17+12*X^18,
  1+4*X+8*X^2+6*X^3+21*X^4+5*X^5+22*X^6+40*X^7+28*X^8+
    105*X^9+3*X^10+10*X^11+24*X^12+20*X^13+63*X^14+
    12*X^15+36*X^16+60*X^17+12*X^18] j

lemma admissible (j : Fin 4) : Admissible 19 (parameter j) := by
  fin_cases j <;> constructor
  all_goals first | (dsimp [parameter]; compute_degree <;> norm_num) | norm_num [parameter]

/-- The formal discrepancy is nonzero and contains the specialization factor. -/
lemma norm_difference :
    (encoding 19 (parameter 0))^2+(encoding 19 (parameter 1))^2-
      (encoding 19 (parameter 2))^2-(encoding 19 (parameter 3))^2 =
        48*X^25*(1439-X)*(X-1)*(X^5-1) := by
  dsimp [encoding, parameter]
  simp only [map_ofNat]
  ring

lemma discrepancy_ne_zero :
    (encoding 19 (parameter 0))^2+(encoding 19 (parameter 1))^2-
      (encoding 19 (parameter 2))^2-(encoding 19 (parameter 3))^2 ≠ 0 := by
  rw [norm_difference]
  intro he
  have hh := congrArg (Polynomial.eval 2) he
  norm_num at hh

def value (j : Fin 4) : ℤ := (encoding 19 (parameter j)).eval 1439

lemma collision : value 0^2+value 1^2=value 2^2+value 3^2 := by
  have hh := congrArg (Polynomial.eval 1439) norm_difference
  simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_ofNat,
    eval_one, sub_self, mul_zero, zero_mul] at hh
  change value 0^2+value 1^2-value 2^2-value 3^2=0 at hh
  linarith

lemma value_eq : value = ![
    1057866062315417538960420782964308843455364493876662244501815,
    1057796062953470585940337019760124841394812182278015855915383,
    1057796062953511732919500894428282060292860586790288689354583,
    1057866062315376394703966699664848499544458250295356285722455] := by
  funext j
  fin_cases j <;> norm_num [value, encoding, parameter]

lemma positive (j : Fin 4) : 0<value j := by
  rw [value_eq]
  fin_cases j <;> decide +kernel

lemma ordered_values : value 1<value 2 ∧ value 2<value 3 ∧ value 3<value 0 := by
  rw [value_eq]
  decide +kernel

lemma value_injective : Function.Injective value := by
  rw [value_eq]
  decide +kernel

lemma formal_square_sidon :
    IsSidon ((univ.image (fun j : Fin 4 => (encoding 19 (parameter j))^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon 19)
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j,_,rfl⟩ := mem_image.mp hf
  exact ⟨parameter j,admissible j,rfl⟩

/-- Evaluation is even injective on the four root values, but its image
of their formal square-Sidon set is not Sidon. -/
theorem specialization_not_sidon :
    ¬IsSidon ((univ.image (fun j : Fin 4 => value j^2)) : Set ℤ) := by
  intro hs
  have hm (j : Fin 4) : value j^2 ∈ univ.image (fun j : Fin 4 => value j^2) :=
    mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have h02 : value 2^2<value 0^2 :=
    (sq_lt_sq₀ (positive 2).le (positive 0).le).mpr
      (ordered_values.2.1.trans ordered_values.2.2)
  have h03 : value 3^2<value 0^2 :=
    (sq_lt_sq₀ (positive 3).le (positive 0).le).mpr ordered_values.2.2
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) collision with h | h <;> omega

#print axioms prime_base
#print axioms admissible
#print axioms norm_difference
#print axioms discrepancy_ne_zero
#print axioms collision
#print axioms value_injective
#print axioms formal_square_sidon
#print axioms specialization_not_sidon
end
end Erdos773.FormalGaussianSpecialization
