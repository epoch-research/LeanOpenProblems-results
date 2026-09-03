import Submission.EvenPolynomialModel

/-! Additive coordinates and exact reconstruction for the even polynomial
model. The first 2m+1 values are free; the vanishing next difference determines
the final value. -/
namespace Erdos3EvenPolynomialCoordinates
open Finset Erdos3PairedEvenModelCounting Erdos3EvenDifferencePairing
  Erdos3EvenPolynomialModel Erdos3HigherPhaseDifferences Erdos3LocalPolynomialPhaseExtension
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G]

lemma binomialTail_add (m : ℕ) (u v : Fin m → G) :
    binomialTail m (u+v) = binomialTail m u+binomialTail m v := by
  simp only [binomialTail,Pi.add_apply,smul_add,sum_add_distrib,neg_add]

lemma binomialTail_zero (m : ℕ) : binomialTail m (0 : Fin m → G) = 0 := by
  simp only [binomialTail,Pi.zero_apply,smul_zero,sum_const_zero,neg_zero]

lemma paired_binomial_add (m : ℕ) (p r : G × (Fin m → G) × (Fin m → G))
    (i : Option (Fin m) ⊕ Option (Fin m)) :
    pairedValues (binomialTail m) (p+r) i =
      pairedValues (binomialTail m) p i+pairedValues (binomialTail m) r i := by
  cases i <;> rename_i i <;> cases i <;>
    simp only [pairedValues,Prod.fst_add,Prod.snd_add,Pi.add_apply,binomialTail_add] <;> abel

lemma paired_binomial_zero (m : ℕ) (i : Option (Fin m) ⊕ Option (Fin m)) :
    pairedValues (binomialTail m) (0 : G × (Fin m → G) × (Fin m → G)) i = 0 := by
  cases i <;> rename_i i <;> cases i <;>
    simp only [pairedValues,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,binomialTail_zero,sub_self,add_zero]

lemma evenSeed_add (m : ℕ) (p r : G × (Fin m → G) × (Fin m → G)) :
    evenSeed m (p+r) = evenSeed m p+evenSeed m r := by
  funext n
  simp only [evenSeed,Pi.add_apply]
  split_ifs
  · exact paired_binomial_add m p r _
  · exact (zero_add _).symm

lemma evenSeed_zero (m : ℕ) : evenSeed m (0 : G × (Fin m → G) × (Fin m → G)) = 0 := by
  funext n
  simp only [evenSeed,paired_binomial_zero,Pi.zero_apply,dite_eq_ite,ite_self]

lemma evenPolynomial_add (m : ℕ) (p r : G × (Fin m → G) × (Fin m → G)) (n : ℕ) :
    evenPolynomial m (p+r) n = evenPolynomial m p n+evenPolynomial m r n := by
  simp only [evenPolynomial,newtonExtension,evenSeed_add,diffIter,fwdDiff_iter_add,
    Pi.add_apply,smul_add,sum_add_distrib]

lemma evenPolynomial_zero (m n : ℕ) :
    evenPolynomial m (0 : G × (Fin m → G) × (Fin m → G)) n = 0 := by
  simp only [evenPolynomial,newtonExtension,evenSeed_zero,diffIter_zero,Pi.zero_apply,nsmul_zero,sum_const_zero]

noncomputable def evenPolynomialHom (m n : ℕ) : (G × (Fin m → G) × (Fin m → G)) →+ G where
  toFun p := evenPolynomial m p n
  map_zero' := evenPolynomial_zero m n
  map_add' p r := evenPolynomial_add m p r n

def polynomialCoordinates (m : ℕ) (q : ℕ → G) : G × (Fin m → G) × (Fin m → G) :=
  (q 0,fun i ↦ q (i.val+1),fun i ↦ q (2*m-i.val))

lemma polynomialCoordinates_paired (m : ℕ) (q : ℕ → G)
    (hq : diffIter (2*m+1) q 0 = 0) (i : Option (Fin m) ⊕ Option (Fin m)) :
    pairedValues (binomialTail m) (polynomialCoordinates m q) i = q (pairedIndex m i).val := by
  cases i with
  | inl i => cases i <;> rfl
  | inr i =>
    cases i with
    | some i => rfl
    | none =>
      change q 0-binomialTail m (fun i ↦ q (i.val+1))+binomialTail m (fun i ↦ q (2*m-i.val)) = q (2*m+1)
      rw [binomialTail,binomialTail,sub_neg_eq_add]
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ alternatingBinomial (2*m+1) (i+1) • q (i+1)) m,
        Fin.sum_univ_eq_sum_range (fun i ↦ alternatingBinomial (2*m+1) (i+1) • q (2*m-i)) m]
      simpa only [sub_eq_add_neg] using (even_difference_last m q hq).symm

/-- Exact reconstruction requires only the single top-difference equation on
the window. No unproved global extension property is used. -/
theorem evenPolynomial_reconstruct (m : ℕ) (q : ℕ → G)
    (hq : diffIter (2*m+1) q 0 = 0) (j : Fin (2*m+2)) :
    evenPolynomial m (polynomialCoordinates m q) j.val = q j.val := by
  obtain ⟨i,rfl⟩ := (evenIndex m).surjective j
  rw [evenIndex_apply,evenPolynomial_paired,polynomialCoordinates_paired m q hq]

lemma polynomialCoordinates_model (m : ℕ) (p : G × (Fin m → G) × (Fin m → G)) :
    polynomialCoordinates m (evenPolynomial m p) = p := by
  have h0 : evenPolynomial m p 0 = p.1 := evenPolynomial_paired m p (.inl none)
  have hL (i : Fin m) : evenPolynomial m p (i.val+1) = p.2.1 i := evenPolynomial_paired m p (.inl (some i))
  have hR (i : Fin m) : evenPolynomial m p (2*m-i.val) = p.2.2 i := evenPolynomial_paired m p (.inr (some i))
  ext
  · exact h0
  · exact hL _
  · exact hR _

/-- A product-character test on all model values is a single additive
character of the free coordinate group. -/
noncomputable def modelCharacter (m : ℕ) (χ : Fin (2*m+2) → AddChar G ℂ) :
    AddChar (G × (Fin m → G) × (Fin m → G)) ℂ where
  toFun p := ∏ j, χ j (evenPolynomial m p j.val)
  map_zero_eq_one' := by simp only [evenPolynomial_zero,AddChar.map_zero_eq_one,prod_const_one]
  map_add_eq_mul' p r := by
    simp only [evenPolynomial_add,AddChar.map_add_eq_mul,prod_mul_distrib]

lemma modelCharacter_apply (m : ℕ) (χ : Fin (2*m+2) → AddChar G ℂ)
    (p : G × (Fin m → G) × (Fin m → G)) :
    modelCharacter m χ p = ∏ j, χ j (evenPolynomial m p j.val) := rfl

#print axioms evenPolynomialHom
#print axioms evenPolynomial_reconstruct
#print axioms modelCharacter
end Erdos3EvenPolynomialCoordinates
