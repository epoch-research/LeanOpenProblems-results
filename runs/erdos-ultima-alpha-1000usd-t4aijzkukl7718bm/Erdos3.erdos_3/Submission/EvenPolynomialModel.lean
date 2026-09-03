import Submission.PairedEvenModelCounting
import Submission.EvenDifferencePairing
import Submission.LocalPolynomialPhaseExtension

/-! Every even-length paired binomial model has an exact polynomial
realization, with vanishing next finite difference, and its count is at least
the corresponding power of the mean. This is a pure model, not a general
higher-order structural theorem. -/
namespace Erdos3EvenPolynomialModel
open Finset Erdos3PairedEvenModelCounting Erdos3EvenDifferencePairing
  Erdos3HigherPhaseDifferences Erdos3LocalPolynomialPhaseExtension
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G]

def pairedIndex (m : ℕ) : Option (Fin m) ⊕ Option (Fin m) → Fin (2*m+2)
  | .inl none => ⟨0,by omega⟩
  | .inl (some i) => ⟨i.val+1,by omega⟩
  | .inr none => ⟨2*m+1,by omega⟩
  | .inr (some i) => ⟨2*m-i.val,by omega⟩

lemma pairedIndex_injective (m : ℕ) : Function.Injective (pairedIndex m) := by
  intro i j hij
  cases i <;> cases j <;> rename_i i j <;> cases i <;> cases j
  all_goals simp only [pairedIndex,Fin.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,Option.some.injEq] at hij ⊢
  all_goals first | rfl | omega | (apply Fin.ext; omega)

noncomputable def evenIndex (m : ℕ) : Option (Fin m) ⊕ Option (Fin m) ≃ Fin (2*m+2) :=
  Equiv.ofBijective (pairedIndex m) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨pairedIndex_injective m,by simp; omega⟩)

lemma evenIndex_apply (m : ℕ) (i : Option (Fin m) ⊕ Option (Fin m)) :
    evenIndex m i = pairedIndex m i := rfl

noncomputable def binomialTail (m : ℕ) (u : Fin m → G) : G :=
  -(∑ i, alternatingBinomial (2*m+1) (i.val+1) • u i)

noncomputable def evenSeed (m : ℕ) (p : G × (Fin m → G) × (Fin m → G)) (n : ℕ) : G :=
  if h : n < 2*m+2 then pairedValues (binomialTail m) p ((evenIndex m).symm ⟨n,h⟩) else 0

lemma evenSeed_paired (m : ℕ) (p : G × (Fin m → G) × (Fin m → G))
    (i : Option (Fin m) ⊕ Option (Fin m)) :
    evenSeed m p (pairedIndex m i).val = pairedValues (binomialTail m) p i := by
  rw [evenSeed,dif_pos (pairedIndex m i).isLt]
  change pairedValues (binomialTail m) p ((evenIndex m).symm (evenIndex m i)) = _
  rw [Equiv.symm_apply_apply]

lemma evenSeed_difference_zero (m : ℕ) (p : G × (Fin m → G) × (Fin m → G)) :
    diffIter (2*m+1) (evenSeed m p) 0 = 0 := by
  rw [even_difference_zero_iff_last]
  have h0 : evenSeed m p 0 = p.1 := evenSeed_paired m p (.inl none)
  have hN : evenSeed m p (2*m+1) = p.1-binomialTail m p.2.1+binomialTail m p.2.2 :=
    evenSeed_paired m p (.inr none)
  have hL (i : Fin m) : evenSeed m p (i.val+1) = p.2.1 i := evenSeed_paired m p (.inl (some i))
  have hR (i : Fin m) : evenSeed m p (2*m-i.val) = p.2.2 i := evenSeed_paired m p (.inr (some i))
  rw [h0,hN,← Fin.sum_univ_eq_sum_range (fun i ↦ alternatingBinomial (2*m+1) (i+1) • evenSeed m p (i+1)) m,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ alternatingBinomial (2*m+1) (i+1) • evenSeed m p (2*m-i)) m]
  simp only [hL,hR,binomialTail,sub_eq_add_neg,neg_neg]

noncomputable def evenPolynomial (m : ℕ) (p : G × (Fin m → G) × (Fin m → G)) : ℕ → G :=
  newtonExtension (2*m) (evenSeed m p)

lemma evenPolynomial_difference_zero (m : ℕ) (p : G × (Fin m → G) × (Fin m → G)) :
    diffIter (2*m+1) (evenPolynomial m p) = 0 := newtonExtension_difference_zero (2*m) (evenSeed m p)

lemma evenPolynomial_eq_seed (m : ℕ) (p : G × (Fin m → G) × (Fin m → G))
    (n : ℕ) (hn : n ≤ 2*m+1) : evenPolynomial m p n = evenSeed m p n := by
  apply newtonExtension_eq (N := 2*m+1) _ _ n hn
  intro a ha
  have ha0 : a = 0 := by omega
  subst a
  exact evenSeed_difference_zero m p

lemma evenPolynomial_paired (m : ℕ) (p : G × (Fin m → G) × (Fin m → G))
    (i : Option (Fin m) ⊕ Option (Fin m)) :
    evenPolynomial m p (pairedIndex m i).val = pairedValues (binomialTail m) p i := by
  rw [evenPolynomial_eq_seed m p _ (by have := (pairedIndex m i).isLt; omega),evenSeed_paired]

variable [Fintype G]

theorem even_polynomial_model_lower (m : ℕ) (f : G → ℝ) :
    (𝔼 x : G, f x)^(2*m+2) ≤
      𝔼 p : G × (Fin m → G) × (Fin m → G), ∏ j : Fin (2*m+2), f (evenPolynomial m p j.val) := by
  have hprod (p : G × (Fin m → G) × (Fin m → G)) :
      (∏ j : Fin (2*m+2), f (evenPolynomial m p j.val)) =
      ∏ i : Option (Fin m) ⊕ Option (Fin m), f (pairedValues (binomialTail m) p i) := by
    rw [← Equiv.prod_comp (evenIndex m)]
    apply prod_congr rfl
    intro i _
    rw [evenIndex_apply,evenPolynomial_paired]
  simp only [hprod,← pairedModelCount_eq]
  simpa only [Fintype.card_fin,show 2*(m+1) = 2*m+2 by omega] using
    pairedModelCount_lower f (binomialTail m)

#print axioms evenPolynomial_difference_zero
#print axioms even_polynomial_model_lower
end Erdos3EvenPolynomialModel
