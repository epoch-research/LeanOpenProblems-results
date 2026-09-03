import Submission.PrimePatternInclusion

/-! Reflection of selected prime colours cancels the model term, including
at every finite truncation degree. -/
namespace Erdos371.FiniteSieve
open Finset

lemma powerset_equiv_map {ι κ : Type*} (e : ι ≃ κ) (S : Finset ι) :
    (S.map e.toEmbedding).powerset = S.powerset.map e.finsetCongr.toEmbedding := by
  classical
  simp only [map_eq_image,powerset_image,Equiv.coe_toEmbedding]
  apply image_congr
  intro T _
  simp only [Equiv.finsetCongr_apply,map_eq_image,Equiv.coe_toEmbedding]

lemma patternDifference_equiv_map {ι κ : Type*} (e : ι ≃ κ)
    (F : Finset κ → ℝ) (S : Finset ι) :
    patternDifference F (S.map e.toEmbedding) =
      patternDifference (fun T => F (T.map e.toEmbedding)) S := by
  unfold patternDifference
  rw [powerset_equiv_map,sum_map]
  simp only [Equiv.coe_toEmbedding,Equiv.finsetCongr_apply,card_map]

lemma patternDifference_neg {ι : Type*} (F : Finset ι → ℝ) (S : Finset ι) :
    patternDifference (fun T => -F T) S = -patternDifference F S := by
  simp only [patternDifference,mul_neg,sum_neg_distrib]

lemma primeAtomModel_equiv_map (e : PrimeAtom ≃ PrimeAtom)
    (he : ∀ a, (e a).1=a.1) (T : Finset PrimeAtom) :
    primeAtomModel (T.map e.toEmbedding) = primeAtomModel T := by
  classical
  have hi : Set.InjOn Prod.fst (T.map e.toEmbedding : Set PrimeAtom) ↔
      Set.InjOn Prod.fst (T : Set PrimeAtom) := by
    constructor
    · intro h a ha b hb hab
      apply e.injective
      apply h (mem_map.mpr ⟨a,ha,rfl⟩) (mem_map.mpr ⟨b,hb,rfl⟩)
      simpa only [Equiv.coe_toEmbedding,he] using hab
    · intro h a ha b hb hab
      obtain ⟨a',ha',rfl⟩ := mem_map.mp ha
      obtain ⟨b',hb',rfl⟩ := mem_map.mp hb
      apply congrArg e
      apply h ha' hb'
      simpa only [Equiv.coe_toEmbedding,he] using hab
  simp only [primeAtomModel,hi,prod_map,Equiv.coe_toEmbedding,he]

/-- An odd model observable has zero truncated model mean, not just zero
mean over a complete CRT period. -/
theorem prime_pattern_model_odd_zero (P : Finset ℕ) (L : ℕ)
    (e : PrimeAtom ≃ PrimeAtom) (he : ∀ a, (e a).1=a.1)
    (hP : (primeAtoms P).map e.toEmbedding = primeAtoms P)
    (F : Finset PrimeAtom → ℝ) (hF : ∀ T, F (T.map e.toEmbedding) = -F T) :
    (∑ T ∈ (primeAtoms P).powerset,
      if T.card < L then patternDifference F T*primeAtomModel T else 0) = 0 := by
  let z : ℝ := ∑ T ∈ (primeAtoms P).powerset,
    if T.card < L then patternDifference F T*primeAtomModel T else 0
  have hdiff (T : Finset PrimeAtom) : patternDifference F (T.map e.toEmbedding) = -patternDifference F T := by
    rw [patternDifference_equiv_map]
    simp_rw [hF]
    exact patternDifference_neg F T
  have hz : z = -z := by
    dsimp only [z]
    conv_lhs => rw [← hP,powerset_equiv_map,sum_map]
    simp only [Equiv.coe_toEmbedding,Equiv.finsetCongr_apply,card_map,hdiff,
      primeAtomModel_equiv_map e he,neg_mul,← sum_neg_distrib]
    apply sum_congr rfl
    intro T _
    split_ifs <;> simp
  change z=0
  linarith

/-- A colour flip preserves the prime label and is an involution. -/
def primeColourFlip (B : Finset ℕ) : PrimeAtom ≃ PrimeAtom where
  toFun a := (a.1, if a.1 ∈ B then !a.2 else a.2)
  invFun a := (a.1, if a.1 ∈ B then !a.2 else a.2)
  left_inv a := by rcases a with ⟨p,c⟩; simp only; split_ifs <;> simp
  right_inv a := by rcases a with ⟨p,c⟩; simp only; split_ifs <;> simp

@[simp] lemma primeColourFlip_fst (B : Finset ℕ) (a : PrimeAtom) : (primeColourFlip B a).1=a.1 := rfl

lemma primeColourFlip_atoms (B P : Finset ℕ) :
    (primeAtoms P).map (primeColourFlip B).toEmbedding = primeAtoms P := by
  ext a
  constructor
  · intro ha
    obtain ⟨b,hb,rfl⟩ := mem_map.mp ha
    simp only [primeAtoms,mem_product,mem_univ,and_true] at hb ⊢
    exact hb
  · intro ha
    refine mem_map.mpr ⟨(primeColourFlip B).symm a,?_,(primeColourFlip B).apply_symm_apply a⟩
    simp only [primeAtoms,mem_product,mem_univ,and_true] at ha ⊢
    exact ha

#print axioms prime_pattern_model_odd_zero
end Erdos371.FiniteSieve
