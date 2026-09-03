import Submission.FiniteFrequencyCoordinates

/-! Rectangular dual sets provide explicit small-boundary spectral cutoffs on
finite tori. All complexity bounds depend on the cutoff K and dimension, not
on the ambient modulus N (provided K+1 <= N). -/
namespace Erdos3RectangularSpectralCutoff
open Finset Erdos3FiniteFrequencyCoordinates Erdos3PositiveSpectralKernel
  Erdos3PositiveSpectralSmoothing Erdos3FiniteSampling
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 6000000

variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]

noncomputable def boxCharacter (K : ℕ) (a : I → Fin (K+1)) : AddChar (I → ZMod N) ℂ :=
  frequencyCharacter (fun i ↦ ((a i).val : ZMod N))

noncomputable def spectralBox (K : ℕ) : Finset (AddChar (I → ZMod N) ℂ) :=
  univ.image (boxCharacter (N := N) K)

lemma boxCharacter_injective {K : ℕ} (hKN : K+1 ≤ N) :
    Function.Injective (boxCharacter (I := I) (N := N) K) := by
  intro a b hab
  have he := frequencyCharacter_injective hab
  funext i
  apply Fin.ext
  have h := congrArg (fun f : I → ZMod N ↦ (f i).val) he
  simpa only [ZMod.val_natCast_of_lt ((a i).isLt.trans_le hKN),
    ZMod.val_natCast_of_lt ((b i).isLt.trans_le hKN)] using h

lemma spectralBox_nonempty (K : ℕ) : (spectralBox (I := I) (N := N) K).Nonempty :=
  ⟨boxCharacter K (fun _ ↦ 0),mem_image_of_mem _ (mem_univ _)⟩

lemma spectralBox_card {K : ℕ} (hKN : K+1 ≤ N) :
    (spectralBox (I := I) (N := N) K).card = (K+1)^(Fintype.card I) := by
  rw [spectralBox,card_image_of_injective _ (boxCharacter_injective hKN)]
  simp only [card_univ,Fintype.card_fun,Fintype.card_fin]

lemma boxCharacter_integer (K : ℕ) (a : I → Fin (K+1)) :
    boxCharacter (N := N) K a = integerCharacter (fun i ↦ ((a i).val : ℤ)) := by
  simp only [boxCharacter,integerCharacter,Int.cast_natCast]

lemma box_ratio_frequency {K : ℕ} {χ : AddChar (I → ZMod N) ℂ}
    (hχ : χ ∈ spectralBox (I := I) (N := N) K/spectralBox K) : HasFrequencyBound K χ := by
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_div.mp hχ
  obtain ⟨u,_,rfl⟩ := mem_image.mp ha
  obtain ⟨v,_,rfl⟩ := mem_image.mp hb
  refine ⟨(fun i ↦ ((u i).val : ℤ))- (fun i ↦ ((v i).val : ℤ)),?_,?_⟩
  · intro i
    have hu := (u i).isLt
    have hv := (v i).isLt
    change |((u i).val : ℤ)-((v i).val : ℤ)| ≤ (K : ℤ)
    exact abs_le.mpr ⟨by omega,by omega⟩
  · rw [boxCharacter_integer,boxCharacter_integer,integerCharacter_sub]

lemma spectralBox_ratio_card {K : ℕ} (hKN : K+1 ≤ N) :
    (spectralBox (I := I) (N := N) K/spectralBox K).card ≤ (K+1)^(2*Fintype.card I) := by
  calc
    _ ≤ (spectralBox (I := I) (N := N) K).card*(spectralBox K).card := card_div_le
    _ = _ := by rw [spectralBox_card hKN,← pow_add]; congr 1; omega

lemma box_shift_inside {K : ℕ} (a : I → Fin (K+1)) (i : I) (hi : a i ≠ Fin.last K) :
    boxCharacter (N := N) K a*coordinateCharacter i ∈ spectralBox K := by
  have hai : (a i).val < K := by
    have hn : (a i).val ≠ K := by intro h; exact hi (Fin.ext h)
    have hlt := (a i).isLt
    omega
  let a' : I → Fin (K+1) := Function.update a i ⟨(a i).val+1,by omega⟩
  have he : (fun j ↦ ((a' j).val : ZMod N)) =
      (fun j ↦ ((a j).val : ZMod N))+(Pi.single i (1 : ZMod N) : I → ZMod N) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [a',Function.update_self,Pi.add_apply,Pi.single_eq_same,Nat.cast_add,Nat.cast_one]
    · simp [a',hj,Pi.add_apply]
  have hchar : boxCharacter (N := N) K a' = boxCharacter K a*coordinateCharacter i := by
    unfold boxCharacter coordinateCharacter
    rw [he,frequencyCharacter_add]
  rw [← hchar]
  exact mem_image_of_mem _ (mem_univ a')

lemma expect_pi_coordinate {A : Type*} [Fintype A] [Nonempty A] (i : I) (f : A → ℝ) :
    (𝔼 a : I → A, f (a i)) = 𝔼 a : A, f a := by
  have h : (𝔼 a : I → A, ∏ j : I, if j = i then f (a j) else 1) =
      ∏ j : I, 𝔼 a : A, if j = i then f a else 1 := by
    simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,Nat.cast_prod,prod_div_distrib]
    congr 1
    exact (Fintype.prod_sum (fun j (a : A) ↦ if j = i then f a else 1)).symm
  have he (j : I) : (𝔼 a : A, if j = i then f a else 1) =
      if j = i then (𝔼 a : A, f a) else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa only [he,prod_ite_eq',mem_univ,if_true] using h

/-- Each coordinate loses at most one face of a rectangular dual set. -/
theorem spectralBox_overlap {K : ℕ} (hKN : K+1 ≤ N) (i : I) :
    1-1/(K+1 : ℝ) ≤
      (((spectralBox (I := I) (N := N) K).filter
        (fun b ↦ b*coordinateCharacter i ∈ spectralBox K)).card : ℝ)/
        ((spectralBox (I := I) (N := N) K).card : ℝ) := by
  let A := I → Fin (K+1)
  let U : Finset A := univ.filter (fun a ↦ a i ≠ Fin.last K)
  have hsub : U.image (boxCharacter (N := N) K) ⊆
      (spectralBox (I := I) (N := N) K).filter (fun b ↦ b*coordinateCharacter i ∈ spectralBox K) := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ a),box_shift_inside a i (mem_filter.mp ha).2⟩
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (boxCharacter_injective hKN)] at hcard
  have he (j : Fin (K+1)) : (if j ≠ Fin.last K then (1 : ℝ) else 0) =
      1-(if j = Fin.last K then 1 else 0) := by
    by_cases hj : j = Fin.last K <;> simp [hj]
  have hm : (𝔼 j : Fin (K+1), if j ≠ Fin.last K then (1 : ℝ) else 0) = 1-1/(K+1 : ℝ) := by
    simp only [he,expect_sub_distrib,Fintype.expect_const]
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hi' := expect_pi_coordinate i (fun j : Fin (K+1) ↦ if j ≠ Fin.last K then (1 : ℝ) else 0)
  rw [hm,Fintype.expect_eq_sum_div_card,sum_boole] at hi'
  have hsize : (spectralBox (I := I) (N := N) K).card = Fintype.card A := by
    rw [spectralBox_card hKN]
    simp only [A,Fintype.card_fun,Fintype.card_fin]
  rw [hsize,← hi']
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

lemma spectralBox_boundary {K : ℕ} (hKN : K+1 ≤ N) (i : I) :
    2*(1-(((spectralBox (I := I) (N := N) K).filter
      (fun b ↦ b*coordinateCharacter i ∈ spectralBox K)).card : ℝ)/
      ((spectralBox (I := I) (N := N) K).card : ℝ)) ≤ 2/(K+1 : ℝ) := by
  have h := spectralBox_overlap hKN i
  rw [show 2/(K+1 : ℝ) = 2*(1/(K+1 : ℝ)) by ring]
  linarith

#print axioms spectralBox_ratio_card
#print axioms spectralBox_boundary
end Erdos3RectangularSpectralCutoff
