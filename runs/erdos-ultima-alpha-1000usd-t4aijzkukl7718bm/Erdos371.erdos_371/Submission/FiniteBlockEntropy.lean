import Submission.FiniteEntropy
import Submission.FiniteProductConcentration

/-! Conditional subadditivity and the finite block entropy decrement inequality.
Stationarity is not assumed implicitly: the blockwise entropy and information
hypotheses are explicit. -/

namespace Erdos371.FiniteInformation
open Finset
attribute [local instance] Classical.propDecidable

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma mean_finset_sum {ι : Type*} (s : Finset ι) (p : Law α) (F : ι → α → ℝ) :
    mean p (fun a => ∑ i ∈ s, F i a) = ∑ i ∈ s, mean p (F i) := by
  simp only [mean, mul_sum]
  exact sum_comm

lemma firstMarginal_map_first_coordinate (P : Law (α × β)) (f : α → γ) :
    firstMarginal (mapLaw P (fun ab => (f ab.1, ab.2))) = mapLaw (firstMarginal P) f := by
  rw [← mapLaw_fst, mapLaw_comp, ← mapLaw_fst, mapLaw_comp]
  rfl

lemma firstMarginal_map_second_equiv (P : Law (α × β)) (e : β ≃ γ) :
    firstMarginal (mapLaw P (fun ab => (ab.1, e ab.2))) = firstMarginal P := by
  rw [← mapLaw_fst, mapLaw_comp]
  exact mapLaw_fst P

lemma secondMarginal_map_second_equiv (P : Law (α × β)) (e : β ≃ γ) :
    secondMarginal (mapLaw P (fun ab => (ab.1, e ab.2))) = mapLaw (secondMarginal P) e := by
  rw [← mapLaw_snd, mapLaw_comp, ← mapLaw_snd, mapLaw_comp]
  rfl

lemma mutualInformation_map_second_equiv (P : Law (α × β)) (e : β ≃ γ) :
    mutualInformation (mapLaw P (fun ab => (ab.1, e ab.2))) = mutualInformation P := by
  rw [mutualInformation_eq_entropy, firstMarginal_map_second_equiv,
    secondMarginal_map_second_equiv, entropy_mapLaw_equiv]
  have he := entropy_mapLaw_equiv P (Equiv.prodCongr (Equiv.refl α) e)
  change entropy (mapLaw P (fun ab => (ab.1, e ab.2))) = entropy P at he
  rw [he, mutualInformation_eq_entropy]

lemma conditionalLaw_apply_of_ne (P : Law (α × β)) (b : β)
    (hb : secondMarginal P b ≠ 0) (a : α) :
    conditionalLaw P b a = P (a,b) / secondMarginal P b := by
  change (if secondMarginal P b = 0 then _ else _) = _
  rw [if_neg hb]

lemma mapLaw_first_coordinate_apply (P : Law (α × β)) (f : α → γ) (c : γ) (b : β) :
    mapLaw P (fun ab => (f ab.1, ab.2)) (c,b) =
      ∑ a, if f a = c then P (a,b) else 0 := by
  classical
  simp only [mapLaw_apply, Fintype.sum_prod_type, Prod.mk.injEq]
  apply sum_congr rfl
  intro a _
  by_cases ha : f a = c <;> simp [ha]

lemma secondMarginal_map_first_coordinate (P : Law (α × β)) (f : α → γ) :
    secondMarginal (mapLaw P (fun ab => (f ab.1, ab.2))) = secondMarginal P := by
  rw [← mapLaw_snd, mapLaw_comp]
  exact mapLaw_snd P

lemma conditionalLaw_map_first_coordinate (P : Law (α × β)) (f : α → γ) (b : β)
    (hb : secondMarginal P b ≠ 0) :
    conditionalLaw (mapLaw P (fun ab => (f ab.1, ab.2))) b =
      mapLaw (conditionalLaw P b) f := by
  ext c
  rw [conditionalLaw_apply_of_ne _ b (by rwa [secondMarginal_map_first_coordinate]),
    secondMarginal_map_first_coordinate, mapLaw_first_coordinate_apply, mapLaw_apply, sum_div]
  apply sum_congr rfl
  intro a _
  rw [conditionalLaw_apply_of_ne P b hb a]
  split_ifs <;> simp

lemma conditionalEntropy_map_first_coordinate (P : Law (α × β)) (f : α → γ) :
    conditionalEntropy (mapLaw P (fun ab => (f ab.1, ab.2))) =
      mean (secondMarginal P) (fun b => entropy (mapLaw (conditionalLaw P b) f)) := by
  unfold conditionalEntropy
  rw [secondMarginal_map_first_coordinate]
  apply sum_congr rfl
  intro b _
  by_cases hb : secondMarginal P b = 0
  · simp [hb]
  · dsimp only
    rw [conditionalLaw_map_first_coordinate P f b hb]

lemma conditionalEntropy_eq_entropy_sub_mutualInformation (P : Law (α × β)) :
    conditionalEntropy P = entropy (firstMarginal P) - mutualInformation P := by
  rw [mutualInformation_eq_entropy, entropy_chain_rule P]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Entropy is subadditive over an arbitrary finite family of coordinates. -/
theorem entropy_le_sum_coordinate_entropies (P : Law (∀ i, κ i)) :
    entropy P ≤ ∑ i, entropy (mapLaw P (fun x => x i)) := by
  let q : ∀ i, Law (κ i) := fun i => mapLaw P (fun x => x i)
  have hs : SupportedBy P (productLaw q) := by
    intro x hx
    rw [productLaw_apply]
    apply prod_ne_zero_iff.mpr
    intro i _
    exact (lt_of_lt_of_le (lt_of_le_of_ne (P.nonneg x) (Ne.symm hx))
      (mass_le_mapLaw P (fun x => x i) x)).ne'
  have he : mean P (fun x => Real.log (productLaw q x)) =
      ∑ i, mean (q i) (fun a => Real.log (q i a)) := by
    calc
      _ = mean P (fun x => ∑ i, Real.log (q i (x i))) := by
        apply sum_congr rfl
        intro x _
        by_cases hx : P x = 0
        · simp [hx]
        · dsimp only
          congr 1
          rw [productLaw_apply]
          apply Real.log_prod
          exact prod_ne_zero_iff.mp (hs x hx)
      _ = ∑ i, mean P (fun x => Real.log (q i (x i))) := mean_finset_sum _ _ _
      _ = _ := by
        apply sum_congr rfl
        intro i _
        exact (mean_mapLaw P (fun x => x i) (fun a => Real.log (q i a))).symm
  have h := entropy_le_crossEntropy P (productLaw q) hs
  rw [he] at h
  simpa only [entropy, sum_neg_distrib] using h

/-- Conditional subadditivity over a finite family of coordinates. -/
theorem conditionalEntropy_le_sum_coordinate (P : Law ((∀ i, κ i) × β)) :
    conditionalEntropy P ≤
      ∑ i, conditionalEntropy (mapLaw P (fun xb => (xb.1 i, xb.2))) := by
  calc
    _ ≤ mean (secondMarginal P) (fun b =>
        ∑ i, entropy (mapLaw (conditionalLaw P b) (fun x => x i))) := by
      apply sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        (entropy_le_sum_coordinate_entropies (conditionalLaw P b)) ((secondMarginal P).nonneg b)
    _ = ∑ i, mean (secondMarginal P) (fun b =>
        entropy (mapLaw (conditionalLaw P b) (fun x => x i))) := mean_finset_sum _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro i _
      exact (conditionalEntropy_map_first_coordinate P (fun x => x i)).symm

/-- The finite inequality behind entropy decrement. If each block has entropy
`E` and at least `I` information about a shared auxiliary variable, then the
entropy of all blocks is at most `H(aux) + m*(E-I)`. -/
theorem block_entropy_decrement (P : Law ((∀ i, κ i) × β)) (E I : ℝ)
    (hE : ∀ i, entropy (firstMarginal (mapLaw P (fun xb => (xb.1 i, xb.2)))) ≤ E)
    (hI : ∀ i, I ≤ mutualInformation (mapLaw P (fun xb => (xb.1 i, xb.2)))) :
    entropy (firstMarginal P) ≤ entropy (secondMarginal P) + Fintype.card ι * (E-I) := by
  calc
    _ ≤ entropy P := by simpa only [mapLaw_fst] using entropy_mapLaw_le P Prod.fst
    _ = entropy (secondMarginal P) + conditionalEntropy P := entropy_chain_rule P
    _ ≤ entropy (secondMarginal P) +
        ∑ i, conditionalEntropy (mapLaw P (fun xb => (xb.1 i, xb.2))) :=
      add_le_add le_rfl (conditionalEntropy_le_sum_coordinate P)
    _ ≤ entropy (secondMarginal P) + ∑ _ : ι, (E-I) := by
      gcongr with i
      rw [conditionalEntropy_eq_entropy_sub_mutualInformation]
      linarith [hE i, hI i]
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

#print axioms entropy_le_sum_coordinate_entropies
#print axioms conditionalEntropy_le_sum_coordinate
#print axioms block_entropy_decrement

end Erdos371.FiniteInformation
