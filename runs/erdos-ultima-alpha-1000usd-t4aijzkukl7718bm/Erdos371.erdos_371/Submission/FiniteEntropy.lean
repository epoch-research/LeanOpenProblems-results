import Submission.FiniteInformation

/-! Finite Shannon entropy, maps, chain rule, and conditional laws. All sums
are finite; zero-mass atoms are handled explicitly. -/

namespace Erdos371.FiniteInformation
open Finset
attribute [local instance] Classical.propDecidable

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] lemma Law.ext {p q : Law α} (h : ∀ a, p a = q a) : p = q := by
  cases p with
  | mk p hp ht =>
    cases q with
    | mk q hq hs =>
      have he : p = q := funext h
      cases he
      rfl

lemma mass_le_one (p : Law α) (a : α) : p a ≤ 1 := by
  rw [← p.total]
  exact single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

noncomputable def entropy (p : Law α) : ℝ := -mean p (fun a => Real.log (p a))

lemma entropy_nonneg (p : Law α) : 0 ≤ entropy p := by
  apply neg_nonneg.mpr
  apply sum_nonpos
  intro a _
  exact mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
    (Real.log_nonpos (p.nonneg a) (mass_le_one p a))

/-- Pushforward of a finite law. -/
noncomputable def mapLaw (p : Law α) (f : α → β) : Law β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then p a else 0
    nonneg := fun b => sum_nonneg fun a _ => by split_ifs <;> simp_all [p.nonneg]
    total := by rw [sum_comm]; simpa using p.total }

lemma mapLaw_apply (p : Law α) (f : α → β) (b : β) :
    mapLaw p f b = ∑ a, if f a = b then p a else 0 := by
  classical
  rfl

lemma mean_mapLaw (p : Law α) (f : α → β) (G : β → ℝ) :
    mean (mapLaw p f) G = mean p (fun a => G (f a)) := by
  classical
  simp only [mean, mapLaw_apply, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

lemma mapLaw_id (p : Law α) : mapLaw p id = p := by
  classical
  ext a
  simp [mapLaw_apply]

lemma mapLaw_comp (p : Law α) (f : α → β) (g : β → γ) :
    mapLaw (mapLaw p f) g = mapLaw p (g ∘ f) := by
  classical
  ext c
  have h := mean_mapLaw p f (fun b => if g b = c then 1 else 0)
  simpa only [mean, mapLaw_apply, mul_ite, mul_one, mul_zero, Function.comp_apply] using h

lemma mass_le_mapLaw (p : Law α) (f : α → β) (a : α) : p a ≤ mapLaw p f (f a) := by
  classical
  rw [mapLaw_apply]
  have h := single_le_sum (s := (univ : Finset α))
    (f := fun b => if f b = f a then p b else 0)
    (fun b _ => by dsimp only; split_ifs <;> simp_all [p.nonneg]) (mem_univ a)
  simpa using h

lemma entropy_mapLaw_le (p : Law α) (f : α → β) : entropy (mapLaw p f) ≤ entropy p := by
  unfold entropy
  rw [mean_mapLaw]
  apply neg_le_neg
  apply sum_le_sum
  intro a _
  by_cases ha : p a = 0
  · simp [ha]
  · apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
    exact Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm ha))
      (mass_le_mapLaw p f a)

lemma entropy_mapLaw_equiv (p : Law α) (e : α ≃ β) : entropy (mapLaw p e) = entropy p := by
  apply le_antisymm (entropy_mapLaw_le p e)
  have h := entropy_mapLaw_le (mapLaw p e) e.symm
  rw [mapLaw_comp] at h
  have he : (e.symm ∘ e : α → α) = id := by funext a; simp
  simpa only [he, mapLaw_id] using h

lemma mapLaw_fst (P : Law (α × β)) : mapLaw P Prod.fst = firstMarginal P := by
  classical
  ext a
  simp only [mapLaw_apply, Fintype.sum_prod_type, firstMarginal]
  rw [sum_comm]
  simp

lemma mapLaw_snd (P : Law (α × β)) : mapLaw P Prod.snd = secondMarginal P := by
  classical
  ext b
  simp only [mapLaw_apply, Fintype.sum_prod_type, secondMarginal]
  simp

lemma mean_firstMarginal (P : Law (α × β)) (F : α → ℝ) :
    mean (firstMarginal P) F = mean P (fun ab => F ab.1) := by
  rw [← mapLaw_fst, mean_mapLaw]

lemma mean_secondMarginal (P : Law (α × β)) (F : β → ℝ) :
    mean (secondMarginal P) F = mean P (fun ab => F ab.2) := by
  rw [← mapLaw_snd, mean_mapLaw]

lemma mutualInformation_eq_entropy (P : Law (α × β)) :
    mutualInformation P = entropy (firstMarginal P) + entropy (secondMarginal P) -
      entropy P := by
  have he (ab : α × β) :
      P ab * Real.log (P ab / independent (firstMarginal P) (secondMarginal P) ab) =
        P ab * Real.log (P ab) - P ab * Real.log (firstMarginal P ab.1) -
          P ab * Real.log (secondMarginal P ab.2) := by
    by_cases hp : P ab = 0
    · simp [hp]
    · have hs := supportedBy_independent_marginals P ab hp
      change firstMarginal P ab.1 * secondMarginal P ab.2 ≠ 0 at hs
      change P ab * Real.log (P ab /
        (firstMarginal P ab.1 * secondMarginal P ab.2)) = _
      rw [Real.log_div hp hs, Real.log_mul (mul_ne_zero_iff.mp hs).1
        (mul_ne_zero_iff.mp hs).2]
      ring
  unfold mutualInformation divergence
  simp only [he, sum_sub_distrib]
  change mean P (fun ab => Real.log (P ab)) -
    mean P (fun ab => Real.log (firstMarginal P ab.1)) -
    mean P (fun ab => Real.log (secondMarginal P ab.2)) = _
  rw [← mean_firstMarginal P (fun a => Real.log (firstMarginal P a)),
    ← mean_secondMarginal P (fun b => Real.log (secondMarginal P b))]
  unfold entropy
  ring

lemma entropy_subadditive (P : Law (α × β)) :
    entropy P ≤ entropy (firstMarginal P) + entropy (secondMarginal P) := by
  have h := mutualInformation_nonneg P
  rw [mutualInformation_eq_entropy] at h
  linarith

lemma mutualInformation_le_entropy_first (P : Law (α × β)) :
    mutualInformation P ≤ entropy (firstMarginal P) := by
  have h := entropy_mapLaw_le P Prod.snd
  rw [mapLaw_snd] at h
  rw [mutualInformation_eq_entropy]
  linarith

lemma mutualInformation_le_entropy_second (P : Law (α × β)) :
    mutualInformation P ≤ entropy (secondMarginal P) := by
  have h := entropy_mapLaw_le P Prod.fst
  rw [mapLaw_fst] at h
  rw [mutualInformation_eq_entropy]
  linarith

lemma divergence_eq_entropy (p q : Law α) (hs : SupportedBy p q) :
    divergence p q = -entropy p - mean p (fun a => Real.log (q a)) := by
  have he (a : α) : p a * Real.log (p a / q a) =
      p a * Real.log (p a) - p a * Real.log (q a) := by
    by_cases hp : p a = 0
    · simp [hp]
    · rw [Real.log_div hp (hs a hp)]
      ring
  simp only [divergence, he, sum_sub_distrib, entropy, mean, neg_neg]

lemma entropy_le_crossEntropy (p q : Law α) (hs : SupportedBy p q) :
    entropy p ≤ -mean p (fun a => Real.log (q a)) := by
  have h := divergence_nonneg p q hs
  rw [divergence_eq_entropy p q hs] at h
  linarith

noncomputable def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : Law α where
  mass _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

lemma entropy_le_log_card (p : Law α) : entropy p ≤ Real.log (Fintype.card α) := by
  obtain ⟨a, ha⟩ := exists_mass_pos p
  letI : Nonempty α := ⟨a⟩
  have hs : SupportedBy p (uniformLaw α) := fun _ _ =>
    inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have h := entropy_le_crossEntropy p (uniformLaw α) hs
  change entropy p ≤ -mean p (fun _ => Real.log (Fintype.card α : ℝ)⁻¹) at h
  simpa only [Real.log_inv, mean_const, neg_neg] using h

/-- Conditional law of the first coordinate given the second. At a null atom,
use the first marginal as a harmless normalized default. -/
noncomputable def conditionalLaw (P : Law (α × β)) (b : β) : Law α := by
  classical
  exact {
    mass := fun a => if secondMarginal P b = 0 then firstMarginal P a
      else P (a,b) / secondMarginal P b
    nonneg := fun a => by
      split_ifs
      · exact (firstMarginal P).nonneg a
      · exact div_nonneg (P.nonneg (a,b)) ((secondMarginal P).nonneg b)
    total := by
      split_ifs with hb
      · exact (firstMarginal P).total
      · rw [← sum_div]
        exact div_self hb }

lemma disintegrate_mass (P : Law (α × β)) (a : α) (b : β) :
    P (a,b) = secondMarginal P b * conditionalLaw P b a := by
  classical
  change P (a,b) = secondMarginal P b *
    (if secondMarginal P b = 0 then firstMarginal P a else P (a,b) / secondMarginal P b)
  split_ifs with hb
  · have hp := mass_le_secondMarginal P a b
    rw [hb, zero_mul] at *
    exact le_antisymm hp (P.nonneg (a,b))
  · field_simp

lemma mean_disintegrate (P : Law (α × β)) (F : α × β → ℝ) :
    mean P F = mean (secondMarginal P) (fun b => mean (conditionalLaw P b) (fun a => F (a,b))) := by
  unfold mean
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  rw [disintegrate_mass P a b]
  ring

noncomputable def conditionalEntropy (P : Law (α × β)) : ℝ :=
  mean (secondMarginal P) (fun b => entropy (conditionalLaw P b))

lemma conditionalEntropy_nonneg (P : Law (α × β)) : 0 ≤ conditionalEntropy P :=
  sum_nonneg fun b _ => mul_nonneg ((secondMarginal P).nonneg b)
    (entropy_nonneg (conditionalLaw P b))

/-- Finite Shannon chain rule. -/
theorem entropy_chain_rule (P : Law (α × β)) :
    entropy P = entropy (secondMarginal P) + conditionalEntropy P := by
  have he (a : α) (b : β) :
      P (a,b) * Real.log (P (a,b)) =
        P (a,b) * Real.log (secondMarginal P b) +
        secondMarginal P b * (conditionalLaw P b a * Real.log (conditionalLaw P b a)) := by
    by_cases hp : P (a,b) = 0
    · rw [hp, zero_mul, zero_mul, zero_add]
      rw [← mul_assoc, ← disintegrate_mass, hp, zero_mul]
    · have hs : secondMarginal P b * conditionalLaw P b a ≠ 0 := by
        rwa [← disintegrate_mass]
      rw [disintegrate_mass P a b, Real.log_mul (mul_ne_zero_iff.mp hs).1
        (mul_ne_zero_iff.mp hs).2]
      ring
  unfold entropy conditionalEntropy mean
  rw [Fintype.sum_prod_type]
  simp only [he, sum_add_distrib]
  rw [sum_comm (f := fun a b => P (a,b) * Real.log (secondMarginal P b))]
  simp only [← sum_mul]
  change -( (∑ b, secondMarginal P b * Real.log (secondMarginal P b)) +
    (∑ a, ∑ b, secondMarginal P b * (conditionalLaw P b a * Real.log (conditionalLaw P b a)))) = _
  rw [sum_comm (f := fun a b => secondMarginal P b *
    (conditionalLaw P b a * Real.log (conditionalLaw P b a)))]
  simp only [entropy, mean, ← mul_sum, mul_neg, sum_neg_distrib]
  ring

#print axioms entropy_mapLaw_le
#print axioms mutualInformation_eq_entropy
#print axioms entropy_chain_rule

end Erdos371.FiniteInformation
