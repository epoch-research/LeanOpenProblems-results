import Submission.FiniteBlockEntropy

/-! The block entropy recurrence for finite stationary systems. The auxiliary
variable transforms by a permutation; it need not be independent of labels. -/

namespace Erdos371.FiniteInformation
open Finset

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

lemma mapLaw_iterate_eq (p : Law Ω) (S : Ω → Ω) (hS : mapLaw p S = p) (n : ℕ) :
    mapLaw p (S^[n]) = p := by
  induction n with
  | zero => simpa only [Function.iterate_zero] using mapLaw_id p
  | succ n ih => rw [Function.iterate_succ', ← mapLaw_comp, ih, hS]

lemma mapLaw_comp_iterate_eq (p : Law Ω) (S : Ω → Ω) (hS : mapLaw p S = p)
    {C : Type*} [Fintype C] (F : Ω → C) (n : ℕ) : mapLaw p (F ∘ S^[n]) = mapLaw p F := by
  rw [← mapLaw_comp, mapLaw_iterate_eq p S hS n]

def labelBlock (S : Ω → Ω) (L : Ω → A) (H : ℕ) (ω : Ω) : Fin H → A :=
  fun j => L (S^[j.val] ω)

def chunkEquiv (A : Type*) (k H : ℕ) :
    (Fin (k*H) → A) ≃ (Fin k → Fin H → A) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl A)).trans (Equiv.curry _ _ _)

omit [Fintype Ω] [Fintype A] in
lemma chunk_labelBlock (S : Ω → Ω) (L : Ω → A) (k H : ℕ) (ω : Ω) (i : Fin k) :
    chunkEquiv A k H (labelBlock S L (k*H) ω) i = labelBlock S L H (S^[H*i.val] ω) := by
  funext j
  change L (S^[j.val+H*i.val] ω) = L (S^[j.val] (S^[H*i.val] ω))
  rw [Function.iterate_add_apply]

noncomputable def blockLaw (p : Law Ω) (S : Ω → Ω) (L : Ω → A) (H : ℕ) : Law (Fin H → A) :=
  mapLaw p (labelBlock S L H)

noncomputable def blockJointLaw (p : Law Ω) (S : Ω → Ω) (L : Ω → A)
    (Y : Ω → B) (H : ℕ) : Law ((Fin H → A) × B) :=
  mapLaw p (fun ω => (labelBlock S L H ω, Y ω))

lemma firstMarginal_blockJointLaw (p : Law Ω) (S : Ω → Ω) (L : Ω → A) (Y : Ω → B) (H : ℕ) :
    firstMarginal (blockJointLaw p S L Y H) = blockLaw p S L H := by
  rw [← mapLaw_fst]
  unfold blockJointLaw blockLaw
  rw [mapLaw_comp]
  rfl

lemma secondMarginal_blockJointLaw (p : Law Ω) (S : Ω → Ω) (L : Ω → A) (Y : Ω → B) (H : ℕ) :
    secondMarginal (blockJointLaw p S L Y H) = mapLaw p Y := by
  rw [← mapLaw_snd]
  unfold blockJointLaw
  rw [mapLaw_comp]
  rfl

lemma entropy_blockLaw_le (p : Law Ω) (S : Ω → Ω) (L : Ω → A) (H : ℕ) :
    entropy (blockLaw p S L H) ≤ H * Real.log (Fintype.card A) := by
  have h := entropy_le_log_card (blockLaw p S L H)
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

/-- Stationarity supplies every block entropy and mutual-information hypothesis
in the finite block decrement. The auxiliary variable is shifted by `R` when
the system is shifted by `S`. -/
theorem stationary_block_entropy_recurrence
    (p : Law Ω) (S : Ω → Ω) (hS : mapLaw p S = p) (L : Ω → A)
    (Y : Ω → B) (R : Equiv.Perm B) (hY : Function.Semiconj Y S R) (H k : ℕ) :
    entropy (blockLaw p S L (k*H)) ≤ entropy (mapLaw p Y) +
      k * (entropy (blockLaw p S L H) - mutualInformation (blockJointLaw p S L Y H)) := by
  let J := blockJointLaw p S L Y (k*H)
  let P : Law ((Fin k → Fin H → A) × B) :=
    mapLaw J (fun xb => (chunkEquiv A k H xb.1, xb.2))
  let Pᵢ (i : Fin k) : Law ((Fin H → A) × B) := mapLaw P (fun xb => (xb.1 i, xb.2))
  have hcorrect (i : Fin k) :
      mapLaw (Pᵢ i) (fun xb => (xb.1, (R^(H*i.val)) xb.2)) = blockJointLaw p S L Y H := by
    dsimp [Pᵢ, P, J, blockJointLaw]
    rw [mapLaw_comp, mapLaw_comp, mapLaw_comp]
    have he : ((fun xb : (Fin H → A) × B => (xb.1, (R^(H*i.val)) xb.2)) ∘
        (fun xb : (Fin k → Fin H → A) × B => (xb.1 i, xb.2)) ∘
        (fun xb : (Fin (k*H) → A) × B => (chunkEquiv A k H xb.1, xb.2)) ∘
        (fun ω => (labelBlock S L (k*H) ω, Y ω))) =
          (fun ω => (labelBlock S L H ω, Y ω)) ∘ S^[H*i.val] := by
      funext ω
      simp only [Function.comp_apply, chunk_labelBlock, Equiv.Perm.coe_pow]
      rw [(hY.iterate_right (H*i.val)) ω]
    simp only [Function.comp_assoc]
    rw [he, mapLaw_comp_iterate_eq p S hS]
  have hfirst (i : Fin k) : firstMarginal (Pᵢ i) = blockLaw p S L H := by
    rw [← firstMarginal_map_second_equiv (Pᵢ i) (R^(H*i.val)), hcorrect,
      firstMarginal_blockJointLaw]
  have hinfo (i : Fin k) : mutualInformation (Pᵢ i) = mutualInformation (blockJointLaw p S L Y H) := by
    rw [← mutualInformation_map_second_equiv (Pᵢ i) (R^(H*i.val)), hcorrect]
  have hb := block_entropy_decrement P (entropy (blockLaw p S L H))
    (mutualInformation (blockJointLaw p S L Y H))
    (fun i => by change entropy (firstMarginal (Pᵢ i)) ≤ _; rw [hfirst])
    (fun i => by change _ ≤ mutualInformation (Pᵢ i); rw [hinfo])
  have hPfirst : entropy (firstMarginal P) = entropy (blockLaw p S L (k*H)) := by
    dsimp [P]
    rw [firstMarginal_map_first_coordinate, entropy_mapLaw_equiv]
    exact congrArg entropy (firstMarginal_blockJointLaw p S L Y (k*H))
  have hPsecond : secondMarginal P = mapLaw p Y := by
    dsimp [P]
    rw [secondMarginal_map_first_coordinate]
    exact secondMarginal_blockJointLaw p S L Y (k*H)
  simpa only [hPfirst, hPsecond, Fintype.card_fin] using hb

#print axioms stationary_block_entropy_recurrence
end Erdos371.FiniteInformation
