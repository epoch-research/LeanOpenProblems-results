import Submission.TaperedFaithfulLiftExplore

/-! Exact translation-average row cardinalities for the safe tapered lift.
These first-moment identities do not assert representation estimates. -/
namespace Erdos66TaperedRowAverage
open Erdos66TaperedFaithfulLift
open scoped Classical
set_option maxHeartbeats 1400000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def safeRow (U : Finset F) (a y : F) : Finset F :=
  Finset.univ.filter (fun x ↦ x+a ≠ 0 ∧ y+x+a ≠ 0 ∧ label a x y∈U)

lemma row_eq_safeRow (U : Finset F) (a y : F)
    (hU : ∀ u∈U, a+u ≠ 0) : row U a y=safeRow U a y := by
  ext x
  rw [mem_row_label U a x y hU]
  simp only [safeRow,Finset.mem_filter,Finset.mem_univ,true_and]

/-- This is a permutation of the entire coordinate plane; the two excluded
values of the second coordinate are imposed separately. -/
noncomputable def parameterEquiv (y : F) : (F × F) ≃ (F × F) where
  toFun uz := (uz.2^2/(y+uz.2)-uz.1,uz.2-(uz.2^2/(y+uz.2)-uz.1))
  invFun ax := (label ax.1 ax.2 y,ax.2+ax.1)
  left_inv uz := by
    ext <;> dsimp [label]
    · rw [sub_add_cancel,show y+(uz.2-(uz.2^2/(y+uz.2)-uz.1))+
          (uz.2^2/(y+uz.2)-uz.1)=y+uz.2 by ring]
      ring
    · ring
  right_inv ax := by
    ext <;> dsimp [label]
    · rw [show y+ax.2+ax.1=y+(ax.2+ax.1) by ring]
      ring
    · rw [show y+ax.2+ax.1=y+(ax.2+ax.1) by ring]
      ring

lemma sum_card_safeRow (U : Finset F) (y : F) :
    (∑ a : F, (safeRow U a y).card)=
      U.card*(Finset.univ.filter (fun z : F ↦ z≠0 ∧ y+z≠0)).card := by
  simp only [safeRow,Finset.card_filter]
  rw [←Fintype.sum_prod_type (fun ax : F × F ↦
    if ax.2+ax.1≠0 ∧ y+ax.2+ax.1≠0 ∧ label ax.1 ax.2 y∈U then (1:ℕ) else 0),
    ←(parameterEquiv y).sum_comp]
  have he (uz : F × F) :
      let ax := parameterEquiv y uz
      (ax.2+ax.1≠0 ∧ y+ax.2+ax.1≠0 ∧ label ax.1 ax.2 y∈U) ↔
        (uz.2≠0 ∧ y+uz.2≠0 ∧ uz.1∈U) := by
    have hi := (parameterEquiv y).left_inv uz
    have hi₁ := congrArg Prod.fst hi
    have hi₂ := congrArg Prod.snd hi
    change label ((parameterEquiv y uz).1) ((parameterEquiv y uz).2) y=uz.1 at hi₁
    change (parameterEquiv y uz).2+(parameterEquiv y uz).1=uz.2 at hi₂
    dsimp only
    rw [hi₁,show y+(parameterEquiv y uz).2+(parameterEquiv y uz).1=
      y+((parameterEquiv y uz).2+(parameterEquiv y uz).1) by ring,hi₂]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  calc
    (∑ u : F, ∑ z : F, if z≠0 ∧ y+z≠0 ∧ u∈U then (1 : ℕ) else 0) =
        ∑ u : F, if u∈U then
          ∑ z : F, if z≠0 ∧ y+z≠0 then (1 : ℕ) else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hm : u∈U <;> simp only [hm,and_true,and_false,if_true,if_false,Finset.sum_const_zero]
    _ = _ := by simp

lemma allowed_card_zero :
    (Finset.univ.filter (fun z : F ↦ z≠0 ∧ (0:F)+z≠0)).card=Fintype.card F-1 := by
  have he : Finset.univ.filter (fun z : F ↦ z≠0 ∧ (0:F)+z≠0)=
      Finset.univ.erase (0:F) := by ext z; simp
  rw [he,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]

lemma allowed_card_nonzero (y : F) (hy : y≠0) :
    (Finset.univ.filter (fun z : F ↦ z≠0 ∧ y+z≠0)).card=Fintype.card F-2 := by
  have he : Finset.univ.filter (fun z : F ↦ z≠0 ∧ y+z≠0)=
      (Finset.univ.erase (0:F)).erase (-y) := by
    ext z
    have hn : y+z≠0 ↔ z≠-y := by constructor <;> intro h h' <;> apply h <;> linear_combination h'
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,hn]
    tauto
  rw [he,Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨neg_ne_zero.mpr hy,Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
  omega

/-- The average includes all translations, with zero parameters safely
removed. An admissible translation still needs a joint selection theorem. -/
theorem safeRow_translation_average (U : Finset F) (y : F) :
    (∑ a : F, (safeRow U a y).card)=
      U.card*(Fintype.card F-if y=0 then 1 else 2) := by
  rw [sum_card_safeRow]
  by_cases hy : y=0
  · subst y
    rw [allowed_card_zero,if_pos rfl]
  · rw [allowed_card_nonzero y hy,if_neg hy]

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Even a constant parameter family need not have decreasing spatial rows. -/
theorem constant_parameters_not_antitone :
    ¬Antitone (fun k : ℕ ↦ row ({1}:Finset (ZMod 5)) 0 (k:ZMod 5)) := by
  intro h
  have hU : ∀ u∈({1}:Finset (ZMod 5)), (0:ZMod 5)+u ≠ 0 := by simp
  have hmem : (3:ZMod 5)∈row ({1}:Finset (ZMod 5)) 0 1 := by
    rw [row_eq_safeRow _ _ _ hU]
    norm_num [safeRow,label]
    decide
  have hnot : (3:ZMod 5)∉row ({1}:Finset (ZMod 5)) 0 0 := by
    rw [row_zero _ _ hU]
    norm_num
    decide
  exact hnot (h (show 0 ≤ 1 by omega) hmem)

end Erdos66TaperedRowAverage
