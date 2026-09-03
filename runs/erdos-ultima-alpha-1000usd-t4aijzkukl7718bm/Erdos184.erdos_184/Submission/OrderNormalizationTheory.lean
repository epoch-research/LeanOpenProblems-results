import Submission.OrderNormalizationDefs
import Submission.MarkedOrderCycle

/-! Structural normalization of marked orders, valid for every number of markers. -/
namespace Erdos184Work.SmallOrderNormalization
open CycleSegments LabelKernel
set_option maxHeartbeats 1000000

lemma raw_eq_pow (n : ℕ) (o : Marked.Order n) (i : Fin (n+2)) :
    raw n o i = (Marked.numberedPerm n o ^ i.val) 0 := by
  rw [raw,Marked.fastNext_coe_numberedPerm]
  rfl

lemma raw_injective (n : ℕ) (o : Marked.Order n) : Function.Injective (raw n o) := by
  intro i j h
  simp only [raw_eq_pow] at h
  have hp : (Marked.numberedPerm n o).IsCycleOn (Finset.univ : Finset (Fin (n+2))) := by
    simpa using Marked.numberedPerm_isCycleOn n o
  have he := (hp.pow_apply_eq_pow_apply (Finset.mem_univ (0 : Fin (n+2)))).mp h
  simp only [Finset.card_univ,Fintype.card_fin,Nat.ModEq,
    Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at he
  exact Fin.ext he

lemma raw_zero (n : ℕ) (o : Marked.Order n) : raw n o 0 = 0 := by
  rw [raw_eq_pow]
  rfl

lemma raw_next (n : ℕ) (o : Marked.Order n) (i : Fin (n+2)) :
    Marked.nextFin n o (raw n o i) = raw n o (i+1) := by
  have hp : (Marked.numberedPerm n o).IsCycleOn (Finset.univ : Finset (Fin (n+2))) := by
    simpa using Marked.numberedPerm_isCycleOn n o
  rw [← Marked.numberedPerm_apply,raw_eq_pow,raw_eq_pow]
  rw [← Equiv.Perm.mul_apply,← pow_succ']
  apply (hp.pow_apply_eq_pow_apply (Finset.mem_univ (0 : Fin (n+2)))).mpr
  simp [Nat.ModEq,Fin.val_add,Fin.val_one]

lemma normalized_valid_all (n : ℕ) (o : Marked.Order n) :
    (normalized n o).Valid id (Marked.nextFin n o) := by
  have hinj := raw_injective n o
  by_cases h : forward n o = true
  · simp only [CycleData.Valid,normalized,h,ite_true]
    refine ⟨hinj,hinj,?_⟩
    intro i
    exact Or.inl ⟨rfl,raw_next n o i⟩
  · simp only [CycleData.Valid,normalized,h,ite_false]
    refine ⟨?_,?_,?_⟩
    · intro i j he
      apply hinj at he
      exact neg_injective (sub_left_inj.mp he)
    · intro i j he
      exact neg_injective (hinj he)
    · intro i
      refine Or.inr ⟨?_,?_⟩
      · simpa only [sub_add_cancel] using raw_next n o (-i-1)
      · change raw n o (-i-1) = raw n o (-(i+1))
        congr 1
        abel

lemma normalized_first_all (n : ℕ) (o : Marked.Order n) :
    (normalized n o).vertex 0 = 0 := by
  simp only [normalized,neg_zero]
  split <;> exact raw_zero n o

lemma last_eq_neg_one (n : ℕ) : (Fin.last (n+1) : Fin (n+2)) = -1 := by
  apply Fin.ext
  simpa using (Fin.coe_neg_one (n := n+1)).symm

lemma normalized_orientation_all (n : ℕ) (o : Marked.Order n) :
    n = 0 ∨ (normalized n o).vertex 1 < (normalized n o).vertex (Fin.last (n+1)) := by
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have hne : (1 : Fin (n+2)) ≠ Fin.last (n+1) := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_one,Fin.val_last] at he
    omega
  have hrne := (raw_injective n o).ne hne
  by_cases h : forward n o = true
  · have hlt : (raw n o 1).val < (raw n o (Fin.last (n+1))).val := by
      simpa only [forward,decide_eq_true_eq] using h
    simpa only [normalized,h,ite_true] using hlt
  · have hle : (raw n o (Fin.last (n+1))).val ≤ (raw n o 1).val := by
      have hf : ¬ (raw n o 1).val < (raw n o (Fin.last (n+1))).val := by
        simpa only [forward,decide_eq_true_eq] using h
      omega
    have hlt : raw n o (Fin.last (n+1)) < raw n o 1 :=
      lt_of_le_of_ne hle (Ne.symm hrne)
    simpa only [normalized,h,ite_false,last_eq_neg_one,neg_neg] using hlt

lemma normalized_support (n : ℕ) (o : Marked.Order n) :
    (normalized n o).support = Finset.univ := by
  have h := (normalized_valid_all n o).1
  have hs := (Finite.injective_iff_surjective).mp h
  exact Finset.image_univ_of_surjective hs

#print axioms normalized_valid_all
#print axioms normalized_orientation_all
end Erdos184Work.SmallOrderNormalization
