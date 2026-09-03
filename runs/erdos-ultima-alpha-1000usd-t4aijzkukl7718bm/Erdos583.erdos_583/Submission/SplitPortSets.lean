import Submission.NearCompleteCorePorts

/-! Reindex two families of exterior pieces when one pair is split. -/
namespace Erdos583SplitPortSetsDevelopment
open scoped Classical
set_option maxHeartbeats 1400000
set_option Elab.async false

lemma split_port_sets_pairwise {E : Type*} {t : ℕ}
    (A B : Fin t → Set E) (j : Fin t)
    (hd : Pairwise (fun z w : Fin t × Bool ↦
      Disjoint (if z.2 then A z.1 else B z.1) (if w.2 then A w.1 else B w.1))) :
    Pairwise (fun z w : Fin (t+1) × Bool ↦
      Disjoint (if z.2 then Fin.cases (motive := fun _ ↦ Set E) ∅ A z.1 else Fin.cases (motive := fun _ ↦ Set E) (B j) (fun i ↦ if i=j then ∅ else B i) z.1)
        (if w.2 then Fin.cases (motive := fun _ ↦ Set E) ∅ A w.1 else Fin.cases (motive := fun _ ↦ Set E) (B j) (fun i ↦ if i=j then ∅ else B i) w.1)) := by
  classical
  have hAA (i l : Fin t) (h : i ≠ l) : Disjoint (A i) (A l) := by
    exact hd (i := (i,true)) (j := (l,true)) (fun he ↦ h (congrArg Prod.fst he))
  have hBB (i l : Fin t) (h : i ≠ l) : Disjoint (B i) (B l) := by
    exact hd (i := (i,false)) (j := (l,false)) (fun he ↦ h (congrArg Prod.fst he))
  have hAB (i l : Fin t) : Disjoint (A i) (B l) := by
    exact hd (i := (i,true)) (j := (l,false)) (by intro he; cases congrArg Prod.snd he)
  rintro ⟨i,bi⟩ ⟨l,bl⟩ hne
  induction i using Fin.cases with
  | zero =>
    induction l using Fin.cases with
    | zero =>
      cases bi <;> cases bl <;> simp only [Fin.cases_zero,Bool.false_eq_true,if_false,if_true]
      · exact (hne rfl).elim
      · exact Set.disjoint_empty _
      · exact Set.empty_disjoint _
      · exact Set.empty_disjoint _
    | succ l =>
      cases bi <;> cases bl <;> simp only [Fin.cases_zero,Fin.cases_succ,Bool.false_eq_true,if_false,if_true]
      · by_cases hl : l=j
        · simp only [if_pos hl]; exact Set.disjoint_empty _
        · rw [if_neg hl]; exact hBB j l (Ne.symm hl)
      · exact (hAB l j).symm
      · exact Set.empty_disjoint _
      · exact Set.empty_disjoint _
  | succ i =>
    induction l using Fin.cases with
    | zero =>
      cases bi <;> cases bl <;> simp only [Fin.cases_zero,Fin.cases_succ,Bool.false_eq_true,if_false,if_true]
      · by_cases hi : i=j
        · simp only [if_pos hi]; exact Set.empty_disjoint _
        · rw [if_neg hi]; exact hBB i j hi
      · exact Set.disjoint_empty _
      · exact hAB i j
      · exact Set.disjoint_empty _
    | succ l =>
      cases bi <;> cases bl <;> simp only [Fin.cases_succ,Bool.false_eq_true,if_false,if_true]
      · by_cases hi : i=j
        · rw [if_pos hi]; exact Set.empty_disjoint _
        · by_cases hl : l=j
          · rw [if_pos hl]; exact Set.disjoint_empty _
          · rw [if_neg hi,if_neg hl]
            exact hBB i l (by rintro rfl; exact hne rfl)
      · by_cases hi : i=j
        · rw [if_pos hi]; exact Set.empty_disjoint _
        · rw [if_neg hi]; exact (hAB l i).symm
      · by_cases hl : l=j
        · rw [if_pos hl]; exact Set.disjoint_empty _
        · rw [if_neg hl]; exact hAB i l
      · exact hAA i l (by rintro rfl; exact hne rfl)

lemma split_port_sets_union {E : Type*} {t : ℕ}
    (A B : Fin t → Set E) (j : Fin t) :
    (⋃ i : Fin (t+1), (Fin.cases (motive := fun _ ↦ Set E) ∅ A i) ∪ (Fin.cases (motive := fun _ ↦ Set E) (B j) (fun l ↦ if l=j then ∅ else B l) i))=
      ⋃ i : Fin t, A i ∪ B i := by
  classical
  ext e
  simp only [Set.mem_iUnion,Set.mem_union]
  constructor
  · rintro ⟨i,hi⟩
    induction i using Fin.cases with
    | zero =>
      have hh : e ∈ B j := by simpa only [Fin.cases_zero,Set.notMem_empty,false_or] using hi
      exact ⟨j,Or.inr hh⟩
    | succ i =>
      simp only [Fin.cases_succ] at hi
      rcases hi with hi | hi
      · exact ⟨i,Or.inl hi⟩
      · by_cases hij : i=j
        · simp only [if_pos hij,Set.notMem_empty] at hi
        · rw [if_neg hij] at hi
          exact ⟨i,Or.inr hi⟩
  · rintro ⟨i,hi | hi⟩
    · exact ⟨i.succ,Or.inl hi⟩
    · by_cases hij : i=j
      · subst i; exact ⟨0,Or.inr hi⟩
      · refine ⟨i.succ,Or.inr ?_⟩
        simpa only [Fin.cases_succ,if_neg hij] using hi

end Erdos583SplitPortSetsDevelopment
