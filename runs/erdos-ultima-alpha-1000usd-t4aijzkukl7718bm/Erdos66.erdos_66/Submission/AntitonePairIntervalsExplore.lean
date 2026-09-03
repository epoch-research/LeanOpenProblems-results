import Submission.OriginRepairExplore

/-! For antitone row families, the row indices in which one fixed pair is
active form an interval. A half-row support bounds the number of such pairs. -/
namespace Erdos66AntitonePairIntervals
open Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1600000

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def active (C D : ℕ → Finset G) (q : ℕ) (z a : G) : Finset ℕ :=
  (Finset.range (q+1)).filter (fun k ↦ a ∈ C k ∧ z-a ∈ D (q-k))

lemma mem_active (C D : ℕ → Finset G) (q : ℕ) (z a : G) (k : ℕ) :
    k ∈ active C D q z a ↔ k ≤ q ∧ a ∈ C k ∧ z-a ∈ D (q-k) := by
  simp only [active,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

lemma active_convex (C D : ℕ → Finset G) (hC : Antitone C) (hD : Antitone D)
    (q : ℕ) (z a : G) (i j k : ℕ)
    (hi : i ∈ active C D q z a) (hk : k ∈ active C D q z a)
    (hij : i ≤ j) (hjk : j ≤ k) : j ∈ active C D q z a := by
  rw [mem_active] at hi hk ⊢
  exact ⟨by omega,hC hjk hk.2.1,hD (by omega) hi.2.2⟩

lemma active_eq_interval (C D : ℕ → Finset G) (hC : Antitone C) (hD : Antitone D)
    (q : ℕ) (z a : G) :
    ∃ l u : ℕ, l ≤ u ∧ u ≤ q+1 ∧ active C D q z a = Finset.Ico l u := by
  let S := active C D q z a
  by_cases hS : S.Nonempty
  · let l := S.min' hS
    let d := S.max' hS
    have hl : l ∈ S := Finset.min'_mem _ _
    have hd : d ∈ S := Finset.max'_mem _ _
    have hld : l ≤ d := Finset.min'_le _ _ hd
    have hdq : d ≤ q := (mem_active C D q z a d).mp hd |>.1
    refine ⟨l,d+1,by omega,by omega,?_⟩
    ext k
    constructor
    · intro hk
      have h1 := Finset.min'_le S k hk
      have h2 := Finset.le_max' S k hk
      exact Finset.mem_Ico.mpr ⟨h1,by dsimp [d]; omega⟩
    · intro hk
      obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp hk
      exact active_convex C D hC hD q z a l k d hl hd h1 (by omega)
  · refine ⟨0,0,le_rfl,Nat.zero_le _,?_⟩
    rw [Finset.Ico_self]
    exact Finset.not_nonempty_iff_eq_empty.mp hS

noncomputable def halfSupport (C D : ℕ → Finset G) (q : ℕ) (z : G) : Finset G :=
  ((C 0).filter (fun a ↦ z-a ∈ D (q/2))) ∪
    ((C (q/2)).filter (fun a ↦ z-a ∈ D 0))

lemma active_mem_halfSupport (C D : ℕ → Finset G) (hC : Antitone C) (hD : Antitone D)
    (q : ℕ) (z a : G) (k : ℕ) (hk : k ∈ active C D q z a) :
    a ∈ halfSupport C D q z := by
  obtain ⟨hkq,hak,hbk⟩ := (mem_active C D q z a k).mp hk
  rw [halfSupport,Finset.mem_union]
  by_cases hh : q/2 ≤ k
  · exact Or.inr (Finset.mem_filter.mpr ⟨hC hh hak,hD (Nat.zero_le _) hbk⟩)
  · exact Or.inl (Finset.mem_filter.mpr
      ⟨hC (Nat.zero_le _) hak,hD (by omega) hbk⟩)

lemma active_empty_off_halfSupport (C D : ℕ → Finset G) (hC : Antitone C) (hD : Antitone D)
    (q : ℕ) (z a : G) (ha : a ∉ halfSupport C D q z) : active C D q z a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  exact ha (active_mem_halfSupport C D hC hD q z a k hk)

lemma halfSupport_card_le (C D : ℕ → Finset G) (q : ℕ) (z : G) :
    (halfSupport C D q z).card ≤ pairCount (C 0) (D (q/2)) z +
      pairCount (C (q/2)) (D 0) z := by
  exact Finset.card_union_le _ _

end Erdos66AntitonePairIntervals
