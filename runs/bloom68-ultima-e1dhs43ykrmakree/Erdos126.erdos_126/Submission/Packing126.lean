import FormalConjecturesUtil

/-! A finite packing estimate for symmetric forbidden neighborhoods. -/

namespace E126.Packing126

variable {ι : Type*} [DecidableEq ι]

def Independent (bad : ι → Finset ι) (T : Finset ι) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, i ≠ j → j ∉ bad i

/-- A maximal independent set and its forbidden neighborhoods cover the ambient set. -/
theorem card_le (Y : Finset ι) (bad : ι → Finset ι)
    (hsymm : ∀ i j, j ∈ bad i ↔ i ∈ bad j)
    (d k : ℕ) (hdegree : ∀ i, (bad i).card ≤ d)
    (hind : ∀ T ⊆ Y, Independent bad T → T.card ≤ k) :
    Y.card ≤ k * (d + 1) := by
  classical
  let S := Y.powerset.filter (Independent bad)
  have hS : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    simp [Independent]
  obtain ⟨T, hT, hmax⟩ := S.exists_max_image Finset.card hS
  obtain ⟨hTY, hTi⟩ := Finset.mem_filter.mp hT
  have hTY' : T ⊆ Y := Finset.mem_powerset.mp hTY
  have hcover : Y ⊆ T.biUnion (fun i => insert i (bad i)) := by
    intro y hy
    by_contra hnot
    have hyT : y ∉ T := by
      intro hyT
      exact hnot (Finset.mem_biUnion.mpr ⟨y, hyT, Finset.mem_insert_self _ _⟩)
    have hybad : ∀ i ∈ T, y ∉ bad i := by
      intro i hi hbad
      exact hnot (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_insert_of_mem hbad⟩)
    have hnew : Independent bad (insert y T) := by
      intro i hi j hj hij
      by_cases hiy : i = y
      · subst i
        have hjT : j ∈ T := (Finset.mem_insert.mp hj).resolve_left (Ne.symm hij)
        exact fun h => hybad j hjT ((hsymm y j).mp h)
      · have hiT : i ∈ T := (Finset.mem_insert.mp hi).resolve_left hiy
        by_cases hjy : j = y
        · subst j
          exact hybad i hiT
        · have hjT : j ∈ T := (Finset.mem_insert.mp hj).resolve_left hjy
          exact hTi i hiT j hjT hij
    have hmem : insert y T ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hy hTY'), hnew⟩
    have hc := hmax (insert y T) hmem
    rw [Finset.card_insert_of_notMem hyT] at hc
    omega
  calc
    Y.card ≤ (T.biUnion (fun i => insert i (bad i))).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ T, (insert i (bad i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ T, (d + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.card_insert_le i (bad i)).trans (Nat.add_le_add_right (hdegree i) 1)
    _ = T.card * (d + 1) := by simp
    _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ (hind T hTY' hTi)

end E126.Packing126
