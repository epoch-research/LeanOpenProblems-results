import Submission.GreedyTripleWitnessTails

/-!
Deterministic heavy/light packing for indexed two-vertex witnesses.
The split is on original incidences; the packing uses selected incidences.
-/
namespace Erdos773.GreedyTwoWitnessPacking
open Finset GreedyTripleWitnessTails
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
lemma selected_incidence_le (T : Finset β) (C : β → Finset α) (I : Finset α) (a : α) :
    ((T.filter (fun i => C i ⊆ I)).filter (fun i => a ∈ C i)).card ≤
      ((link T C a).filter (fun i => (C i).erase a ⊆ I)).card := by
  apply card_le_card
  intro i hi
  obtain ⟨hi,ha⟩ := mem_filter.mp hi
  obtain ⟨hi,hCI⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi,ha⟩,(erase_subset _ _).trans hCI⟩

/-- A bounded number of selected heavy vertices and controlled selected
    links leave a large disjoint selected family when the edge count is large. -/
theorem packing_of_split (T : Finset β) (C : β → Finset α) (A I : Finset α)
    (hC : ∀ i ∈ T, (C i).card = 2) (M₀ M₁ s k : ℕ)
    (hfull : ∀ a, ((link T C a).filter (fun i => (C i).erase a ⊆ I)).card ≤ M₀)
    (hlight : ∀ a, a ∉ A → ((link T C a).filter (fun i => (C i).erase a ⊆ I)).card ≤ M₁)
    (hheavy : (A ∩ I).card ≤ s)
    (hlarge : s*M₀+2*M₁*k < (T.filter (fun i => C i ⊆ I)).card) :
    packedEvent T C k I := by
  let S := T.filter (fun i => C i ⊆ I)
  let R := T.filter (fun i => Disjoint (C i) A)
  let Q := R.filter (fun i => C i ⊆ I)
  have hRT : R ⊆ T := filter_subset _ _
  have hcover : S ⊆ Q ∪ (A ∩ I).biUnion (fun a => S.filter (fun i => a ∈ C i)) := by
    intro i hi
    obtain ⟨hiT,hiI⟩ := mem_filter.mp hi
    by_cases hd : Disjoint (C i) A
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hiT,hd⟩,hiI⟩)
    · obtain ⟨a,ha⟩ := not_disjoint_iff_nonempty_inter.mp hd
      obtain ⟨haC,haA⟩ := mem_inter.mp ha
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨a,mem_inter.mpr ⟨haA,hiI haC⟩,mem_filter.mpr ⟨hi,haC⟩⟩)
  have hcovered : ((A ∩ I).biUnion (fun a => S.filter (fun i => a ∈ C i))).card ≤ s*M₀ := by
    calc
      _ ≤ ∑ a ∈ A ∩ I, (S.filter (fun i => a ∈ C i)).card := card_biUnion_le
      _ ≤ ∑ _a ∈ A ∩ I, M₀ := sum_le_sum (fun a _ =>
        (selected_incidence_le T C I a).trans (hfull a))
      _ = (A ∩ I).card*M₀ := by simp
      _ ≤ _ := Nat.mul_le_mul_right M₀ hheavy
  have hinc (a : α) : (Q.filter (fun i => a ∈ C i)).card ≤ M₁ := by
    by_cases ha : a ∈ A
    · have he : Q.filter (fun i => a ∈ C i) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hi,hai⟩ := mem_filter.mp hi
        have hd := (mem_filter.mp (mem_filter.mp hi).1).2
        exact disjoint_left.mp hd hai ha
      rw [he]
      exact Nat.zero_le _
    · have hs : Q.filter (fun i => a ∈ C i) ⊆ S.filter (fun i => a ∈ C i) := by
        intro i hi
        obtain ⟨hi,hai⟩ := mem_filter.mp hi
        obtain ⟨hiR,hiI⟩ := mem_filter.mp hi
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hRT hiR,hiI⟩,hai⟩
      exact (card_le_card hs).trans ((selected_incidence_le T C I a).trans (hlight a ha))
  have hQ : 2*M₁*k < Q.card := by
    have hh := (card_le_card hcover).trans (card_union_le _ _)
    change s*M₀+2*M₁*k < S.card at hlarge
    omega
  obtain ⟨U,hU,hd,hUI⟩ := selected_packing R C 2 M₁ k
    (fun i hi => card_pos.mp (by rw [hC i (hRT hi)]; decide))
    (fun i hi => (hC i (hRT hi)).le) I hinc hQ
  obtain ⟨hUR,hUk⟩ := mem_powersetCard.mp hU
  exact ⟨U,mem_powersetCard.mpr ⟨hUR.trans hRT,hUk⟩,hd,hUI⟩

theorem split_or_packed (T : Finset β) (C : β → Finset α) (A I : Finset α)
    (hC : ∀ i ∈ T, (C i).card = 2) (M₀ M₁ s k : ℕ)
    (hlarge : s*M₀+2*M₁*k < (T.filter (fun i => C i ⊆ I)).card) :
    (∃ a, linkBad T C a M₀ I) ∨ (∃ a, a ∉ A ∧ linkBad T C a M₁ I) ∨
      s < (A ∩ I).card ∨ packedEvent T C k I := by
  by_cases hfull : ∃ a, linkBad T C a M₀ I
  · exact Or.inl hfull
  right
  by_cases hlight : ∃ a, a ∉ A ∧ linkBad T C a M₁ I
  · exact Or.inl hlight
  right
  by_cases hheavy : s < (A ∩ I).card
  · exact Or.inl hheavy
  right
  apply packing_of_split T C A I hC M₀ M₁ s k _ _ (le_of_not_gt hheavy) hlarge
  · intro a
    exact le_of_not_gt (fun hb => hfull ⟨a,hb⟩)
  · intro a ha
    exact le_of_not_gt (fun hb => hlight ⟨a,ha,hb⟩)

variable [Fintype α]

def heavy (T : Finset β) (C : β → Finset α) (h : ℕ) : Finset α :=
  univ.filter (fun a => h < (link T C a).card)

omit [DecidableEq β] in
lemma not_heavy_degree (T : Finset β) (C : β → Finset α) (h : ℕ) {a : α}
    (ha : a ∉ heavy T C h) : (link T C a).card ≤ h := by
  simpa only [heavy,mem_filter,mem_univ,true_and,not_lt] using ha

omit [DecidableEq β] in
lemma heavy_card_bound (T : Finset β) (C : β → Finset α)
    (hC : ∀ i ∈ T, (C i).card = 2) (h : ℕ) :
    h*(heavy T C h).card ≤ 2*T.card := by
  have hsum : (∑ a : α, (link T C a).card) = 2*T.card := by
    have he := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (univ : Finset α)) (t := T) (fun a i => a ∈ C i)
    change (∑ a : α, (link T C a).card) = ∑ i ∈ T, (univ.filter (fun a => a ∈ C i)).card at he
    rw [he]
    have hf (i : β) : univ.filter (fun a => a ∈ C i) = C i := by ext a; simp
    simp_rw [hf]
    rw [sum_congr rfl hC]
    simp [mul_comm]
  calc
    _ = ∑ _a ∈ heavy T C h, h := by simp [mul_comm]
    _ ≤ ∑ a ∈ heavy T C h, (link T C a).card := by
      apply sum_le_sum
      intro a ha
      exact (mem_filter.mp ha).2.le
    _ ≤ ∑ a : α, (link T C a).card :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = _ := hsum

#print axioms selected_incidence_le
#print axioms packing_of_split
#print axioms split_or_packed
#print axioms not_heavy_degree
#print axioms heavy_card_bound
end
end Erdos773.GreedyTwoWitnessPacking
