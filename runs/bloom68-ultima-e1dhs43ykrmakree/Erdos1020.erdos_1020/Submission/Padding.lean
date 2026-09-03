import Submission.Boundary

/-!
# Matching padding

Auxiliary to a possible uniformity induction. This file does not prove the
missing sharp crossover bound and does not use either conjectural theorem.
-/
namespace Erdos1020

/-- A uniform matching can be enlarged by distinct unused vertices if the
ambient cardinality allows it. -/
theorem pad_matching_one {α : Type*} [Fintype α] [DecidableEq α]
    {P H : Finset (Finset α)} {r : ℕ}
    (hu : ∀ a ∈ P, a.card = r)
    (hd : (P : Set (Finset α)).PairwiseDisjoint id)
    (hn : (r + 1) * P.card ≤ Fintype.card α)
    (hH : ∀ a ∈ P, ∀ x ∉ a, insert x a ∈ H) :
    ∃ Q : Finset (Finset α), Q ⊆ H ∧ Q.card = P.card ∧
      (∀ a ∈ Q, a.card = r + 1) ∧
      (Q : Set (Finset α)).PairwiseDisjoint id := by
  classical
  have hc : (P.biUnion id).card = r * P.card := by
    rw [Finset.card_biUnion hd]
    simp only [id_eq]
    rw [Finset.sum_congr rfl hu]
    simp [Nat.mul_comm]
  have hspace : P.card ≤ (P.biUnion id)ᶜ.card := by
    rw [Finset.card_compl, hc]
    have h := hn
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  obtain ⟨U, hU, hUc⟩ := Finset.exists_subset_card_eq hspace
  let e : P ≃ U := Finset.equivOfCardEq hUc.symm
  have hx : ∀ a : P, ∀ b ∈ P, (e a).val ∉ b := by
    intro a b hb hmem
    exact (Finset.mem_compl.mp (hU (e a).property))
      (Finset.mem_biUnion.mpr ⟨b, hb, hmem⟩)
  let B : P → Finset α := fun a ↦ insert (e a).val a.val
  have hBcard : ∀ a, (B a).card = r + 1 := by
    intro a
    change (insert (e a).val a.val).card = r + 1
    rw [Finset.card_insert_of_notMem (hx a a.val a.property), hu a.val a.property]
  have hBdisj : ∀ a b : P, a ≠ b → Disjoint (B a) (B b) := by
    intro a b hab
    have hne : (e a).val ≠ (e b).val := by
      intro h
      exact hab (e.injective (Subtype.ext h))
    apply Finset.disjoint_insert_left.mpr
    refine ⟨?_, Finset.disjoint_insert_right.mpr ⟨hx b a.val a.property, ?_⟩⟩
    · change (e a).val ∉ insert (e b).val b.val
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne, hx a b.val b.property⟩
    · exact hd a.property b.property (fun h ↦ hab (Subtype.ext h))
  have hBinj : Function.Injective B := by
    intro a b hab
    by_contra hne
    have h := hBdisj a b hne
    rw [hab, Finset.disjoint_self_iff_empty] at h
    have hcard := hBcard b
    rw [h, Finset.card_empty] at hcard
    omega
  refine ⟨Finset.univ.image B, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact hH b.val b.property (e b).val (hx b b.val b.property)
  · rw [Finset.card_image_of_injective _ hBinj]
    simp
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact hBcard b
  · intro a ha b hb hab
    obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
    exact hBdisj a' b' (fun h ↦ hab (congrArg B h))

/-- A matching-free family cannot contain every one-vertex extension of a
lower-uniformity matching, provided there are enough vertices for padding. -/
theorem matching_free_of_extensions {α : Type*} [Fintype α] [DecidableEq α]
    {A H : Finset (Finset α)} {r k : ℕ}
    (hu : ∀ a ∈ A, a.card = r)
    (hn : (r + 1) * k ≤ Fintype.card α)
    (hext : ∀ a ∈ A, ∀ x ∉ a, insert x a ∈ H)
    (hfree : ¬ ∃ M : Finset (Finset α),
      M ⊆ H ∧ M.card = k ∧ (M : Set (Finset α)).PairwiseDisjoint id) :
    ¬ ∃ M : Finset (Finset α),
      M ⊆ A ∧ M.card = k ∧ (M : Set (Finset α)).PairwiseDisjoint id := by
  rintro ⟨M, hM, hc, hd⟩
  obtain ⟨Q, hQ, hQc, _, hQd⟩ := pad_matching_one
    (fun a ha ↦ hu a (hM ha)) hd (by simpa [hc] using hn)
    (fun a ha ↦ hext a (hM ha))
  exact hfree ⟨Q, hQ, hQc.trans hc, hQd⟩

#print axioms pad_matching_one
#print axioms matching_free_of_extensions
end Erdos1020
