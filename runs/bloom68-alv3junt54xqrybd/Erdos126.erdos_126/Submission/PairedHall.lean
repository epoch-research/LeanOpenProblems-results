import Submission.PairedCore

/-!
# A finite capacity version of Hall for coherent pairs

Rows have paired source and target sets.  Two pairs are nested on both
sides, or disjoint on both sides.  A row lies in its source set, the row
labels are injective, and each source set has size at most `c` times its
target set.  These hypotheses imply the capacity Hall inequalities.

The ancestor-most witness is chosen by the *sum* of the two cardinalities.
This is important when finite target sets coincide: reverse containment
and equality of total size force equality of both sides.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos126Aux.Paired

variable {ρ ι : Type*}

/-- Reverse paired containment together with nonincreasing total size
forces containment in the other direction on both sides. -/
lemma paired_subset_of_size_le {S₁ S₂ T₁ T₂ : Finset ι}
    (h : S₂ ⊆ S₁ ∧ T₂ ⊆ T₁)
    (hsize : S₁.card + T₁.card ≤ S₂.card + T₂.card) :
    S₁ ⊆ S₂ ∧ T₁ ⊆ T₂ := by
  have hS := Finset.card_le_card h.1
  have hT := Finset.card_le_card h.2
  have eS : S₂ = S₁ := Finset.eq_of_subset_of_card_le h.1 (by omega)
  have eT : T₂ = T₁ := Finset.eq_of_subset_of_card_le h.2 (by omega)
  exact ⟨le_of_eq eS.symm, le_of_eq eT.symm⟩

/-- The capacity Hall inequality for coherently nested source/target pairs.
No strictness of either containment, or distinctness of the pairs, is assumed. -/
theorem capacity_hall [DecidableEq ι]
    (a : ρ → ι) (ha : Function.Injective a)
    (S T : ρ → Finset ι) (c : ℕ)
    (hmem : ∀ i, a i ∈ S i)
    (hbal : ∀ i, (S i).card ≤ c * (T i).card)
    (hpair : ∀ i j,
      (S i ⊆ S j ∧ T i ⊆ T j) ∨
      (S j ⊆ S i ∧ T j ⊆ T i) ∨
      (Disjoint (S i) (S j) ∧ Disjoint (T i) (T j)))
    (X : Finset ρ) : X.card ≤ c * (X.biUnion T).card := by
  classical
  induction X using Finset.strongInductionOn with
  | _ X ih =>
    rcases X.eq_empty_or_nonempty with rfl | hX
    · simp
    obtain ⟨m, hm, hmax⟩ :=
      X.exists_max_image (fun i => (S i).card + (T i).card) hX
    let D := X.filter (fun i => a i ∈ S m)
    let E := X.filter (fun i => a i ∉ S m)
    have hE : E ⊂ X := by
      apply Finset.filter_ssubset.mpr
      exact ⟨m, hm, by simpa using hmem m⟩
    have hIH := ih E hE
    have hD : D.card ≤ (S m).card := by
      apply Finset.card_le_card_of_injOn a
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · exact ha.injOn
    have hdis : Disjoint (T m) (E.biUnion T) := by
      apply Finset.disjoint_left.mpr
      intro j hj hjE
      obtain ⟨i, hiE, hji⟩ := Finset.mem_biUnion.mp hjE
      obtain ⟨hiX, hi⟩ := Finset.mem_filter.mp hiE
      have hd : Disjoint (T i) (T m) := by
        rcases hpair i m with hin | hrev | hd
        · exact False.elim (hi (hin.1 (hmem i)))
        · have hin := paired_subset_of_size_le hrev (hmax i hiX)
          exact False.elim (hi (hin.1 (hmem i)))
        · exact hd.2
      exact Finset.disjoint_left.mp hd hji hj
    have htarget : T m ∪ E.biUnion T ⊆ X.biUnion T := by
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_biUnion.mpr ⟨m, hm, hj⟩
      · obtain ⟨i, hiE, hji⟩ := Finset.mem_biUnion.mp hj
        exact Finset.mem_biUnion.mpr ⟨i, (Finset.mem_filter.mp hiE).1, hji⟩
    calc
      X.card = D.card + E.card :=
        (Finset.card_filter_add_card_filter_not (s := X) (p := fun i => a i ∈ S m)).symm
      _ ≤ c * (T m).card + c * (E.biUnion T).card :=
        Nat.add_le_add (hD.trans (hbal m)) hIH
      _ = c * (T m ∪ E.biUnion T).card := by
        rw [Finset.card_union_of_disjoint hdis, Nat.mul_add]
      _ ≤ c * (X.biUnion T).card :=
        Nat.mul_le_mul_left c (Finset.card_le_card htarget)

/-- Hall applied to `c` labeled copies of every target. -/
theorem exists_capacity_injection [Finite ρ] [DecidableEq ι]
    (a : ρ → ι) (ha : Function.Injective a)
    (S T : ρ → Finset ι) (c : ℕ)
    (hmem : ∀ i, a i ∈ S i)
    (hbal : ∀ i, (S i).card ≤ c * (T i).card)
    (hpair : ∀ i j,
      (S i ⊆ S j ∧ T i ⊆ T j) ∨
      (S j ⊆ S i ∧ T j ⊆ T i) ∨
      (Disjoint (S i) (S j) ∧ Disjoint (T i) (T j))) :
    ∃ g : ρ → ι × Fin c, Function.Injective g ∧ ∀ i, (g i).1 ∈ T i := by
  classical
  let N : ρ → Finset (ι × Fin c) := fun i => T i ×ˢ (Finset.univ : Finset (Fin c))
  have hHall : ∀ X : Finset ρ, X.card ≤ (X.biUnion N).card := by
    intro X
    have he : X.biUnion N = (X.biUnion T) ×ˢ (Finset.univ : Finset (Fin c)) := by
      ext p
      simp only [N, Finset.mem_biUnion, Finset.mem_product, Finset.mem_univ,
        and_true]
    rw [he, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    simpa only [Nat.mul_comm] using capacity_hall a ha S T c hmem hbal hpair X
  obtain ⟨g, hg, hN⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  exact ⟨g, hg, fun i => (Finset.mem_product.mp (hN i)).1⟩

/-- Projecting an injection into `c` target copies gives fibers of size at most `c`. -/
lemma capacity_of_injective_copies [Fintype ρ] [DecidableEq ι]
    (c : ℕ) (g : ρ → ι × Fin c) (hg : Function.Injective g) (j : ι) :
    (Finset.univ.filter (fun i => (g i).1 = j)).card ≤ c := by
  classical
  have hi : Set.InjOn (fun i => (g i).2)
      (Finset.univ.filter (fun i => (g i).1 = j) : Finset ρ) := by
    intro i hi k hk hik
    apply hg
    apply Prod.ext
    · exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm
    · exact hik
  have h := Finset.card_le_card_of_injOn (fun i => (g i).2)
    (t := (Finset.univ : Finset (Fin c))) (by intro i hi; simp) hi
  simpa using h

/-- A choice in each target set, with at most `c` rows choosing any one target. -/
theorem exists_capacity_selection [Fintype ρ] [DecidableEq ι]
    (a : ρ → ι) (ha : Function.Injective a)
    (S T : ρ → Finset ι) (c : ℕ)
    (hmem : ∀ i, a i ∈ S i)
    (hbal : ∀ i, (S i).card ≤ c * (T i).card)
    (hpair : ∀ i j,
      (S i ⊆ S j ∧ T i ⊆ T j) ∨
      (S j ⊆ S i ∧ T j ⊆ T i) ∨
      (Disjoint (S i) (S j) ∧ Disjoint (T i) (T j))) :
    ∃ F : ρ → ι, (∀ j, (Finset.univ.filter (fun i => F i = j)).card ≤ c) ∧
      ∀ i, F i ∈ T i := by
  obtain ⟨g, hg, hT⟩ := exists_capacity_injection a ha S T c hmem hbal hpair
  exact ⟨fun i => (g i).1, capacity_of_injective_copies c g hg, hT⟩

end Erdos126Aux.Paired
