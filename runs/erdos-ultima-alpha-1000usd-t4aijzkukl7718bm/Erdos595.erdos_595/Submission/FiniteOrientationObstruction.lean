import FormalConjecturesUtil

/-!
A finite-orientation obstruction for the triangle hypergraph of a complete
tripartite graph. This does not settle Erdős Problem 595: complete tripartite
graphs are finitely colorable, but the stronger greedy ordering criterion fails.
-/

open Set Cardinal
namespace Erdos595FiniteOrientation

abbrev B := Set ℕ
abbrev C := Set B

lemma union_first_bound (f : ℕ → B → Finset C) :
    Cardinal.mk (⋃ n, ⋃ b, (f n b : Set C)) ≤ Cardinal.mk B := by
  have hB : Cardinal.aleph0 ≤ Cardinal.mk B := by
    simpa only [B, Cardinal.mk_set, Cardinal.mk_nat] using Cardinal.aleph0_le_continuum
  have hfin : ∀ n b, Cardinal.mk (f n b : Set C) ≤ Cardinal.aleph0 := by
    intro n b
    exact Cardinal.mk_le_aleph0 (α := (f n b : Set C))
  calc
    Cardinal.mk (⋃ n, ⋃ b, (f n b : Set C))
        ≤ Cardinal.mk ℕ * ⨆ n, Cardinal.mk (⋃ b, (f n b : Set C)) :=
      Cardinal.mk_iUnion_le _
    _ ≤ Cardinal.aleph0 * Cardinal.mk B := by
      rw [Cardinal.mk_nat]
      apply mul_le_mul_left'
      apply ciSup_le'
      intro n
      calc
        Cardinal.mk (⋃ b, (f n b : Set C))
            ≤ Cardinal.mk B * ⨆ b, Cardinal.mk (f n b : Set C) :=
          Cardinal.mk_iUnion_le _
        _ ≤ Cardinal.mk B * Cardinal.aleph0 :=
          mul_le_mul_left' (ciSup_le' (hfin n)) _
        _ ≤ Cardinal.mk B * Cardinal.mk B := mul_le_mul_left' hB _
        _ = Cardinal.mk B := Cardinal.mul_eq_self hB
    _ ≤ Cardinal.mk B * Cardinal.mk B := mul_le_mul_right' hB _
    _ = Cardinal.mk B := Cardinal.mul_eq_self hB

lemma exists_outside_first (f : ℕ → B → Finset C) :
    ∃ c : C, ∀ n b, c ∉ f n b := by
  classical
  by_contra h
  push_neg at h
  have hu : (⋃ n, ⋃ b, (f n b : Set C)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro c
    obtain ⟨n, b, hc⟩ := h c
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨b, hc⟩⟩
  have hh := union_first_bound f
  rw [hu, Cardinal.mk_univ] at hh
  have hlt : Cardinal.mk B < Cardinal.mk C := by
    simpa only [C, Cardinal.mk_set] using Cardinal.cantor (Cardinal.mk B)
  exact (not_le_of_gt hlt) hh

/-- Three finite-valued maps on the pairs of three sufficiently large parts
cannot account for every triple by one of its pairs. -/
theorem free_triple (f : ℕ → B → Finset C) (g : ℕ → C → Finset B)
    (h : B → C → Finset ℕ) :
    ∃ a b c, c ∉ f a b ∧ b ∉ g a c ∧ a ∉ h b c := by
  classical
  obtain ⟨c, hc⟩ := exists_outside_first f
  have hcount : (⋃ a, (g a c : Set B)).Countable :=
    Set.countable_iUnion (fun a => (g a c).countable_toSet)
  have hbex : ∃ b : B, b ∉ ⋃ a, (g a c : Set B) := by
    by_contra hh
    push_neg at hh
    have hu : (⋃ a, (g a c : Set B)) = Set.univ := Set.eq_univ_of_forall hh
    rw [hu] at hcount
    haveI : Countable B := Set.countable_univ_iff.mp hcount
    have hle : Cardinal.mk B ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
    have hlt : Cardinal.aleph0 < Cardinal.mk B := by
      simpa only [B, Cardinal.mk_set, Cardinal.mk_nat] using Cardinal.cantor Cardinal.aleph0
    exact (not_le_of_gt hlt) hle
  obtain ⟨b, hb⟩ := hbex
  let a := (h b c).sup id + 1
  have ha : a ∉ h b c := by
    intro ha
    have hle := Finset.le_sup (f := id) ha
    change a ≤ (h b c).sup id at hle
    dsimp [a] at hle
    omega
  refine ⟨a, b, c, hc a b, ?_, ha⟩
  intro hab
  exact hb (Set.mem_iUnion.mpr ⟨a, hab⟩)

#print axioms free_triple
end Erdos595FiniteOrientation
