import FormalConjecturesUtil

/-! A bounded-conflict family contains a proportionally large disjoint
subfamily. This is an auxiliary finite combinatorial lemma. -/
namespace Erdos66BoundedConflict
open scoped Classical
set_option maxHeartbeats 1000000

variable {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]

theorem exists_large_disjoint (S : Finset κ) (E : κ → Finset ι) (D : ℕ)
    (hne : ∀ e ∈ S, (E e).Nonempty)
    (hdeg : ∀ e ∈ S, (S.filter (fun f ↦ ¬ Disjoint (E e) (E f))).card ≤ D) :
    ∃ M ⊆ S, (M : Set κ).Pairwise (fun e f ↦ Disjoint (E e) (E f)) ∧
      S.card ≤ D * M.card := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases hs : S.Nonempty
  · obtain ⟨e,he⟩ := hs
    let T := S.filter (fun f ↦ Disjoint (E e) (E f))
    have hTS : T ⊆ S := Finset.filter_subset _ _
    have heT : e ∉ T := by
      intro h
      have hd := (Finset.mem_filter.mp h).2
      obtain ⟨i,hi⟩ := hne e he
      exact Finset.disjoint_left.mp hd hi hi
    have hproper : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hTS,fun h ↦ heT (h.symm ▸ he)⟩
    have hdegT : ∀ f ∈ T, (T.filter (fun g ↦ ¬ Disjoint (E f) (E g))).card ≤ D := by
      intro f hf
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hTS)).trans (hdeg f (hTS hf))
    obtain ⟨M,hMT,hM,hcard⟩ := ih T hproper (fun f hf ↦ hne f (hTS hf)) hdegT
    have heM : e ∉ M := fun h ↦ heT (hMT h)
    refine ⟨insert e M,Finset.insert_subset he (hMT.trans hTS),?_,?_⟩
    · intro f hf g hg hfg
      simp only [Finset.mem_coe,Finset.mem_insert] at hf hg
      rcases hf with rfl | hf <;> rcases hg with rfl | hg
      · exact (hfg rfl).elim
      · exact (Finset.mem_filter.mp (hMT hg)).2
      · exact (Finset.mem_filter.mp (hMT hf)).2.symm
      · exact hM hf hg hfg
    · have hh := Finset.card_filter_add_card_filter_not (s := S)
        (p := fun f ↦ Disjoint (E e) (E f))
      have hd := hdeg e he
      rw [Finset.card_insert_of_notMem heM]
      dsimp only [T] at hcard
      rw [Nat.mul_add,Nat.mul_one]
      omega
  · refine ⟨∅,Finset.empty_subset _,by simp,?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hs]
end Erdos66BoundedConflict
