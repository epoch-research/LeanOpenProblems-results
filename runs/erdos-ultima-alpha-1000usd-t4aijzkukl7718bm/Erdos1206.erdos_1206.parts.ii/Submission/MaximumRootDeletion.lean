import Submission.CubicHypergraph

/-! Deleting maximum roots is compatible with every earlier prefix. -/
namespace Erdos1206.MaximumRootDeletion
open Finset CubicHypergraph
open scoped Classical

noncomputable def deleted (E : Finset (Finset ℕ)) : Finset ℕ :=
  E.image (fun e => e.sup id)

noncomputable def keep (S : Finset ℕ) (E : Finset (Finset ℕ)) : Finset ℕ :=
  S \ deleted E

lemma prefix_bound (S : Finset ℕ) (E : Finset (Finset ℕ)) (n : ℕ) :
    (S.filter (fun v => v < n)).card ≤
      ((keep S E).filter (fun v => v < n)).card +
      (E.filter (fun e => e ⊆ range n)).card := by
  let P := S.filter (fun v => v < n)
  have hk : (keep S E).filter (fun v => v < n)=P \ deleted E := by
    ext v
    simp only [keep,P,mem_filter,mem_sdiff]
    tauto
  have hs : P ∩ deleted E ⊆ deleted (E.filter (fun e => e ⊆ range n)) := by
    intro v hv
    obtain ⟨hvP,hvd⟩ := mem_inter.mp hv
    obtain ⟨e,he,rfl⟩ := mem_image.mp hvd
    refine mem_image.mpr ⟨e,mem_filter.mpr ⟨he,?_⟩,rfl⟩
    intro w hw
    exact mem_range.mpr ((le_sup (f := id) hw).trans_lt (mem_filter.mp hvP).2)
  have hc : (P ∩ deleted E).card ≤ (E.filter (fun e => e ⊆ range n)).card :=
    (card_le_card hs).trans card_image_le
  rw [hk]
  have hh := card_sdiff_add_card_inter P (deleted E)
  change P.card ≤ _
  omega

lemma edge_not_subset_keep {S : Finset ℕ} {E : Finset (Finset ℕ)}
    {e : Finset ℕ} (he : e∈E) (hne : e.Nonempty) : ¬e ⊆ keep S E := by
  intro hs
  obtain ⟨v,hve,hv⟩ := exists_mem_eq_sup e hne id
  have hkeep := mem_sdiff.mp (hs hve)
  apply hkeep.2
  exact mem_image.mpr ⟨e,he,hv⟩

/-- Every collision is destroyed; no arbitrary choice of an edge vertex is
used in the construction. -/
theorem cubeSidon_keep {M : ℕ} {S : Finset ℕ} (hS : S ⊆ range M) :
    IsSidon ((fun n : ℕ => n^3) '' (keep S (edges M S) : Set ℕ)) := by
  apply (independent_iff_cubeSidon _).mp
  intro N
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨_,hsub,hcol⟩ := mem_edges.mp he
  have hs : e ⊆ S := fun v hv => (mem_sdiff.mp (hsub hv)).1
  have heM : e∈edges M S := mem_edges.mpr ⟨hs.trans hS,hs,hcol⟩
  have hne : e.Nonempty := card_pos.mp (by rw [hcol.card]; omega)
  exact edge_not_subset_keep heM hne hsub

/-- The loss in any prefix is at most the number of collisions wholly
contained in that prefix, even when the sampling cutoff is much larger. -/
theorem cubic_prefix_bound {M : ℕ} {S : Finset ℕ} (hS : S ⊆ range M) (n : ℕ) :
    (S.filter (fun v => v < n)).card ≤
      ((keep S (edges M S)).filter (fun v => v < n)).card + (edges n S).card := by
  have hh := prefix_bound S (edges M S) n
  have heq : (edges M S).filter (fun e => e ⊆ range n)=edges n S := by
    ext e
    simp only [mem_filter,mem_edges]
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · exact fun h => ⟨⟨h.2.1.trans hS,h.2⟩,h.1⟩
  rwa [heq] at hh

#print axioms cubeSidon_keep
#print axioms cubic_prefix_bound
end Erdos1206.MaximumRootDeletion
