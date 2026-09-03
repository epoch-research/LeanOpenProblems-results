import Submission.Work
import Submission.CutVertexParity

/-! Nontrivial branches at a vertex of a smallest failure. -/
open SimpleGraph Erdos583Work
namespace Erdos583CutBranchesDevelopment
open Erdos583Work.VertexCritical Erdos583CutVertexParityDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- A branch excludes its attachment vertex. Its boundary-degree parity is
opposite to its number of vertices, provided both cut sides are nontrivial. -/
lemma branch_parity {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (A : Set (Fin n)) (u : Fin n) (hu : u ∉ A)
    (hclosed : ∀ x ∈ A, ∀ y, G.Adj x y → y=u ∨ y ∈ A)
    (hA : 2 ≤ A.ncard) (hcA : 2 ≤ (insert u A)ᶜ.ncard) :
    Odd (G.neighborSet u ∩ A).ncard ↔ Odd (A.ncard+1) := by
  have hc := Set.ncard_insert_of_notMem hu
  have hh := nontrivial_cut_side_parity hsmall hG hfail (insert u A) u (Or.inl rfl) (by
    intro x hx y hy hxy
    rcases hx with hx|hx
    · exact hx
    · exact (hy (hclosed x hx y hxy)).elim) (by omega) hcA
  rw [induced_neighbor_card,hc] at hh
  have he : G.neighborSet u ∩ insert u A=G.neighborSet u ∩ A := by
    ext x
    constructor
    · rintro ⟨hx,rfl|hxA⟩
      · exact (G.loopless _ hx).elim
      · exact ⟨hx,hxA⟩
    · exact fun hx ↦ ⟨hx.1,Or.inr hx.2⟩
  rwa [he] at hh

/-- Two disjoint branches, each containing at least two vertices, leave at
most one vertex outside themselves and the attachment vertex. Thus there
cannot be three nontrivial branches at the same cut vertex. -/
lemma two_nontrivial_branches_exhaust {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (A B : Set (Fin n)) (u : Fin n) (huA : u ∉ A) (huB : u ∉ B) (hdis : Disjoint A B)
    (hclosedA : ∀ x ∈ A, ∀ y, G.Adj x y → y=u ∨ y ∈ A)
    (hclosedB : ∀ x ∈ B, ∀ y, G.Adj x y → y=u ∨ y ∈ B)
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) : (insert u (A ∪ B))ᶜ.ncard ≤ 1 := by
  by_contra hn
  have hR : 2 ≤ (insert u (A ∪ B))ᶜ.ncard := by omega
  have hcA : 2 ≤ (insert u A)ᶜ.ncard := hR.trans (Set.ncard_mono (by
    intro x hx hxa
    exact hx (hxa.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))))
  have hcB : 2 ≤ (insert u B)ᶜ.ncard := hR.trans (Set.ncard_mono (by
    intro x hx hxb
    exact hx (hxb.elim Or.inl (fun h ↦ Or.inr (Or.inr h)))))
  have hparA := branch_parity hsmall hG hfail A u huA hclosedA hA hcA
  have hparB := branch_parity hsmall hG hfail B u huB hclosedB hB hcB
  have hsize : (A ∪ B).ncard=A.ncard+B.ncard := Set.ncard_union_eq hdis
  have hparU := branch_parity hsmall hG hfail (A ∪ B) u (fun hh ↦ hh.elim huA huB) (by
    intro x hx y hxy
    rcases hx with hx|hx
    · exact (hclosedA x hx y hxy).imp_right Or.inl
    · exact (hclosedB x hx y hxy).imp_right Or.inr) (by omega) hR
  have hd : Disjoint (G.neighborSet u ∩ A) (G.neighborSet u ∩ B) :=
    hdis.mono Set.inter_subset_right Set.inter_subset_right
  have hdegree : (G.neighborSet u ∩ (A ∪ B)).ncard =
      (G.neighborSet u ∩ A).ncard+(G.neighborSet u ∩ B).ncard := by
    rw [Set.inter_union_distrib_left,Set.ncard_union_eq hd]
  rw [hdegree,hsize] at hparU
  simp only [Nat.odd_iff] at hparA hparB hparU
  omega

end Erdos583CutBranchesDevelopment
