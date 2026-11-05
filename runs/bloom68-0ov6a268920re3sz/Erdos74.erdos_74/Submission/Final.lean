import Mathlib
import Submission.Basic
import Submission.Main

open SimpleGraph Filter

namespace E74

universe u

/-- the slowly growing function -/
def ff (n : ℕ) : ℕ := Nat.findGreatest (fun k => Tseq k ≤ n) n

lemma Tseq_ff_le (n : ℕ) : Tseq (ff n) ≤ n :=
  Nat.findGreatest_spec (P := fun k => Tseq k ≤ n) (m := 0) (Nat.zero_le n)
    (by simp [Tseq_zero])

lemma ff_tendsto : Tendsto ff atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨max N (Tseq N), fun n hn => ?_⟩
  exact Nat.le_findGreatest (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)

/-- local copies of the definitions of the specification -/
def edgeDists {V : Type u} {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : (A.deleteEdges E).coe.Colorable 2)}

noncomputable def minDist {V : Type u} {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf (edgeDists A)

def subDists {V : Type u} (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (minDist A) | (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

noncomputable def maxDist {V : Type u} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup (subDists G n)

lemma edgeSet_finite {V : Type u} {G : SimpleGraph V} (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.Finite := by
  have hsub : A.edgeSet ⊆ (fun p : V × V => s(p.1, p.2)) '' (A.verts ×ˢ A.verts) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : A.Adj a b := he
      exact ⟨(a, b), ⟨A.edge_vert hab, A.edge_vert hab.symm⟩, rfl⟩
  exact ((hA.prod hA).image _).subset hsub

lemma edgeSet_mem_dists {V : Type u} {G : SimpleGraph V} (A : G.Subgraph) :
    A.edgeSet.ncard ∈ edgeDists A := by
  refine ⟨A.edgeSet, subset_rfl, ?_, rfl⟩
  refine ⟨Coloring.mk (fun _ => (0 : Fin 2)) ?_⟩
  intro v w h
  exfalso
  have h' : (A.deleteEdges A.edgeSet).Adj v w := h
  rw [Subgraph.deleteEdges_adj] at h'
  exact h'.2 (Subgraph.mem_edgeSet.2 h'.1)

lemma bdd_subDists {V : Type u} (G : SimpleGraph V) (n : ℕ) : BddAbove (subDists G n) := by
  refine ⟨n * n, ?_⟩
  rintro x ⟨A, hAn, hAfin, rfl⟩
  have hsub : A.edgeSet ⊆ (fun p : V × V => s(p.1, p.2)) '' (A.verts ×ˢ A.verts) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : A.Adj a b := he
      exact ⟨(a, b), ⟨A.edge_vert hab, A.edge_vert hab.symm⟩, rfl⟩
  have h1 : A.edgeSet.ncard ≤ n * n := calc
    A.edgeSet.ncard ≤ ((fun p : V × V => s(p.1, p.2)) '' (A.verts ×ˢ A.verts)).ncard :=
      Set.ncard_le_ncard hsub ((hAfin.prod hAfin).image _)
    _ ≤ (A.verts ×ˢ A.verts).ncard := Set.ncard_image_le (hAfin.prod hAfin)
    _ = n * n := by rw [Set.ncard_prod, hAn]
  have h2 : minDist A ≤ A.edgeSet.ncard := Nat.sInf_le (edgeSet_mem_dists A)
  exact h2.trans h1


/-- every finite subgraph `A` of `G` has `mono`-count at most `minDist A`. -/
theorem key {V : Type u} (G : SimpleGraph V) (hchi : ¬ G.Colorable 3)
    (hmax : ∀ n, maxDist G n ≤ ff n) : False := by
  classical
  have hex : ∃ G' : G.Subgraph, G'.verts.Finite ∧ ¬ G'.coe.Colorable 3 := by
    by_contra hcon
    push_neg at hcon
    exact hchi (SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
      (F := (⊤ : SimpleGraph (Fin 3))) (fun G' hfin => (hcon G' hfin).some))
  obtain ⟨G', hfin, hG'⟩ := hex
  haveI : Fintype G'.verts := hfin.fintype
  have hcol3 : Col3 G'.coe := by
    refine main_thm (mono G'.coe Finset.univ (fun _ => false)).ncard G'.verts G'.coe
      ⟨fun _ => false, le_rfl⟩ ?_
    intro S k hk
    let A : G.Subgraph := G'.induce (Subtype.val '' (S : Set G'.verts))
    have hAfin : A.verts.Finite := (S.finite_toSet).image _
    have hAcard : A.verts.ncard = S.card := by
      show (Subtype.val '' (S : Set G'.verts)).ncard = S.card
      rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    have h1 : minDist A ≤ ff S.card := by
      have hmem : minDist A ∈ subDists G S.card := ⟨A, hAcard, hAfin, rfl⟩
      exact le_trans (le_csSup (bdd_subDists G _) hmem) (hmax S.card)
    obtain ⟨E, hEsub, hEbip, hEcard⟩ := Nat.sInf_mem (⟨_, edgeSet_mem_dists A⟩ : (edgeDists A).Nonempty)
    obtain ⟨col⟩ := hEbip
    let c : G'.verts → Bool := fun x =>
      if hx : x.1 ∈ A.verts then decide (col ⟨x.1, hx⟩ = 0) else false
    have hsub : (Sym2.map (Subtype.val : G'.verts → V)) '' (mono G'.coe S c) ⊆ E := by
      rintro e ⟨e', ⟨x, y, rfl, hxS, hyS, hxy, hcxy⟩, rfl⟩
      by_contra hnot
      have hxA : x.1 ∈ A.verts := ⟨x, hxS, rfl⟩
      have hyA : y.1 ∈ A.verts := ⟨y, hyS, rfl⟩
      have hadj : (A.deleteEdges E).Adj x.1 y.1 := by
        rw [Subgraph.deleteEdges_adj]
        refine ⟨⟨hxA, hyA, hxy⟩, ?_⟩
        simpa using hnot
      have hne : col ⟨x.1, hxA⟩ ≠ col ⟨y.1, hyA⟩ := col.valid hadj
      simp only [c, dif_pos hxA, dif_pos hyA] at hcxy
      revert hne hcxy
      generalize col ⟨x.1, hxA⟩ = a
      generalize col ⟨y.1, hyA⟩ = b
      revert a b
      decide
    have hEfin : E.Finite := (edgeSet_finite A hAfin).subset hEsub
    have h2 : (mono G'.coe S c).ncard ≤ E.ncard := by
      calc (mono G'.coe S c).ncard
          = ((Sym2.map (Subtype.val : G'.verts → V)) '' (mono G'.coe S c)).ncard :=
            (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm
        _ ≤ E.ncard := Set.ncard_le_ncard hsub hEfin
    have h3 : k ≤ ff S.card := by
      have := hk c
      have h4 : E.ncard = minDist A := hEcard
      omega
    exact (Tseq_mono h3).trans (Tseq_ff_le _)
  obtain ⟨g, hg⟩ := hcol3
  exact hG' ⟨Coloring.mk g (fun {u v} h => hg u v h)⟩

end E74
