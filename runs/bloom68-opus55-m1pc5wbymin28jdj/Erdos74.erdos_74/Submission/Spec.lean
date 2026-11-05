import FormalConjecturesUtil
import Submission.Compact
import Submission.Cover

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def SimpleGraph.edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe)}

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def SimpleGraph.minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| SimpleGraph.edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
induced subgraphs `A` of `G` on `n` vertices.
-/
def SimpleGraph.subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (SimpleGraph.minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges.

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs. This means there exists at least one $n$-vertex
subgraph that requires exactly this many edge deletions.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| SimpleGraph.subgraphEdgeDistsToBipartite G n

/--
Let $f(n)\to \infty$ possibly very slowly.
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?
-/
theorem erdos_74 : ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) := by
  sorry

-- TODO(firsching): add the remaining statements/comments

end Erdos74


namespace Erdos74Glue

open Erdos74Aux

variable {W : Type*}

/-- Thresholds for the slowly growing function. -/
def M (j : ℕ) : ℕ := (ell (j + 1) + 1) ^ (j + 1)

lemma le_M (n : ℕ) : n ≤ M n := by
  unfold M
  have h1 : n + 1 ≤ ell (n + 1) + 1 := by have := le_ell (n + 1); omega
  calc n ≤ n + 1 := Nat.le_succ n
    _ ≤ 2 ^ (n + 1) := (Nat.lt_two_pow_self).le
    _ ≤ (ell (n + 1) + 1) ^ (n + 1) := by
        apply Nat.pow_le_pow_left
        have := ell_pos (n + 1); omega

lemma M_mono : Monotone M := by
  apply monotone_nat_of_le_succ
  intro j
  unfold M
  have h1 : ell (j + 1) ≤ ell (j + 1 + 1) := ell_mono (Nat.le_succ _)
  calc (ell (j + 1) + 1) ^ (j + 1) ≤ (ell (j + 1 + 1) + 1) ^ (j + 1) :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ (ell (j + 1 + 1) + 1) ^ (j + 1 + 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_succ _)

lemma exists_le_M (n : ℕ) : ∃ j, n ≤ M j := ⟨n, le_M n⟩

/-- The slowly growing function witnessing the disproof. -/
noncomputable def fSlow (n : ℕ) : ℕ := Nat.find (exists_le_M n)

lemma fSlow_le {n j : ℕ} (h : n ≤ M j) : fSlow n ≤ j := Nat.find_min' _ h

lemma fSlow_tendsto : Tendsto fSlow atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro J
  refine ⟨M J + 1, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 : n ≤ M (fSlow n) := Nat.find_spec (exists_le_M n)
  have h2 := M_mono hlt.le
  omega

lemma bip_deleteAll {G : SimpleGraph W} (A : G.Subgraph) :
    IsBipartite (A.deleteEdges A.edgeSet).coe := by
  refine ⟨Coloring.mk (fun _ => 0) (fun {a b} hab => ?_)⟩
  exfalso
  rw [Subgraph.coe_adj, Subgraph.deleteEdges_adj] at hab
  exact hab.2 (Subgraph.mem_edgeSet.mpr hab.1)

lemma mem_edgeDists {G : SimpleGraph W} (A : G.Subgraph) :
    A.edgeSet.ncard ∈ Erdos74.SimpleGraph.edgeDistancesToBipartite A :=
  ⟨A.edgeSet, subset_rfl, bip_deleteAll A, rfl⟩

lemma minEdgeDist_le_sq {G : SimpleGraph W} (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.verts.ncard * A.verts.ncard := by
  have hsub : A.edgeSet ⊆ (fun p : W × W => s(p.1, p.2)) '' (A.verts ×ˢ A.verts) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [Subgraph.mem_edgeSet] at he
      exact ⟨(a, b), ⟨A.edge_vert he, A.edge_vert he.symm⟩, rfl⟩
  have hfin : (A.verts ×ˢ A.verts).Finite := hA.prod hA
  calc Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.edgeSet.ncard :=
        Nat.sInf_le (mem_edgeDists A)
    _ ≤ ((fun p : W × W => s(p.1, p.2)) '' (A.verts ×ˢ A.verts)).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (A.verts ×ˢ A.verts).ncard := Set.ncard_image_le hfin
    _ = A.verts.ncard * A.verts.ncard := Set.ncard_prod

lemma minEdgeDist_le_max {G : SimpleGraph W} (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤
      Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G A.verts.ncard := by
  apply le_csSup
  · refine ⟨A.verts.ncard * A.verts.ncard, ?_⟩
    rintro _ ⟨A', hA'n, hA'fin, rfl⟩
    have := minEdgeDist_le_sq A' hA'fin
    rw [hA'n] at this
    exact this
  · exact ⟨A, rfl, hA, rfl⟩

lemma lt_minEdgeDist {G : SimpleGraph W} (A : G.Subgraph) (j : ℕ)
    (h : ∀ E : Set (Sym2 W), E ⊆ A.edgeSet → (A.deleteEdges E).coe.Colorable 2 → j < E.ncard) :
    j < Erdos74.SimpleGraph.minEdgeDistToBipartite A := by
  have hne : (Erdos74.SimpleGraph.edgeDistancesToBipartite A).Nonempty := ⟨_, mem_edgeDists A⟩
  obtain ⟨E, hE, hbip, hEq⟩ := Nat.sInf_mem hne
  unfold Erdos74.SimpleGraph.minEdgeDistToBipartite
  rw [← hEq]
  exact h E hE hbip

/-- Main structural consequence: a graph whose subgraph profile is bounded by `fSlow`
is `3`-colorable. -/
theorem colorable_of_profile (G : SimpleGraph W)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ fSlow n) :
    G.Colorable 3 := by
  apply colorable_of_hits G
  intro j
  rcases cover_or_obstruction G (ell (j + 1)) j with hF | ⟨A, hAfin, hAcard, hA⟩
  · exact hF
  · exfalso
    have h1 := lt_minEdgeDist A j hA
    have h2 := minEdgeDist_le_max A hAfin
    have h3 := hG A.verts.ncard
    have h4 : fSlow A.verts.ncard ≤ j := fSlow_le hAcard
    omega

end Erdos74Glue

theorem Erdos74.erdos_74.disproof : ¬ (type_of% @Erdos74.erdos_74) := by
  intro h
  obtain ⟨V, G, hχ, hG⟩ := h Erdos74Glue.fSlow Erdos74Glue.fSlow_tendsto
  have hcol : G.Colorable 3 := Erdos74Glue.colorable_of_profile G hG
  have hle : G.chromaticNumber ≤ 3 := hcol.chromaticNumber_le
  rw [hχ] at hle
  exact absurd hle (by decide)
