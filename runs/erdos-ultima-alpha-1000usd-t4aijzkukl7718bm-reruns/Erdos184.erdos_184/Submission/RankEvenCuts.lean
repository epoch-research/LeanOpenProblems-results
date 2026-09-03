import Submission.RankBlocks
import Submission.ParityCompletion

/-!
Even-cut parity sharpens the edge-connectivity requirement on rank-critical
graphs. No exclusion of all rank-critical graphs is established here.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace RankEvenCuts
open RankCritical RankCriticalCuts RankCriticalPartitions
variable {V : Type*} [Fintype V]

/-- The incidence sum on one side of a two-color cut detects its crossing
edges modulo two. -/
lemma cut_incidence_sum (G : SimpleGraph V) (f : V → Bool) (e : Sym2 V) :
    (∑ x ∈ Finset.univ.filter (fun x => f x = true), G.incMatrix (ZMod 2) x e) =
      if e ∈ G.edgeSet \ (monochromatic G f).edgeSet then 1 else 0 := by
  induction e using Sym2.ind with
  | h u v =>
    by_cases h : G.Adj u v
    · have hc := ParityCompletion.column_eq_boundary G h
      have hf : (∑ x ∈ Finset.univ.filter (fun x => f x = true),
          G.incMatrix (ZMod 2) x s(u,v)) =
          (if f u = true then 1 else 0) + (if f v = true then 1 else 0) := by
        simp_rw [congrFun hc]
        simp [ParityCompletion.boundary,Finset.sum_add_distrib]
      rw [hf]
      cases hu : f u <;> cases hv : f v <;>
        simp [monochromatic,h,hu,hv,CharTwo.add_self_eq_zero]
    · have hz : ∀ x, G.incMatrix (ZMod 2) x s(u,v) = 0 := by
        intro x
        apply incMatrix_of_notMem_incidenceSet
        intro he
        exact h he.1
      simp [hz,h]

lemma even_two_color_cut (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (f : V → Bool) : Even ((G.edgeSet \ (monochromatic G f).edgeSet).ncard) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hsum : (∑ e : Sym2 V,
      if e ∈ G.edgeSet \ (monochromatic G f).edgeSet then (1 : ZMod 2) else 0) =
      ((G.edgeSet \ (monochromatic G f).edgeSet).ncard : ZMod 2) := by
    rw [Finset.sum_boole]
    congr 1
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext e
    simp
  rw [← hsum]
  simp_rw [← cut_incidence_sum G f]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v _
  rw [sum_incMatrix_apply G]
  exact ZMod.natCast_eq_zero_iff_even.mpr (he v)

lemma two_color_cut_lower {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (f : V → Bool) (hne : monochromatic G f ≠ G) :
    2*C+2 ≤ (G.edgeSet \ (monochromatic G f).edgeSet).ncard := by
  have hlo := closed_cut_lower hG (monochromatic G f) (monochromatic_le G f)
    (monochromatic_closed G f) hne
  obtain ⟨r,hr⟩ := even_two_color_cut G hG.1 f
  omega

/-- Odd-sized deletions gain one edge of slack because an even graph has
no odd edge cut. -/
lemma small_edge_deletion_reachable {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (F : Set (Sym2 V)) (hF : F.ncard ≤ 2*C+1) (u v : V) (huv : G.Reachable u v) :
    (G.deleteEdges F).Reachable u v := by
  by_contra hn
  let R := G.deleteEdges F
  let f : V → Bool := fun x => decide (R.Reachable u x)
  have hne : monochromatic G f ≠ G := by
    intro heq
    have hcol := color_eq_of_reachable G f (heq.symm ▸ huv)
    have hself : R.Reachable u u := Reachable.refl _
    change ¬ R.Reachable u v at hn
    simp only [f,hself,hn,decide_true,decide_false] at hcol
    cases hcol
  have hlo := two_color_cut_lower hG f hne
  have hs : G.edgeSet \ (monochromatic G f).edgeSet ⊆ F := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      by_contra hf
      have hxy : R.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨he.1,hf⟩
      have hh : R.Reachable u x ↔ R.Reachable u y :=
        ⟨fun h => h.trans hxy.reachable,fun h => h.trans hxy.symm.reachable⟩
      apply he.2
      refine ⟨he.1,?_⟩
      change decide (R.Reachable u x) = decide (R.Reachable u y)
      simp only [hh]
  have hle := Set.ncard_le_ncard hs
  omega

lemma edge_reachable_lower {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (u v : V) (huv : G.Reachable u v) : G.IsEdgeReachable (2*C+2) u v := by
  intro F hF
  apply small_edge_deletion_reachable hG F ?_ u v huv
  have hh : F.ncard < 2*C+2 := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card'] at hF
    exact_mod_cast hF
  omega

end RankEvenCuts
end Erdos184
