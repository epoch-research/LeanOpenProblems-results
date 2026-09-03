import Submission.RegularRootedCut

/-! Defect accounting for regular rooted cuts. A single possible cycle tail
leaves total path deficit at most one. -/
namespace Erdos583RegularCutDefectsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583RegularRootedCutDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

noncomputable def walkDefect {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : ℕ := p.length+1-p.toSubgraph.verts.ncard

lemma walkDefect_add_vertices {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : walkDefect p+p.toSubgraph.verts.ncard=p.length+1 :=
  Nat.sub_add_cancel (walk_vertex_ncard_le p)

lemma walkDefect_zero_iff {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : walkDefect p=0 ↔ p.IsPath := by
  rw [←walk_vertex_ncard_eq_iff]
  have hh := walkDefect_add_vertices p
  omega

lemma regularTail_defect_le_one {V : Type*} {G : SimpleGraph V} {a r : V}
    (p : G.Walk a r) (hp : RegularTail p) : walkDefect p ≤ 1 := by
  rcases hp with hp|⟨_,hp⟩
  · rw [(walkDefect_zero_iff p).mpr hp]; omega
  · have hh := walkDefect_add_vertices p
    omega

lemma regularCut_member_defect {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (i : Fin k) (hi : i ∈ A) :
    T.defect i=walkDefect (R.tail ⟨(i,true),hi⟩)+walkDefect (R.tail ⟨(i,false),hi⟩) := by
  let L := R.tail ⟨(i,true),hi⟩
  let B := R.tail ⟨(i,false),hi⟩
  have hiLB : (⟨(i,true),hi⟩ : {s : Fin k × Bool // s.1 ∈ A}) ≠ ⟨(i,false),hi⟩ := by
    intro hh
    have := congrArg (fun s ↦ s.val.2) hh
    contradiction
  have hd : Disjoint L.toSubgraph.edgeSet B.toSubgraph.edgeSet := R.disjoint hiLB
  have hl : (T.walk i).length=L.length+B.length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail i),R.decomp i hi,Subgraph.edgeSet_sup,
      Set.ncard_union_eq hd,trail_edgeSet_ncard _ (R.trail _),trail_edgeSet_ncard _ (R.trail _)]
  have hint : L.toSubgraph.verts ∩ B.toSubgraph.verts={r} := by
    apply Set.Subset.antisymm (hR.2.1 i hi)
    apply Set.singleton_subset_iff.mpr
    exact ⟨L.mem_verts_toSubgraph.mpr L.end_mem_support,
      B.mem_verts_toSubgraph.mpr B.end_mem_support⟩
  have hv := Set.ncard_union_add_ncard_inter L.toSubgraph.verts B.toSubgraph.verts
  rw [hint,Set.ncard_singleton] at hv
  have hv' : (T.walk i).toSubgraph.verts.ncard+1=
      L.toSubgraph.verts.ncard+B.toSubgraph.verts.ncard := by
    rw [R.decomp i hi,Subgraph.verts_sup]
    exact hv
  have hT := T.defect_add_vertices i
  have hL := walkDefect_add_vertices L
  have hB := walkDefect_add_vertices B
  change T.defect i=walkDefect L+walkDefect B
  omega

lemma regularCut_all_paths {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (hp : ∀ s, (R.tail s).IsPath) : ∀ i, (T.walk i).IsPath := by
  intro i
  by_cases hi : i ∈ A
  · apply (T.defect_eq_zero_iff i).mp
    rw [regularCut_member_defect R hR i hi,(walkDefect_zero_iff _).mpr (hp _),
      (walkDefect_zero_iff _).mpr (hp _)]
  · exact hR.2.2 i hi

lemma regularCut_one_petal_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (ρ : {s : Fin k × Bool // s.1 ∈ A})
    (hp : ∀ s, s ≠ ρ → (R.tail s).IsPath) :
    G.edgeSet.ncard+k ≤ T.score+1 := by
  classical
  have ht (s : {s : Fin k × Bool // s.1 ∈ A}) :
      walkDefect (R.tail s) ≤ if s=ρ then 1 else 0 := by
    by_cases hs : s=ρ
    · rw [if_pos hs]
      exact regularTail_defect_le_one _ (hR.1 s)
    · rw [if_neg hs,(walkDefect_zero_iff _).mpr (hp s hs)]
  have hi (i : Fin k) : T.defect i ≤ if i=ρ.val.1 then 1 else 0 := by
    by_cases hiA : i ∈ A
    · rw [regularCut_member_defect R hR i hiA]
      have h1 := ht ⟨(i,true),hiA⟩
      have h2 := ht ⟨(i,false),hiA⟩
      by_cases hir : i=ρ.val.1
      · rw [if_pos hir]
        have hne : (⟨(i,true),hiA⟩ : {s : Fin k × Bool // s.1 ∈ A}) ≠ ⟨(i,false),hiA⟩ := by
          intro hh
          have := congrArg (fun s ↦ s.val.2) hh
          contradiction
        split_ifs at h1 h2 with h1' h2' <;> try omega
        exact (hne (h1'.trans h2'.symm)).elim
      · have hn1 : (⟨(i,true),hiA⟩ : {s : Fin k × Bool // s.1 ∈ A}) ≠ ρ :=
          fun hh ↦ hir (congrArg (fun s ↦ s.val.1) hh)
        have hn2 : (⟨(i,false),hiA⟩ : {s : Fin k × Bool // s.1 ∈ A}) ≠ ρ :=
          fun hh ↦ hir (congrArg (fun s ↦ s.val.1) hh)
        rw [if_neg hn1] at h1
        rw [if_neg hn2] at h2
        rw [if_neg hir]
        omega
    · rw [(T.defect_eq_zero_iff i).mpr (hR.2.2 i hiA)]
      exact Nat.zero_le _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
  have hs' : ∑ i, T.defect i ≤ 1 := by simpa using hs
  have hh := T.sum_defect_add_score
  omega

end Erdos583RegularCutDefectsDevelopment
