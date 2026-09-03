import Submission.GlobalCycleEar

/-! Direct endpoint obstructions. A whole-member ear can already be absorbed
by cycle-prefix repair, so its conditional length comparison is not a new
possible configuration in a maximum one-defect family. -/
namespace Erdos583CyclePrefixEndpointObstructionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583UnifiedMinimalDefectDevelopment Erdos583GlobalTailDefectDevelopment
open Erdos583TailPrefixRunFreshnessDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cycle_append_support_inter {V : Type*} {G : SimpleGraph V} {r s x : V}
    (A : G.Walk r s) (B : G.Walk s r) (hc : (A.append B).IsCycle)
    (hxA : x ∈ A.support) (hxB : x ∈ B.support) : x=r ∨ x=s := by
  cases A with
  | nil => exact Or.inl (by simpa using hxA)
  | @cons r a s h Q =>
    simp only [Walk.support_cons,List.mem_cons] at hxA
    rcases hxA with hx|hx
    · exact Or.inl hx
    · have hpath : (Q.append B).IsPath := (Walk.cons_isCycle_iff _ h).mp hc |>.1
      exact Or.inr (path_append_support_inter Q B hpath hx hxB)

lemma maximum_endpoint_meets_cycle_prefix {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (j : Fin k) (hij : L.index ≠ j)
    {s b : V} (A : G.Walk r s) (B : G.Walk s r) (hsr : s ≠ r)
    (hform : L.cycle=A.append B)
    (P : G.Walk s b) (hp : P.IsPath) (hP : (T.walk j).toSubgraph=P.toSubgraph) :
    ∃ x ∈ A.support, x ∈ P.support ∧ x ≠ s := by
  by_contra hn
  have hAP (x) (hxA : x ∈ A.support) (hxP : x ∈ P.support) : x=s := by
    by_contra hxs
    exact hn ⟨x,hxA,hxP,hxs⟩
  have hd : Disjoint ((A.append B).append L.tail).toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [←hform,←L.subgraph,←hP]
    exact T.disjoint hij
  have hc := CyclePrefixRepair.cycle_prefix_exchange A B L.tail P (hform ▸ L.isCycle)
    hsr L.isPath hp (fun x hx ht ↦ L.inter x (hform.symm ▸ hx) ht) hAP hd
  apply ShortLollipop.maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  simpa only [←hform,←L.subgraph,←hP] using hc

lemma maximum_root_avoiding_endpoint_two_sides {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (j : Fin k) (hij : L.index ≠ j)
    {s b : V} (A : G.Walk r s) (B : G.Walk s r) (hform : L.cycle=A.append B)
    (P : G.Walk s b) (hp : P.IsPath) (hP : (T.walk j).toSubgraph=P.toSubgraph)
    (hav : r ∉ P.support) :
    ∃ x ∈ A.support, ∃ y ∈ B.support,
      x ∈ P.support ∧ y ∈ P.support ∧ x ≠ s ∧ y ≠ s ∧ x ≠ y := by
  have hsr : s ≠ r := fun he ↦ hav (he ▸ P.start_mem_support)
  obtain ⟨x,hxA,hxP,hxs⟩ := maximum_endpoint_meets_cycle_prefix T hs hm r L j hij
    A B hsr hform P hp hP
  let M : RootedCycleRep T r :=
    ⟨L.index,L.finish,L.start_eq,L.finish_eq,L.cycle.reverse,L.tail,L.isCycle.reverse,L.isPath,
      by intro z hz ht; exact L.inter z (by simpa using hz) ht,
      by simpa only [Walk.toSubgraph_append,Walk.toSubgraph_reverse] using L.subgraph⟩
  obtain ⟨y,hyB,hyP,hys⟩ := maximum_endpoint_meets_cycle_prefix T hs hm r M j hij
    B.reverse A.reverse hsr (by simp only [M,hform,Walk.reverse_append]) P hp hP
  have hyB' : y ∈ B.support := by simpa using hyB
  refine ⟨x,hxA,y,hyB',hxP,hyP,hxs,hys,?_⟩
  intro hxy
  rcases cycle_append_support_inter A B (hform ▸ L.isCycle) hxA (hxy.symm ▸ hyB') with hx|hx
  · exact hav (hx ▸ hxP)
  · exact hxs hx

lemma maximum_no_whole_cycle_ear {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (j : Fin k) (hij : L.index ≠ j)
    {s t : V} (A : G.Walk r s) (B : G.Walk s t) (E : G.Walk t r)
    (hrs : r ≠ s) (hst : s ≠ t) (htr : t ≠ r)
    (hform : L.cycle=(A.append B).append E)
    (P : G.Walk s t) (hp : P.IsPath) (hP : (T.walk j).toSubgraph=P.toSubgraph)
    (hinter : ∀ x ∈ P.support, x ∈ L.cycle.support → x=s ∨ x=t) : False := by
  obtain ⟨x,hxA,hxP,hxs⟩ := maximum_endpoint_meets_cycle_prefix T hs hm r L j hij
    A (B.append E) hrs.symm (by simpa only [Walk.append_assoc] using hform) P hp hP
  have hxC : x ∈ L.cycle.support := by
    rw [hform,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
    exact Or.inl (Or.inl hxA)
  have hxt := (hinter x hxP hxC).resolve_left hxs
  have hAB := (hform ▸ L.isCycle).isPath_of_append_left (Walk.not_nil_of_ne htr)
  have hh := path_append_support_inter A B hAB hxA (hxt ▸ B.end_mem_support)
  exact hst (hh.symm.trans hxt)

lemma maximum_no_one_touch_cycle_endpoint {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (j : Fin k) (hij : L.index ≠ j)
    {s b : V} (P : G.Walk s b) (hp : P.IsPath) (hP : (T.walk j).toSubgraph=P.toSubgraph)
    (hsC : s ∈ L.cycle.support)
    (hinter : ∀ x ∈ L.cycle.support, x ∈ P.support → x=s) : False := by
  by_cases hsr : s=r
  · subst s
    cases hC : L.cycle with
    | nil => exact L.isCycle.ne_nil hC
    | @cons r v r h Q =>
      have hv := Erdos583LollipopEndpointRotationDevelopment.maximum_lollipop_shared_start_neighbor_present
        T hm r L j hij h Q hC P hp hP
      have hvC : v ∈ L.cycle.support := by rw [hC]; exact List.mem_cons_of_mem _ Q.start_mem_support
      exact h.ne (hinter v hvC hv).symm
  · obtain ⟨A,B,hform⟩ := L.cycle.mem_support_iff_exists_append.mp hsC
    obtain ⟨x,hxA,hxP,hxs⟩ := maximum_endpoint_meets_cycle_prefix T hs hm r L j hij
      A B hsr hform P hp hP
    exact hxs (hinter x (by rw [hform,Walk.mem_support_append_iff]; exact Or.inl hxA) hxP)

end Erdos583CyclePrefixEndpointObstructionDevelopment
