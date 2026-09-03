import Submission.EndpointPathMaximality
import Submission.RigidSwitching

/-! Absorbing a cycle into two paths which meet it only at their four distinct
endpoints. Intersections of the old paths away from the cycle are unrestricted.
This does not prove arbitrary-degree all-odd path decomposition. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.Absorption
open RigidSwitching
set_option maxHeartbeats 600000
variable {V : Type*} {G : SimpleGraph V} {a b c d z : V}

lemma append_path_clean (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (h : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b)
    (ha : a ∉ q.support) : (p.append q).IsPath := by
  apply append_isPath_of_support_inter hp hq
  intro x hx hy
  exact (h x hx hy).resolve_left (fun he => ha (he ▸ hy))

lemma extend_both_ends (p : G.Walk a b) (r : G.Walk c a) (s : G.Walk b d)
    (hp : p.IsPath) (hr : r.IsPath) (hs : s.IsPath)
    (hrp : ∀ x, x ∈ r.support → x ∈ p.support → x = a)
    (hps : ∀ x, x ∈ p.support → x ∈ s.support → x = b)
    (hrs : r.support.Disjoint s.support) : ((r.append p).append s).IsPath := by
  apply append_isPath_of_support_inter (append_isPath_of_support_inter hr hp hrp) hs
  intro x hx hy
  rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
  · exact (hrs hx hy).elim
  · exact hps x hx hy

lemma take_support_comparable (p : G.Walk a b) (hc : c ∈ p.support) (hd : d ∈ p.support) :
    c ∈ (p.takeUntil d hd).support ∨ d ∈ (p.takeUntil c hc).support := by
  rcases le_total (p.takeUntil c hc).length (p.takeUntil d hd).length with h | h
  · left
    have he : (p.takeUntil d hd).getVert (p.takeUntil c hc).length = c :=
      (p.getVert_takeUntil hd h).trans (p.getVert_length_takeUntil hc)
    exact he ▸ (p.takeUntil d hd).getVert_mem_support _
  · right
    have he : (p.takeUntil c hc).getVert (p.takeUntil d hd).length = d :=
      (p.getVert_takeUntil hc h).trans (p.getVert_length_takeUntil hd)
    exact he ▸ (p.takeUntil c hc).getVert_mem_support _

lemma split_support_inter (p : G.Walk a b) (hp : p.IsPath) (hc : c ∈ p.support)
    (x : V) (hx : x ∈ (p.takeUntil c hc).support) (hy : x ∈ (p.dropUntil c hc).support) :
    x = c := by
  by_contra h
  have hh : ((p.takeUntil c hc).append (p.dropUntil c hc)).IsPath := by
    simpa only [Walk.take_spec] using hp
  exact hh.ne_of_mem_support_of_append h hx hy rfl

lemma cyclePaths_edge_perm (R : G.Walk a a) (hR : R.IsCycle) (S : CyclePaths R b) :
    (S.left.edges ++ S.right.edges).Perm R.edges := by
  apply (List.perm_ext_iff_of_nodup
    (S.left_path.isTrail.edges_nodup.append S.right_path.isTrail.edges_nodup S.edges_disjoint)
    hR.isTrail.edges_nodup).mpr
  intro e
  simpa only [List.mem_append] using S.edges_cover e

/-- The alternating cyclic order. -/
lemma clean_alternating
    (p : G.Walk a b) (q : G.Walk c d) (R : G.Walk a a)
    (hp : p.IsPath) (hq : q.IsPath) (hR : R.IsCycle) (S : CyclePaths R b)
    (hcL : c ∈ S.left.support) (hdR : d ∈ S.right.support)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hpc : ∀ x, x ∈ p.support → x ∈ R.support → x = a ∨ x = b)
    (hqc : ∀ x, x ∈ q.support → x ∈ R.support → x = c ∨ x = d) :
    ∃ (r : G.Walk c d) (s : G.Walk a b), r.IsPath ∧ s.IsPath ∧
      (r.edges ++ s.edges).Perm (p.edges ++ q.edges ++ R.edges) := by
  let A := S.left.takeUntil c hcL
  let B := S.left.dropUntil c hcL
  let C := S.right.takeUntil d hdR
  let D := S.right.dropUntil d hdR
  have hA := S.left_path.takeUntil hcL
  have hB := S.left_path.dropUntil hcL
  have hC := S.right_path.takeUntil hdR
  have hD := S.right_path.dropUntil hdR
  have hAL : A.support ⊆ S.left.support := S.left.support_takeUntil_subset hcL
  have hBL : B.support ⊆ S.left.support := S.left.support_dropUntil_subset hcL
  have hCR : C.support ⊆ S.right.support := S.right.support_takeUntil_subset hdR
  have hDR : D.support ⊆ S.right.support := S.right.support_dropUntil_subset hdR
  have hbA : b ∉ A.support := Walk.endpoint_notMem_support_takeUntil S.left_path hcL hbc
  have hbC : b ∉ C.support := Walk.endpoint_notMem_support_takeUntil S.right_path hdR hbd
  have haB : a ∉ B.support := by
    intro h
    exact hac (split_support_inter S.left S.left_path hcL a
      (S.left.takeUntil c hcL).start_mem_support h)
  have haD : a ∉ D.support := by
    intro h
    exact had (split_support_inter S.right S.right_path hdR a
      (S.right.takeUntil d hdR).start_mem_support h)
  have hcR : c ∉ S.right.support := by
    intro h
    exact (S.support_inter c hcL h).elim (fun h => hac h.symm) (fun h => hbc h.symm)
  have hdL : d ∉ S.left.support := by
    intro h
    exact (S.support_inter d h hdR).elim (fun h => had h.symm) (fun h => hbd h.symm)
  let r := (A.reverse.append p).append D.reverse
  let s := (C.append q.reverse).append B
  have hr : r.IsPath := by
    apply extend_both_ends p A.reverse D.reverse hp hA.reverse hD.reverse
    · intro x hx hy
      have hxA : x ∈ A.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
      exact (hpc x hy (S.left_support_subset (hAL hxA))).resolve_right (fun h => hbA (h ▸ hxA))
    · intro x hx hy
      have hyD : x ∈ D.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hy
      exact (hpc x hx (S.right_support_subset (hDR hyD))).resolve_left (fun h => haD (h ▸ hyD))
    · intro x hx hy
      have hxA : x ∈ A.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
      have hyD : x ∈ D.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hy
      exact (S.support_inter x (hAL hxA) (hDR hyD)).elim
        (fun h => haD (h ▸ hyD)) (fun h => hbA (h ▸ hxA))
  have hs : s.IsPath := by
    apply extend_both_ends q.reverse C B hq.reverse hC hB
    · intro x hx hy
      have hyp : x ∈ q.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hy
      exact (hqc x hyp (S.right_support_subset (hCR hx))).resolve_left (fun h => hcR (h ▸ hCR hx))
    · intro x hx hy
      have hxp : x ∈ q.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
      exact (hqc x hxp (S.left_support_subset (hBL hy))).resolve_right (fun h => hdL (h ▸ hBL hy))
    · intro x hx hy
      exact (S.support_inter x (hBL hy) (hCR hx)).elim
        (fun h => haB (h ▸ hy)) (fun h => hbC (h ▸ hx))
  refine ⟨r,s,hr,hs,?_⟩
  have heL : A.edges ++ B.edges = S.left.edges := by
    simpa only [A,B,Walk.edges_append] using congrArg Walk.edges (S.left.take_spec hcL)
  have heR : C.edges ++ D.edges = S.right.edges := by
    simpa only [C,D,Walk.edges_append] using congrArg Walk.edges (S.right.take_spec hdR)
  apply List.perm_iff_count.mpr
  intro e
  have h₁ := congrArg (List.count e) heL
  have h₂ := congrArg (List.count e) heR
  have h₃ := List.Perm.count_eq (cyclePaths_edge_perm R hR S) e
  simp only [r,s,Walk.edges_append,Walk.edges_reverse,List.count_append,List.count_reverse] at h₁ h₂ h₃ ⊢
  omega

/-- The two endpoints of `q` occur on the same rim arc, in the specified order. -/
lemma clean_same_arc_ordered
    (p : G.Walk a b) (q : G.Walk c d) (R : G.Walk a a)
    (hp : p.IsPath) (hq : q.IsPath) (hR : R.IsCycle) (S : CyclePaths R b)
    (hcL : c ∈ S.left.support) (hdL : d ∈ S.left.support)
    (horder : c ∈ (S.left.takeUntil d hdL).support)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hpc : ∀ x, x ∈ p.support → x ∈ R.support → x = a ∨ x = b)
    (hqc : ∀ x, x ∈ q.support → x ∈ R.support → x = c ∨ x = d) :
    ∃ (r : G.Walk b d) (s : G.Walk c a), r.IsPath ∧ s.IsPath ∧
      (r.edges ++ s.edges).Perm (p.edges ++ q.edges ++ R.edges) := by
  let A := S.left.takeUntil d hdL
  let B := S.left.dropUntil d hdL
  have hA := S.left_path.takeUntil hdL
  have hB := S.left_path.dropUntil hdL
  have hAL : A.support ⊆ S.left.support := S.left.support_takeUntil_subset hdL
  have hBL : B.support ⊆ S.left.support := S.left.support_dropUntil_subset hdL
  have hbA : b ∉ A.support := Walk.endpoint_notMem_support_takeUntil S.left_path hdL hbd
  have haB : a ∉ B.support := by
    intro h
    exact had (split_support_inter S.left S.left_path hdL a
      (S.left.takeUntil d hdL).start_mem_support h)
  have hcB : c ∉ B.support := by
    intro h
    exact hcd (split_support_inter S.left S.left_path hdL c horder h)
  have hcR : c ∉ S.right.support := by
    intro h
    exact (S.support_inter c hcL h).elim (fun h => hac h.symm) (fun h => hbc h.symm)
  let Q := B.append S.right.reverse
  have hQ : Q.IsPath := by
    apply append_isPath_of_support_inter hB S.right_path.reverse
    intro x hx hy
    have hyR : x ∈ S.right.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hy
    exact (S.support_inter x (hBL hx) hyR).resolve_left (fun h => haB (h ▸ hx))
  have hQR : Q.support ⊆ R.support := by
    intro x hx
    rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
    · exact S.left_support_subset (hBL hx)
    · exact S.right_support_subset (by simpa only [Walk.support_reverse,List.mem_reverse] using hx)
  have hcQ : c ∉ Q.support := by
    intro h
    rcases (Walk.mem_support_append_iff _ _).mp h with h | h
    · exact hcB h
    · exact hcR (by simpa only [Walk.support_reverse,List.mem_reverse] using h)
  let r := p.reverse.append A
  let s := q.append Q
  have hr : r.IsPath := by
    apply append_path_clean p.reverse A hp.reverse hA _ hbA
    intro x hx hy
    have hxp : x ∈ p.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
    exact (hpc x hxp (S.left_support_subset (hAL hy))).symm
  have hs : s.IsPath := append_path_clean q Q hq hQ
    (fun x hx hy => hqc x hx (hQR hy)) hcQ
  refine ⟨r,s,hr,hs,?_⟩
  have heL : A.edges ++ B.edges = S.left.edges := by
    simpa only [A,B,Walk.edges_append] using congrArg Walk.edges (S.left.take_spec hdL)
  apply List.perm_iff_count.mpr
  intro e
  have h₁ := congrArg (List.count e) heL
  have h₂ := List.Perm.count_eq (cyclePaths_edge_perm R hR S) e
  simp only [r,s,Q,Walk.edges_append,Walk.edges_reverse,List.count_append,List.count_reverse] at h₁ h₂ ⊢
  omega

/-- Two paths with four distinct endpoints on a cycle absorb that cycle if
they have no internal vertices on it. They may intersect arbitrarily elsewhere. -/
lemma absorb_clean_cycle_ended (p q : Piece G) (R : G.Walk z z) (hR : R.IsCycle)
    (hps : p.src ∈ R.support) (hpt : p.dst ∈ R.support)
    (hqs : q.src ∈ R.support) (hqt : q.dst ∈ R.support)
    (hsep : p.src ≠ q.src ∧ p.src ≠ q.dst ∧ p.dst ≠ q.src ∧ p.dst ≠ q.dst)
    (hpc : ∀ x, x ∈ p.walk.support → x ∈ R.support → x = p.src ∨ x = p.dst)
    (hqc : ∀ x, x ∈ q.walk.support → x ∈ R.support → x = q.src ∨ x = q.dst) :
    ∃ r s : Piece G,
      (r.walk.edges ++ s.walk.edges).Perm (p.walk.edges ++ q.walk.edges ++ R.edges) ∧
      [r.src,r.dst,s.src,s.dst].Perm [p.src,p.dst,q.src,q.dst] := by
  let T := R.rotate hps
  have hT : T.IsCycle := hR.rotate hps
  have hptT : p.dst ∈ T.support := (R.mem_support_rotate_iff hps).mpr hpt
  have hqsT : q.src ∈ T.support := (R.mem_support_rotate_iff hps).mpr hqs
  have hqtT : q.dst ∈ T.support := (R.mem_support_rotate_iff hps).mpr hqt
  have hpT : ∀ x, x ∈ p.walk.support → x ∈ T.support → x = p.src ∨ x = p.dst := by
    intro x hx hy
    exact hpc x hx ((R.mem_support_rotate_iff hps).mp hy)
  have hqT : ∀ x, x ∈ q.walk.support → x ∈ T.support → x = q.src ∨ x = q.dst := by
    intro x hx hy
    exact hqc x hx ((R.mem_support_rotate_iff hps).mp hy)
  suffices H : ∃ r s : Piece G,
      (r.walk.edges ++ s.walk.edges).Perm (p.walk.edges ++ q.walk.edges ++ T.edges) ∧
      [r.src,r.dst,s.src,s.dst].Perm [p.src,p.dst,q.src,q.dst] by
    obtain ⟨r,s,he,hv⟩ := H
    exact ⟨r,s,he.trans ((R.rotate_edges hps).perm.append_left (p.walk.edges ++ q.walk.edges)),hv⟩
  obtain ⟨S⟩ := exists_cyclePaths T hT hptT p.ne
  obtain ⟨S,hcL⟩ := S.exists_left_through hqsT
  by_cases hdR : q.dst ∈ S.right.support
  · obtain ⟨r,s,hr,hs,he⟩ := clean_alternating p.walk q.walk T p.isPath q.isPath hT S
      hcL hdR hsep.1 hsep.2.1 hsep.2.2.1 hsep.2.2.2 hpT hqT
    refine ⟨⟨q.src,q.dst,r,hr,q.ne⟩,⟨p.src,p.dst,s,hs,p.ne⟩,he,?_⟩
    apply List.perm_iff_count.mpr
    intro v
    simp only [List.count_cons,List.count_nil]
    omega
  · have hdL : q.dst ∈ S.left.support := ((S.support_cover q.dst).mpr hqtT).resolve_right hdR
    rcases take_support_comparable S.left hcL hdL with hord | hord
    · obtain ⟨r,s,hr,hs,he⟩ := clean_same_arc_ordered p.walk q.walk T p.isPath q.isPath hT S
        hcL hdL hord hsep.1 hsep.2.1 hsep.2.2.1 hsep.2.2.2 q.ne hpT hqT
      refine ⟨⟨p.dst,q.dst,r,hr,hsep.2.2.2⟩,⟨q.src,p.src,s,hs,hsep.1.symm⟩,he,?_⟩
      apply List.perm_iff_count.mpr
      intro v
      simp only [List.count_cons,List.count_nil]
      omega
    · have hqr : ∀ x, x ∈ q.walk.reverse.support → x ∈ T.support → x = q.dst ∨ x = q.src := by
        intro x hx hy
        exact (hqT x (by simpa only [Walk.support_reverse,List.mem_reverse] using hx) hy).symm
      obtain ⟨r,s,hr,hs,he⟩ := clean_same_arc_ordered p.walk q.walk.reverse T
        p.isPath q.isPath.reverse hT S hdL hcL hord
        hsep.2.1 hsep.1 hsep.2.2.2 hsep.2.2.1 q.ne.symm hpT hqr
      refine ⟨⟨p.dst,q.src,r,hr,hsep.2.2.1⟩,⟨q.dst,p.src,s,hs,hsep.2.1.symm⟩,?_,?_⟩
      · apply List.perm_iff_count.mpr
        intro e
        have hh := List.Perm.count_eq he e
        simpa only [List.count_append,Walk.edges_reverse,List.count_reverse] using hh
      · apply List.perm_iff_count.mpr
        intro v
        simp only [List.count_cons,List.count_nil]
        omega

end Erdos184Work.OddPaths.Absorption
#print axioms Erdos184Work.OddPaths.Absorption.clean_alternating
#print axioms Erdos184Work.OddPaths.Absorption.clean_same_arc_ordered
#print axioms Erdos184Work.OddPaths.Absorption.absorb_clean_cycle_ended
