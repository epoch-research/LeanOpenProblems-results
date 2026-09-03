import Submission.EndpointPathMaximality

/-! A four-spoke cycle-absorption move. This is an auxiliary exchange, not an
arbitrary-degree path decomposition or a settlement of Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.Absorption
set_option maxHeartbeats 400000
variable {V : Type*} {G : SimpleGraph V} {w a b c d : V}

/-- Four arms from a common center, and two complementary rim paths from `b`
to `d`, can be rearranged into two simple paths. The first rim path avoids `a`
and the second avoids `c`; these are the opposite-marker conditions. -/
lemma four_spoke_paths
    (A : G.Walk w a) (B : G.Walk w b) (C : G.Walk w c) (D : G.Walk w d)
    (P Q : G.Walk b d)
    (hA : A.IsPath) (hB : B.IsPath) (hC : C.IsPath) (hD : D.IsPath)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hAB : ∀ x, x ∈ A.support → x ∈ B.support → x = w)
    (hDC : ∀ x, x ∈ D.support → x ∈ C.support → x = w)
    (hAP : ∀ x, x ∈ A.support → x ∈ P.support → x = a)
    (hBP : ∀ x, x ∈ B.support → x ∈ P.support → x = b)
    (hDQ : ∀ x, x ∈ D.support → x ∈ Q.support → x = d)
    (hCQ : ∀ x, x ∈ C.support → x ∈ Q.support → x = c)
    (ha : a ∉ P.support) (hc : c ∉ Q.support) :
    ∃ (r : G.Walk a d) (s : G.Walk b c),
      r.IsPath ∧ s.IsPath ∧
      (r.edges ++ s.edges).Perm
        (A.edges ++ B.edges ++ C.edges ++ D.edges ++ P.edges ++ Q.edges) := by
  let r := (A.reverse.append B).append P
  let s := (Q.append D.reverse).append C
  have hAB' : (A.reverse.append B).IsPath := by
    apply append_isPath_of_support_inter hA.reverse hB
    intro x hx hy
    exact hAB x (by simpa only [Walk.support_reverse,List.mem_reverse] using hx) hy
  have hr : r.IsPath := by
    apply append_isPath_of_support_inter hAB' hP
    intro x hx hy
    rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
    · have hxA : x ∈ A.support := by
        simpa only [Walk.support_reverse,List.mem_reverse] using hx
      exact (ha ((hAP x hxA hy) ▸ hy)).elim
    · exact hBP x hx hy
  have hQD : (Q.append D.reverse).IsPath := by
    apply append_isPath_of_support_inter hQ hD.reverse
    intro x hx hy
    exact hDQ x (by simpa only [Walk.support_reverse,List.mem_reverse] using hy) hx
  have hs : s.IsPath := by
    apply append_isPath_of_support_inter hQD hC
    intro x hx hy
    rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
    · exact (hc ((hCQ x hy hx) ▸ hx)).elim
    · exact hDC x (by simpa only [Walk.support_reverse,List.mem_reverse] using hx) hy
  refine ⟨r,s,hr,hs,?_⟩
  apply List.perm_iff_count.mpr
  intro e
  simp only [r,s,Walk.edges_append,Walk.edges_reverse,List.count_append,List.count_reverse]
  omega

/-- The four-spoke move absorbs an unused cycle while retaining the four
endpoints of two old paths. The old pairing of the four arms is arbitrary. -/
lemma absorb_four_spokes
    (A : G.Walk w a) (B : G.Walk w b) (C : G.Walk w c) (D : G.Walk w d)
    (P Q : G.Walk b d) (p q : Piece G)
    (hA : A.IsPath) (hB : B.IsPath) (hC : C.IsPath) (hD : D.IsPath)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hAB : ∀ x, x ∈ A.support → x ∈ B.support → x = w)
    (hDC : ∀ x, x ∈ D.support → x ∈ C.support → x = w)
    (hAP : ∀ x, x ∈ A.support → x ∈ P.support → x = a)
    (hBP : ∀ x, x ∈ B.support → x ∈ P.support → x = b)
    (hDQ : ∀ x, x ∈ D.support → x ∈ Q.support → x = d)
    (hCQ : ∀ x, x ∈ C.support → x ∈ Q.support → x = c)
    (ha : a ∉ P.support) (hc : c ∉ Q.support)
    (had : a ≠ d) (hbc : b ≠ c)
    (he : (p.walk.edges ++ q.walk.edges).Perm (A.edges ++ B.edges ++ C.edges ++ D.edges))
    (hv : [a,d,b,c].Perm [p.src,p.dst,q.src,q.dst]) :
    ∃ r s : Piece G,
      (r.walk.edges ++ s.walk.edges).Perm
        (p.walk.edges ++ q.walk.edges ++ (P.edges ++ Q.edges)) ∧
      [r.src,r.dst,s.src,s.dst].Perm [p.src,p.dst,q.src,q.dst] := by
  obtain ⟨r,s,hr,hs,hcov⟩ := four_spoke_paths A B C D P Q hA hB hC hD hP hQ
    hAB hDC hAP hBP hDQ hCQ ha hc
  refine ⟨⟨a,d,r,hr,had⟩,⟨b,c,s,hs,hbc⟩,?_,hv⟩
  apply List.perm_iff_count.mpr
  intro e
  have h₁ := List.Perm.count_eq hcov e
  have h₂ := List.Perm.count_eq he e
  simp only [List.count_append] at h₁ h₂ ⊢
  omega



/-- A maximal admissible family cannot have the indicated four-spoke
configuration around unused rim edges. No degree bound is needed. -/
lemma no_four_spokes_in_maximal
    (A : G.Walk w a) (B : G.Walk w b) (C : G.Walk w c) (D : G.Walk w d)
    (P Q : G.Walk b d) (p q : Piece G) (M : List (Piece G))
    (hA : A.IsPath) (hB : B.IsPath) (hC : C.IsPath) (hD : D.IsPath)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hAB : ∀ x, x ∈ A.support → x ∈ B.support → x = w)
    (hDC : ∀ x, x ∈ D.support → x ∈ C.support → x = w)
    (hAP : ∀ x, x ∈ A.support → x ∈ P.support → x = a)
    (hBP : ∀ x, x ∈ B.support → x ∈ P.support → x = b)
    (hDQ : ∀ x, x ∈ D.support → x ∈ Q.support → x = d)
    (hCQ : ∀ x, x ∈ C.support → x ∈ Q.support → x = c)
    (ha : a ∉ P.support) (hc : c ∉ Q.support)
    (had : a ≠ d) (hbc : b ≠ c)
    (he : (p.walk.edges ++ q.walk.edges).Perm (A.edges ++ B.edges ++ C.edges ++ D.edges))
    (hv : [a,d,b,c].Perm [p.src,p.dst,q.src,q.dst])
    (hmax : Maximal (p :: q :: M))
    (hrim : (P.edges ++ Q.edges).Nodup)
    (hpos : 0 < (P.edges ++ Q.edges).length)
    (hdis : (edgeList (p :: q :: M)).Disjoint (P.edges ++ Q.edges)) : False := by
  obtain ⟨r,s,hr,hs⟩ := absorb_four_spokes A B C D P Q p q hA hB hC hD hP hQ
    hAB hDC hAP hBP hDQ hCQ ha hc had hbc he hv
  exact hmax.no_two_exchange hrim hpos hdis hr hs

/-- The four-spoke exchange applied to two actual paths with a unique interior
intersection. Each old path meets the rim only at its endpoints, and the rim
paths separate the endpoints of the first old path. -/
lemma intersecting_paths_exchange
    (p : G.Walk a c) (q : G.Walk b d) (P Q : G.Walk b d)
    (hp : p.IsPath) (hq : q.IsPath) (hP : P.IsPath) (hQ : Q.IsPath)
    (hwp : w ∈ p.support) (hwq : w ∈ q.support)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = w)
    (hwa : a ≠ w) (hwc : c ≠ w) (hwb : b ≠ w) (hwd : d ≠ w)
    (hpc : ∀ x, x ∈ p.support → x ∈ P.support ∨ x ∈ Q.support → x = a ∨ x = c)
    (hqc : ∀ x, x ∈ q.support → x ∈ P.support ∨ x ∈ Q.support → x = b ∨ x = d)
    (ha : a ∉ P.support) (hc : c ∉ Q.support) :
    ∃ (r : G.Walk a d) (s : G.Walk b c), r.IsPath ∧ s.IsPath ∧
      (r.edges ++ s.edges).Perm (p.edges ++ q.edges ++ (P.edges ++ Q.edges)) := by
  let A := p.takeUntil w hwp
  let C := p.dropUntil w hwp
  let B := q.takeUntil w hwq
  let D := q.dropUntil w hwq
  have hAC : (A.append C).IsPath := by simpa only [A,C,Walk.take_spec] using hp
  have hBD : (B.append D).IsPath := by simpa only [B,D,Walk.take_spec] using hq
  have haC : a ∉ C.support := by
    intro h
    exact hAC.ne_of_mem_support_of_append hwa A.start_mem_support h rfl
  have hcA : c ∉ A.support := Walk.endpoint_notMem_support_takeUntil hp hwp hwc
  have hbD : b ∉ D.support := by
    intro h
    exact hBD.ne_of_mem_support_of_append hwb B.start_mem_support h rfl
  have hdB : d ∉ B.support := Walk.endpoint_notMem_support_takeUntil hq hwq hwd
  have hA_sub : A.support ⊆ p.support := p.support_takeUntil_subset hwp
  have hC_sub : C.support ⊆ p.support := p.support_dropUntil_subset hwp
  have hB_sub : B.support ⊆ q.support := q.support_takeUntil_subset hwq
  have hD_sub : D.support ⊆ q.support := q.support_dropUntil_subset hwq
  have hAB : ∀ x, x ∈ A.reverse.support → x ∈ B.reverse.support → x = w := by
    intro x hx hy
    apply hinter x
    · exact hA_sub (by simpa only [Walk.support_reverse,List.mem_reverse] using hx)
    · exact hB_sub (by simpa only [Walk.support_reverse,List.mem_reverse] using hy)
  have hDC : ∀ x, x ∈ D.support → x ∈ C.support → x = w := by
    intro x hx hy
    exact hinter x (hC_sub hy) (hD_sub hx)
  have hAP : ∀ x, x ∈ A.reverse.support → x ∈ P.support → x = a := by
    intro x hx hy
    have hxA : x ∈ A.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
    rcases hpc x (hA_sub hxA) (Or.inl hy) with h | h
    · exact h
    · exact (hcA (h ▸ hxA)).elim
  have hBP : ∀ x, x ∈ B.reverse.support → x ∈ P.support → x = b := by
    intro x hx hy
    have hxB : x ∈ B.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
    rcases hqc x (hB_sub hxB) (Or.inl hy) with h | h
    · exact h
    · exact (hdB (h ▸ hxB)).elim
  have hDQ : ∀ x, x ∈ D.support → x ∈ Q.support → x = d := by
    intro x hx hy
    rcases hqc x (hD_sub hx) (Or.inr hy) with h | h
    · exact (hbD (h ▸ hx)).elim
    · exact h
  have hCQ : ∀ x, x ∈ C.support → x ∈ Q.support → x = c := by
    intro x hx hy
    rcases hpc x (hC_sub hx) (Or.inr hy) with h | h
    · exact (haC (h ▸ hx)).elim
    · exact h
  obtain ⟨r,s,hr,hs,he⟩ := four_spoke_paths A.reverse B.reverse C D P Q
    hAC.of_append_left.reverse hBD.of_append_left.reverse hAC.of_append_right
    hBD.of_append_right hP hQ hAB hDC hAP hBP hDQ hCQ ha hc
  refine ⟨r,s,hr,hs,?_⟩
  have hep : A.edges ++ C.edges = p.edges := by
    simpa only [A,C,Walk.edges_append] using congrArg Walk.edges (p.take_spec hwp)
  have heq : B.edges ++ D.edges = q.edges := by
    simpa only [B,D,Walk.edges_append] using congrArg Walk.edges (q.take_spec hwq)
  apply List.perm_iff_count.mpr
  intro e
  have hh := List.Perm.count_eq he e
  have h₁ := congrArg (List.count e) hep
  have h₂ := congrArg (List.count e) heq
  simp only [Walk.edges_reverse,List.count_append,List.count_reverse] at hh h₁ h₂ ⊢
  omega

end Erdos184Work.OddPaths.Absorption
#print axioms Erdos184Work.OddPaths.Absorption.four_spoke_paths
#print axioms Erdos184Work.OddPaths.Absorption.absorb_four_spokes
#print axioms Erdos184Work.OddPaths.Absorption.no_four_spokes_in_maximal
#print axioms Erdos184Work.OddPaths.Absorption.intersecting_paths_exchange
