import Submission.CleanEndpointCycleAbsorption
import Submission.EndpointPathReversal

/-! An unused cycle in a maximal endpoint-path packing must meet some path
internally. Outside-cycle intersections alone cannot prevent absorption.
This is a necessary obstruction, not the arbitrary-degree path theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 600000
variable {V : Type*} {G : SimpleGraph V} {z : V}

/-- Every path meets the specified walk only at its own endpoints. -/
def CleanOn (L : List (Piece G)) (R : G.Walk z z) : Prop :=
  ∀ p ∈ L, ∀ x, x ∈ p.walk.support → x ∈ R.support → x = p.src ∨ x = p.dst

lemma CleanOn.perm {L M : List (Piece G)} {R : G.Walk z z}
    (h : CleanOn L R) (hperm : L.Perm M) : CleanOn M R :=
  fun p hp => h p (hperm.mem_iff.mpr hp)

lemma CleanOn.reverse_first {p : Piece G} {L : List (Piece G)} {R : G.Walk z z}
    (h : CleanOn (p :: L) R) : CleanOn (p.reverse :: L) R := by
  intro q hq x hx hR
  rcases List.mem_cons.mp hq with rfl | hq
  · have hh := h p (by simp) x (by
      simpa only [Piece.reverse,Walk.support_reverse,List.mem_reverse] using hx) hR
    exact hh.symm
  · exact h q (List.mem_cons_of_mem _ hq) x hx hR

lemma CleanOn.reverse_second {p q : Piece G} {L : List (Piece G)} {R : G.Walk z z}
    (h : CleanOn (p :: q :: L) R) : CleanOn (p :: q.reverse :: L) R := by
  intro r hr x hx hR
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h r (by simp) x hx hR
  · have ht : CleanOn (q :: L) R := fun s hs => h s (List.mem_cons_of_mem _ hs)
    exact ht.reverse_first r hr x hx hR

lemma exists_terminal_head_clean {L : List (Piece G)} {R : G.Walk z z}
    (hL : Maximal L) (hcl : CleanOn L R) (v : V) :
    ∃ (p : Piece G) (M : List (Piece G)), Maximal (p :: M) ∧ p.dst = v ∧
      (edgeList (p :: M)).Perm (edgeList L) ∧ CleanOn (p :: M) R := by
  obtain ⟨p,hp,hv⟩ := List.mem_flatMap.mp (hL.1.2.2 v)
  have hperm := List.perm_cons_erase hp
  have hM := hL.perm hperm
  have hC := hcl.perm hperm
  have he := (edgeList_perm hperm).symm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv | hv
  · exact ⟨p.reverse,L.erase p,hM.reverse_first,hv.symm,
      (reverse_first_edge_perm p _).trans he,hC.reverse_first⟩
  · exact ⟨p,L.erase p,hM,hv.symm,he,hC⟩

lemma exists_initial_second_clean {p : Piece G} {L : List (Piece G)} {R : G.Walk z z}
    (hL : Maximal (p :: L)) (hcl : CleanOn (p :: L) R) (v : V)
    (ha : v ≠ p.src) (hb : v ≠ p.dst) :
    ∃ (q : Piece G) (M : List (Piece G)), Maximal (p :: q :: M) ∧ q.src = v ∧
      (edgeList (p :: q :: M)).Perm (edgeList (p :: L)) ∧ CleanOn (p :: q :: M) R := by
  have hv : v ∈ endpoints L := by
    have hh := hL.1.2.2 v
    simpa only [endpoints_cons,List.mem_cons,ha,hb,false_or] using hh
  obtain ⟨q,hq,hv⟩ := List.mem_flatMap.mp hv
  have hperm := (List.perm_cons_erase hq).cons p
  have hM := hL.perm hperm
  have hC := hcl.perm hperm
  have he := (edgeList_perm hperm).symm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv | hv
  · exact ⟨q,L.erase q,hM,hv.symm,he,hC⟩
  · exact ⟨q.reverse,L.erase q,hM.reverse_second,hv.symm,
      (reverse_second_edge_perm p q _).trans he,hC.reverse_second⟩

lemma Admissible.first_two_endpoints_distinct {p q : Piece G} {L : List (Piece G)}
    (hL : Admissible (p :: q :: L)) :
    p.src ≠ q.src ∧ p.src ≠ q.dst ∧ p.dst ≠ q.src ∧ p.dst ≠ q.dst := by
  have hn := hL.2.1
  change (p.src :: p.dst :: q.src :: q.dst :: endpoints L).Nodup at hn
  have hs := (List.nodup_cons.mp hn).1
  have ht := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  exact ⟨fun h => hs (by simp [h]),fun h => hs (by simp [h]),
    fun h => ht (by simp [h]),fun h => ht (by simp [h])⟩

variable [Fintype V]

lemma Maximal.clean_head_other_end_on_unused_cycle {p : Piece G} {L : List (Piece G)}
    (hL : Maximal (p :: L)) (R : G.Walk z z) (hR : R.IsCycle)
    (hcl : CleanOn (p :: L) R)
    (hdis : (edgeList (p :: L)).Disjoint R.edges) (hp : p.dst ∈ R.support) :
    p.src ∈ R.support := by
  by_contra hpa
  have hcard := hR.ncard_neighborSet_toSubgraph_eq_two hp
  obtain ⟨v,hv⟩ := (Set.ncard_pos (s := R.toSubgraph.neighborSet p.dst)).mp
    (show 0 < (R.toSubgraph.neighborSet p.dst).ncard by omega)
  have huv : G.Adj p.dst v := R.toSubgraph.adj_sub hv
  have he : s(p.dst,v) ∈ R.edges := R.mem_edges_toSubgraph.mp hv
  have hvc : v ∈ R.support := R.snd_mem_support_of_mem_edges he
  have hva : v ≠ p.src := by rintro rfl; contradiction
  obtain ⟨q,M,hM,hqv,hperm,hclM⟩ := exists_initial_second_clean hL hcl v hva huv.ne.symm
  subst v
  have hdisM : (edgeList (p :: q :: M)).Disjoint R.edges := by
    intro e he hc
    exact hdis (hperm.mem_iff.mp he) hc
  have hsep := hM.1.first_two_endpoints_distinct
  have huq : p.dst ∉ q.walk.support := by
    intro h
    exact (hclM q (by simp) p.dst h hp).elim hsep.2.2.1 hsep.2.2.2
  obtain ⟨r,hr,hrperm⟩ := CertificateStructure.cycle_edge_cons R hR huv he
  have hrs : r.support ⊆ R.support := by
    intro x hx
    obtain ⟨e,her,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil
      (r.not_nil_of_ne huv.ne.symm)).mp hx
    exact Walk.mem_support_of_mem_edges (hrperm.mem_iff.mp (List.mem_cons_of_mem _ her)) hxe
  have hclean : ∀ x, x ∈ p.walk.support → x ∈ r.support → x = p.dst := by
    intro x hx hrx
    exact (hclM p (by simp) x hx (hrs hrx)).resolve_left (fun h => hpa (h ▸ hrs hrx))
  have hdisr : (edgeList (p :: q :: M)).Disjoint (Walk.cons huv r).edges := by
    intro e he hc
    exact hdisM he (hrperm.mem_iff.mp hc)
  exact huq (hM.cons_pair_clean_blocked huv r hr hdisr hclean)

lemma Maximal.clean_path_endpoints_on_unused_cycle {L : List (Piece G)}
    (hL : Maximal L) (R : G.Walk z z) (hR : R.IsCycle) (hcl : CleanOn L R)
    (hdis : (edgeList L).Disjoint R.edges) {p : Piece G} (hp : p ∈ L)
    (hv : p.src ∈ R.support ∨ p.dst ∈ R.support) :
    p.src ∈ R.support ∧ p.dst ∈ R.support := by
  have hperm := List.perm_cons_erase hp
  have hM := hL.perm hperm
  have hC := hcl.perm hperm
  have hdisM : (edgeList (p :: L.erase p)).Disjoint R.edges := by
    intro e he hc
    exact hdis ((edgeList_perm hperm).mem_iff.mpr he) hc
  rcases hv with hv | hv
  · refine ⟨hv,?_⟩
    apply hM.reverse_first.clean_head_other_end_on_unused_cycle R hR hC.reverse_first _ hv
    intro e he hc
    exact hdisM ((reverse_first_edge_perm p _).mem_iff.mp he) hc
  · exact ⟨hM.clean_head_other_end_on_unused_cycle R hR hC hdisM hv,hv⟩

lemma Maximal.no_clean_unused_cycle {L : List (Piece G)}
    (hL : Maximal L) (R : G.Walk z z) (hR : R.IsCycle)
    (hdis : (edgeList L).Disjoint R.edges) (hcl : CleanOn L R) : False := by
  obtain ⟨p,M,hM,hpz,hperm,hclM⟩ := exists_terminal_head_clean hL hcl z
  have hdisM : (edgeList (p :: M)).Disjoint R.edges := by
    intro e he hc
    exact hdis (hperm.mem_iff.mp he) hc
  have hpd : p.dst ∈ R.support := by rw [hpz]; exact R.start_mem_support
  have hpa := hM.clean_head_other_end_on_unused_cycle R hR hclM hdisM hpd
  have hcard := hR.ncard_neighborSet_toSubgraph_eq_two hpd
  have hv : ∃ v, R.toSubgraph.Adj p.dst v ∧ v ≠ p.src := by
    by_contra! hn
    have hsub : R.toSubgraph.neighborSet p.dst ⊆ {p.src} := fun v hv => hn v hv
    have hh := Set.ncard_le_ncard hsub
    rw [hcard,Set.ncard_singleton] at hh
    omega
  obtain ⟨v,hv,hva⟩ := hv
  have huv : G.Adj p.dst v := R.toSubgraph.adj_sub hv
  have he : s(p.dst,v) ∈ R.edges := R.mem_edges_toSubgraph.mp hv
  have hvc := R.snd_mem_support_of_mem_edges he
  obtain ⟨q,N,hN,hqv,hpermN,hclN⟩ := exists_initial_second_clean hM hclM v hva huv.ne.symm
  subst v
  have hdisN : (edgeList (p :: q :: N)).Disjoint R.edges := by
    intro e he hc
    exact hdisM (hpermN.mem_iff.mp he) hc
  have hqb := (hN.clean_path_endpoints_on_unused_cycle R hR hclN hdisN (by simp)
    (Or.inl hvc)).2
  obtain ⟨r,s,hr,hs⟩ := Absorption.absorb_clean_cycle_ended p q R hR hpa hpd hvc hqb
    hN.1.first_two_endpoints_distinct (hclN p (by simp)) (hclN q (by simp))
  have hpos : 0 < R.edges.length := by simpa only [Walk.length_edges] using hR.three_le_length.trans_lt' (by omega)
  exact hN.no_two_exchange hR.isTrail.edges_nodup hpos hdisN hr hs

/-- The remaining obstruction is a genuinely internal contact with an unused
cycle, not merely intersections between the paths outside that cycle. -/
lemma Maximal.unused_cycle_internal_contact {L : List (Piece G)}
    (hL : Maximal L) (R : G.Walk z z) (hR : R.IsCycle)
    (hdis : (edgeList L).Disjoint R.edges) :
    ∃ p ∈ L, ∃ x ∈ p.walk.support,
      x ∈ R.support ∧ x ≠ p.src ∧ x ≠ p.dst := by
  by_contra hn
  apply hL.no_clean_unused_cycle R hR hdis
  intro p hp x hx hR
  by_contra hends
  have hs : x ≠ p.src := fun h => hends (Or.inl h)
  have ht : x ≠ p.dst := fun h => hends (Or.inr h)
  exact hn ⟨p,hp,x,hx,hR,hs,ht⟩

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Maximal.no_clean_unused_cycle
#print axioms Erdos184Work.OddPaths.Maximal.unused_cycle_internal_contact
