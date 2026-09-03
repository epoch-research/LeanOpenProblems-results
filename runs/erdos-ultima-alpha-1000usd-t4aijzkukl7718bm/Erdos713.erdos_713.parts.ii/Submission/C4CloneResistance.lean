import FormalConjecturesUtil
import Submission.CloneResistance
import Submission.NeighborhoodVC

/-! C4 cloning resistance is forced locally by the two twin stars, without
any optimality hypothesis on the host. This is not a rationality argument. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713C4CloneResistance
open Erdos713Cloning Erdos713DegreePenalty
variable {V : Type*}
set_option maxHeartbeats 1000000

/-- Making a clone C4-free costs at least d(v)-1 edges, even if edges may
be removed anywhere. The original host need not be C4-free or extremal. -/
theorem free_subclone_cost [Fintype V] (G : SimpleGraph V) (v : V)
    (J : SimpleGraph (Option V)) (hJ : J ≤ clone G v) (hf : (cycleGraph 4).Free J) :
    degreeR G v-1 ≤ edgesR (clone G v)-edgesR J := by
  have hK : Erdos713C4.K22.Free J := fun h =>
    hf (Erdos713NeighborhoodVC.cycle4_contained_k22.trans h)
  let T := (G.neighborFinset v).filter (fun w => J.Adj none (some w) ∧ J.Adj (some v) (some w))
  have hT : T.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    exact Option.some.inj (Erdos713C4.unique_common_of_free hK (by simp : (none : Option V) ≠ some v)
      ha'.1 ha'.2 hb'.1 hb'.2)
  let B := G.neighborFinset v \ T
  let M := (clone G v).edgeFinset \ J.edgeFinset
  let f : V → Sym2 (Option V) := fun w =>
    if J.Adj none (some w) then s(some v,some w) else s(none,some w)
  have hfmem : Set.MapsTo f (B : Set V) (M : Set (Sym2 (Option V))) := by
    intro w hw
    have hw' := mem_sdiff.mp hw
    have hadj : G.Adj v w := by simpa using hw'.1
    have hnot : ¬(J.Adj none (some w) ∧ J.Adj (some v) (some w)) := by
      intro hh
      exact hw'.2 (mem_filter.mpr ⟨hw'.1,hh⟩)
    by_cases hh : J.Adj none (some w)
    · have hh' : ¬J.Adj (some v) (some w) := fun h => hnot ⟨hh,h⟩
      simp only [f,if_pos hh,mem_coe,M,mem_sdiff,mem_edgeFinset,mem_edgeSet,clone_adj,
        project_some]
      exact ⟨hadj,hh'⟩
    · simp only [f,if_neg hh,mem_coe,M,mem_sdiff,mem_edgeFinset,mem_edgeSet,clone_adj,
        project_none,project_some]
      exact ⟨hadj,hh⟩
  have hfinj : Set.InjOn f (B : Set V) := by
    intro a _ b _ hab
    dsimp only [f] at hab
    split_ifs at hab <;> simp_all
    aesop
  have hBM : B.card ≤ M.card := card_le_card_of_injOn f hfmem hfinj
  have hN : B.card+T.card=G.degree v := by
    simpa only [B,card_neighborFinset_eq_degree] using
      card_sdiff_add_card_eq_card (show T ⊆ G.neighborFinset v from filter_subset _ _)
  have hM : M.card+J.edgeFinset.card=(clone G v).edgeFinset.card :=
    card_sdiff_add_card_eq_card (edgeFinset_mono hJ)
  have hbound : G.degree v+J.edgeFinset.card ≤ (clone G v).edgeFinset.card+1 := by omega
  have hboundR : (G.degree v : ℝ)+(J.edgeFinset.card : ℝ) ≤
      ((clone G v).edgeFinset.card : ℝ)+1 := by exact_mod_cast hbound
  unfold degreeR edgesR
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,← edgeFinset_card]
  linarith

/-- The bound is attained by retaining just one edge at the new vertex,
provided the original host is C4-free and the root has positive degree. -/
theorem exists_free_subclone_at_bound [Fintype V] (G : SimpleGraph V)
    (hG : (cycleGraph 4).Free G) (v : V) (hv : 0 < degreeR G v) :
    ∃ J : SimpleGraph (Option V), J ≤ clone G v ∧ (cycleGraph 4).Free J ∧
      edgesR (clone G v)-edgesR J = degreeR G v-1 := by
  have hv' : 0 < G.degree v := by
    unfold degreeR at hv
    simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hv
    exact_mod_cast hv
  obtain ⟨w,hw⟩ := G.degree_pos_iff_exists_adj v |>.mp hv'
  let Q : Finset V := {w}
  have hQ : ∀ z ∈ Q, G.Adj v z := by simpa only [Q,mem_singleton,forall_eq] using hw
  let J := Erdos713PartialCloning.partialClone G Q
  have hf : (cycleGraph 4).Free J := by
    intro hcopy
    have hs := Erdos713PartialCloning.supported_of_copy (cycleGraph 4) G v Q hQ hG hcopy
    have hd : ∀ a : Fin 4, 2 ≤ Nat.card ((cycleGraph 4).neighborSet a) := by
      intro a
      simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,cycleGraph_degree_three_le]
      exact le_rfl
    have hh := hs.card_ge_min_degree hd
    simp only [Q,card_singleton] at hh
    omega
  refine ⟨J,Erdos713PartialCloning.partial_le_clone G v Q hQ,hf,?_⟩
  unfold edgesR degreeR
  rw [card_edges_clone,Erdos713PartialCloning.card_edges]
  simp only [Q,card_singleton,Nat.cast_add,Nat.cast_one]
  ring

/-- The summed local obstruction needs no global optimality: it is already
present in every host, as soon as all remainders are C4-free. -/
theorem total_cost [Fintype V] (G : SimpleGraph V)
    (J : V → SimpleGraph (Option V)) (hJ : ∀ v, J v ≤ clone G v)
    (hf : ∀ v, (cycleGraph 4).Free (J v)) :
    2*edgesR G-Fintype.card V ≤ ∑ v, (edgesR (clone G v)-edgesR (J v)) := by
  have hh := sum_le_sum (s := (univ : Finset V)) (fun v _ => free_subclone_cost G v (J v) (hJ v) (hf v))
  simpa only [sum_sub_distrib,degreeR_sum,sum_const,card_univ,nsmul_eq_mul,mul_one] using hh

/-- At minimum degree two the total resistance is at least the host edge
count, regardless of its proportion of the extremal number. -/
theorem edge_scale_cost [Fintype V] (G : SimpleGraph V) (hdeg : ∀ v, 2 ≤ degreeR G v)
    (J : V → SimpleGraph (Option V)) (hJ : ∀ v, J v ≤ clone G v)
    (hf : ∀ v, (cycleGraph 4).Free (J v)) :
    edgesR G ≤ ∑ v, (edgesR (clone G v)-edgesR (J v)) := by
  have hd := sum_le_sum (s := (univ : Finset V)) (fun v _ => hdeg v)
  simp only [sum_const,card_univ,nsmul_eq_mul,degreeR_sum] at hd
  have hh := total_cost G J hJ hf
  linarith

#print axioms free_subclone_cost
#print axioms exists_free_subclone_at_bound
#print axioms edge_scale_cost
end Erdos713C4CloneResistance
