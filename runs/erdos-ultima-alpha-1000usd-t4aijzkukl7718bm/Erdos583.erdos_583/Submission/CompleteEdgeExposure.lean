import Submission.CompletePrescribedPairs

/-! Prescribed endpoint pairs and a prescribed first edge in a complete
even graph. The first edge must lead to an endpoint of a different pair. -/
namespace Erdos583CompleteEdgeExposureDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CompletePrescribedPairsDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma complete_path_lengths {V : Type*} [Fintype V] {k : ℕ}
    (a b : Fin k → V) (p : ∀ i, (⊤ : SimpleGraph V).Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hc : (⋃ i, (p i).toSubgraph.edgeSet)=(⊤ : SimpleGraph V).edgeSet)
    (hcard : 2*k=Fintype.card V) : ∀ i, (p i).length+1=Fintype.card V := by
  classical
  have hsize : (⊤ : SimpleGraph V).edgeSet.ncard=k*(Fintype.card V-1) := by
    rw [Set.ncard_eq_toFinset_card']
    change (⊤ : SimpleGraph V).edgeFinset.card=_
    rw [card_edgeFinset_top_eq_card_choose_two,←hcard,Nat.choose_two_right]
    simp [Nat.mul_assoc]
  rw [←hc,Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) hd,
    finsum_eq_sum_of_fintype] at hsize
  have hsum : (∑ i, (p i).length)=k*(Fintype.card V-1) := by
    simpa only [trail_edgeSet_ncard _ (hp _).isTrail] using hsize
  intro j
  have hupper (i : Fin k) : (p i).length ≤ Fintype.card V-1 := by
    have hh := (hp i).length_lt; omega
  have hrest := Finset.sum_le_sum (s := Finset.univ.erase j) (fun i _ ↦ hupper i)
  simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hrest
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin k)) (fun i ↦ (p i).length)
    (Finset.mem_univ j)
  rw [hsum] at he
  have hj := (hp j).length_lt
  have hk : 1 ≤ k := by have hh := j.isLt; omega
  have hv : 1 ≤ Fintype.card V := by omega
  have hk' := Nat.sub_add_cancel hk
  have hv' := Nat.sub_add_cancel hv
  nlinarith

lemma path_second_ne_finish {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (h2 : 2 ≤ p.length) : p.snd ≠ b := by
  intro he
  have hh := hp.getVert_injOn (by omega : 1 ≤ p.length) (le_refl p.length)
    (by simpa only [Walk.getVert_length] using he)
  omega

lemma complete_prescribed_first_edge {V : Type*} [Fintype V] {k : ℕ}
    (a b : Fin k → V)
    (he : Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1))
    (i j : Fin k) (hij : i ≠ j) (c : Bool) :
    ∃ p : ∀ l, (⊤ : SimpleGraph V).Walk (a l) (b l),
      (∀ l, (p l).IsPath) ∧
      Pairwise (fun l m ↦ Disjoint (p l).toSubgraph.edgeSet (p m).toSubgraph.edgeSet) ∧
      (⋃ l, (p l).toSubgraph.edgeSet)=(⊤ : SimpleGraph V).edgeSet ∧
      (p i).snd=(if c then a j else b j) := by
  classical
  obtain ⟨p,hp,hd,hcover⟩ := complete_prescribed_pairs a b he
  let d : Fin k × Bool ≃ V := Equiv.ofBijective _ he
  have hcard : 2*k=Fintype.card V := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm]
      using Fintype.card_of_bijective he
  have hlen := complete_path_lengths a b p hp hd hcover hcard
  have hk : 2 ≤ k := by
    by_contra! hh
    have hi := i.isLt
    have hj := j.isLt
    exact hij (Fin.ext (by omega))
  have h2 : 2 ≤ (p i).length := by have hh := hlen i; omega
  have hn : ¬(p i).Nil := fun h ↦ by have hh := Walk.nil_iff_length_eq.mp h; omega
  obtain ⟨⟨l,e⟩,hle⟩ := d.surjective (p i).snd
  have hil : i ≠ l := by
    intro h; subst l
    cases e
    · exact path_second_ne_finish (p i) (hp i) h2 hle.symm
    · exact ((p i).adj_snd hn).ne hle
  let μ : Fin k ≃ Fin k := Equiv.swap l j
  let θ (z : Fin k) : Bool ≃ Bool :=
    if z=l ∧ e ≠ c then Equiv.boolNot else Equiv.refl Bool
  let ρ : Fin k × Bool ≃ Fin k × Bool :=
    (Equiv.prodCongrRight θ).trans (Equiv.prodCongr μ (Equiv.refl Bool))
  let f : V ≃ V := d.symm.trans (ρ.trans d)
  have hμi : μ i=i := by simp [μ,Equiv.swap_apply_of_ne_of_ne hil hij]
  have hθi : θ i=Equiv.refl Bool := by simp [θ,hil]
  have hfi (t : Bool) : f (d (i,t))=d (i,t) := by simp [f,ρ,hθi,hμi]
  have hfn : f (p i).snd=(if c then a j else b j) := by
    rw [←hle]
    have hθle : θ l e=c := by
      by_cases hec : e=c
      · simp [θ,hec]
      · cases e <;> cases c <;> simp_all [θ,Equiv.boolNot]
    simpa only [f,Equiv.trans_apply,Equiv.symm_apply_apply,ρ,Equiv.prodCongrRight_apply,
      Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,hθle,μ,Equiv.swap_apply_left] using
      (show d (j,c)=(if c then a j else b j) from rfl)
  let F : (⊤ : SimpleGraph V) →g (⊤ : SimpleGraph V) := ⟨f,fun h hh ↦ h (f.injective hh)⟩
  have hfa (z : Fin k) : f (a z)=if z=l ∧ e ≠ c then b (μ z) else a (μ z) := by
    change d (ρ (d.symm (d (z,true))))=_
    rw [Equiv.symm_apply_apply]
    change d (μ z, θ z true)=_
    by_cases hz : z=l ∧ e ≠ c
    · rw [if_pos hz,show θ z=Equiv.boolNot from if_pos hz]; rfl
    · rw [if_neg hz,show θ z=Equiv.refl Bool from if_neg hz]; rfl
  have hfb (z : Fin k) : f (b z)=if z=l ∧ e ≠ c then a (μ z) else b (μ z) := by
    change d (ρ (d.symm (d (z,false))))=_
    rw [Equiv.symm_apply_apply]
    change d (μ z, θ z false)=_
    by_cases hz : z=l ∧ e ≠ c
    · rw [if_pos hz,show θ z=Equiv.boolNot from if_pos hz]; rfl
    · rw [if_neg hz,show θ z=Equiv.refl Bool from if_neg hz]; rfl
  let q (z : Fin k) : (⊤ : SimpleGraph V).Walk (a (μ z)) (b (μ z)) :=
    if hz : z=l ∧ e ≠ c then
      ((p z).reverse.map F).copy (by simpa only [if_pos hz] using hfb z)
        (by simpa only [if_pos hz] using hfa z)
    else ((p z).map F).copy (by simpa only [if_neg hz] using hfa z)
        (by simpa only [if_neg hz] using hfb z)
  have hq (z : Fin k) : (q z).IsPath := by
    dsimp only [q]
    split_ifs
    · simpa only [Walk.isPath_copy] using Walk.map_isPath_of_injective f.injective (hp z).reverse
    · simpa only [Walk.isPath_copy] using Walk.map_isPath_of_injective f.injective (hp z)
  have hqe (z : Fin k) : (q z).toSubgraph.edgeSet=Sym2.map f '' (p z).toSubgraph.edgeSet := by
    dsimp only [q]
    split_ifs <;> simp only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_map,
      Subgraph.edgeSet_map,Walk.toSubgraph_reverse] <;> rfl
  have hqd : Pairwise (fun z w ↦ Disjoint (q z).toSubgraph.edgeSet (q w).toSubgraph.edgeSet) := by
    intro z w hzw
    rw [hqe,hqe]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := Sym2.map.injective f.injective (hux.trans hvx.symm)
    exact Set.disjoint_left.mp (hd hzw) hu (huv.symm ▸ hv)
  have hqc : (⋃ z, (q z).toSubgraph.edgeSet)=(⊤ : SimpleGraph V).edgeSet := by
    ext edge
    constructor
    · rintro heq
      obtain ⟨z,hz⟩ := Set.mem_iUnion.mp heq
      exact (q z).toSubgraph.edgeSet_subset hz
    · induction edge using Sym2.ind with
      | h u v =>
        intro huv
        have hpre : s(f.symm u,f.symm v) ∈ (⊤ : SimpleGraph V).edgeSet :=
          fun h ↦ huv (f.symm.injective h)
        rw [←hcover] at hpre
        obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hpre
        refine Set.mem_iUnion.mpr ⟨z,?_⟩
        rw [hqe]
        exact ⟨_,hz,by simp⟩
  let P (z : Fin k) : (⊤ : SimpleGraph V).Walk (a z) (b z) := (q (μ.symm z)).copy (by simp) (by simp)
  have hPe (z : Fin k) : (P z).toSubgraph=(q (μ.symm z)).toSubgraph :=
    NormalTrailSystem.walk_copy_subgraph _ _ _
  refine ⟨P,?_,?_,?_,?_⟩
  · intro z; simpa only [P,Walk.isPath_copy] using hq (μ.symm z)
  · intro z w hzw
    rw [hPe,hPe]
    exact hqd (fun h ↦ hzw (μ.symm.injective h))
  · rw [show (⋃ z, (P z).toSubgraph.edgeSet)=(⋃ z, (q z).toSubgraph.edgeSet) from ?_]
    · exact hqc
    · ext edge
      simp only [hPe,Set.mem_iUnion]
      refine ⟨fun ⟨z,hz⟩ ↦ ⟨_,hz⟩,?_⟩
      rintro ⟨z,hz⟩
      refine ⟨μ z,?_⟩
      exact (congrArg (fun w ↦ edge ∈ (q w).toSubgraph.edgeSet) (μ.symm_apply_apply z)).symm ▸ hz
  · have hμii : μ.symm i=i := by
      apply μ.injective
      simp only [Equiv.apply_symm_apply,hμi]
    simp only [P,Walk.snd,Walk.getVert_copy]
    change (q (μ.symm i)).snd=_
    rw [congrArg (fun z ↦ (q z).snd) hμii]
    dsimp only [q]
    rw [dif_neg (by tauto : ¬(i=l ∧ e ≠ c))]
    simpa only [Walk.getVert_copy,Walk.getVert_map] using hfn

end Erdos583CompleteEdgeExposureDevelopment
