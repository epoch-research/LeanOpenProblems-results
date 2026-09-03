import Submission.NearCompletePairs

/-! Fresh endpoint labels for a complete even core with one missing edge.
A sharp cycle remainder omits precisely the two ends of the missing edge.
One old pair can be split at one of these fresh vertices. -/
namespace Erdos583NearCompleteCorePortsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CompletePrescribedPairsDevelopment Erdos583NearCompletePairsDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma bijective_add_two_labels {I V : Type*} [Fintype I] [Fintype V]
    (f : I → V) (u v : V) (hc : Fintype.card I+2=Fintype.card V)
    (hs : ∀ w, w ≠ u → w ≠ v → ∃ i, f i=w) :
    Function.Bijective (Sum.elim f (fun b : Bool ↦ if b then u else v)) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro w
    by_cases hu : w=u
    · exact ⟨Sum.inr true,hu.symm⟩
    · by_cases hv : w=v
      · exact ⟨Sum.inr false,hv.symm⟩
      · obtain ⟨i,hi⟩ := hs w hu hv
        exact ⟨Sum.inl i,hi⟩
  · simpa only [Fintype.card_sum,Fintype.card_bool] using hc

lemma cycle_remainder_ports_omit_two {V : Type*} [Fintype V] {H : SimpleGraph V}
    {t : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (H.deleteEdges C.toSubgraph.edgeSet) t)
    (u v : V) (hcard : 2*t+2=Fintype.card V)
    (hH : H=(⊤ : SimpleGraph V).deleteEdges {s(u,v)}) :
    Function.Bijective (Sum.elim T.endpoint (fun b : Bool ↦ if b then u else v)) := by
  apply bijective_add_two_labels T.endpoint u v
    (by simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hcard)
  intro w hwu hwv
  have hN : H.neighborSet w=(⊤ : SimpleGraph V).neighborSet w := by
    ext z
    simp only [mem_neighborSet,hH,deleteEdges_adj,top_adj,Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro hwz
      refine ⟨hwz,?_⟩
      intro hh
      exact (Sym2.eq_iff.mp hh).elim (fun h ↦ hwu h.1) (fun h ↦ hwv h.1)
  have ho : Odd (Nat.card (H.neighborSet w)) := by
    rw [hN]
    exact complete_even_degree_odd (k := t+1) (by omega) w
  have ho' : Odd (Nat.card ((H.deleteEdges C.toSubgraph.edgeSet).neighborSet w)) := by
    rw [Nat.card_coe_set_eq,Nat.odd_iff] at ho ⊢
    exact (delete_cycle_preserves_degree_parity hC w).trans ho
  obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T
    ((QuotaParity.quota_odd_iff T w).mpr ho').pos
  rcases hi with hi | hi
  · exact ⟨(i,true),hi.symm⟩
  · exact ⟨(i,false),hi.symm⟩

def splitStart {V : Type*} {t : ℕ} (v : V) (a : Fin t → V) : Fin (t+1) → V :=
  Fin.cases v a

def splitFinish {V : Type*} {t : ℕ} (v : V) (b : Fin t → V) (j : Fin t) : Fin (t+1) → V :=
  Fin.cases (b j) (fun i ↦ if i=j then v else b i)

lemma split_labels_bijective {V : Type*} [Fintype V] {t : ℕ}
    (a b : Fin t → V) (u v : V) (j : Fin t)
    (he : Function.Bijective (Sum.elim
      (fun z : Fin t × Bool ↦ if z.2 then a z.1 else b z.1)
      (fun z : Bool ↦ if z then u else v))) :
    Function.Bijective (fun z : Fin (t+1) × Bool ↦
      if z.2 then splitStart u a z.1 else splitFinish v b j z.1) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro w
    obtain ⟨z,hz⟩ := he.surjective w
    rcases z with ⟨i,c⟩ | c
    · cases c
      · by_cases hij : i=j
        · subst i
          exact ⟨(0,false),hz⟩
        · refine ⟨(i.succ,false),?_⟩
          simpa only [splitFinish,Fin.cases_succ,if_neg hij] using hz
      · exact ⟨(i.succ,true),hz⟩
    · cases c
      · refine ⟨(j.succ,false),?_⟩
        simpa only [splitFinish,Fin.cases_succ,if_pos rfl] using hz
      · exact ⟨(0,true),hz⟩
  · have hc := Fintype.card_of_bijective he
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hc ⊢
    omega

/-- Reconstruct a near-complete core after splitting any chosen original
endpoint pair at v. The two copies of v occur in different output pairs. -/
lemma near_complete_extended_pairs {V : Type*} [Fintype V] {t : ℕ}
    (a b : Fin t → V) (u v : V) (huv : u ≠ v) (j : Fin t)
    (he : Function.Bijective (Sum.elim
      (fun z : Fin t × Bool ↦ if z.2 then a z.1 else b z.1)
      (fun z : Bool ↦ if z then u else v))) :
    ∃ q : ∀ i, ((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).Walk
        (splitStart v a i) (splitFinish v b j i),
      (∀ i, (q i).IsPath) ∧
      Pairwise (fun i l ↦ Disjoint (q i).toSubgraph.edgeSet (q l).toSubgraph.edgeSet) ∧
      (⋃ i, (q i).toSubgraph.edgeSet)=((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).edgeSet := by
  classical
  have hbj : b j ≠ v := by
    intro hh
    have hx := he.injective (a₁ := Sum.inl (j,false)) (a₂ := Sum.inr false) hh
    cases hx
  have hnew := split_labels_bijective a b u v j he
  have hreplace : (fun z : Fin (t+1) × Bool ↦
      if z.2 then (if z.1=0 then u else splitStart v a z.1) else splitFinish v b j z.1)=
      (fun z : Fin (t+1) × Bool ↦
        if z.2 then splitStart u a z.1 else splitFinish v b j z.1) := by
    funext z
    rcases z with ⟨i,c⟩
    induction i using Fin.cases with
    | zero => cases c <;> simp [splitStart]
    | succ i => cases c <;> simp [splitStart]
  apply near_complete_prescribed_pairs u v huv (splitStart v a) (splitFinish v b j) 0 rfl hbj
  rwa [hreplace]

lemma near_complete_cycle_ports {V : Type*} [Fintype V] {H : SimpleGraph V}
    {t : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, H.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsTrail)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=H.edgeSet)
    (u v : V) (hcard : 2*t+2=Fintype.card V)
    (hH : H=(⊤ : SimpleGraph V).deleteEdges {s(u,v)}) :
    Function.Bijective (Sum.elim
      (fun z : Fin t × Bool ↦ if z.2 then a z.1 else b z.1)
      (fun z : Bool ↦ if z then u else v)) := by
  classical
  have hedge (i : Fin t) : ∀ e ∈ (p i).edges, e ∈ (H.deleteEdges C.toSubgraph.edgeSet).edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    refine ⟨(p i).edges_subset_edgeSet he,?_⟩
    intro heC
    exact Set.disjoint_left.mp (hCp i) heC ((p i).mem_edges_toSubgraph.mpr he)
  let q (i : Fin t) := (p i).transfer (H.deleteEdges C.toSubgraph.edgeSet) (hedge i)
  have hqe (i : Fin t) : (q i).toSubgraph.edgeSet=(p i).toSubgraph.edgeSet := by
    ext e
    simp only [q,Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  let T : TrailFamily (H.deleteEdges C.toSubgraph.edgeSet) t :=
    { start := a
      finish := b
      walk := q
      isTrail := fun i ↦ by
        simpa only [q,Walk.isTrail_def,Walk.edges_transfer] using hp i
      disjoint := fun i j hij ↦ by
        change Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet
        rw [hqe,hqe]
        exact hd hij
      cover := fun e ↦ by
        simp only [hqe,edgeSet_deleteEdges,Set.mem_diff]
        constructor
        · rintro ⟨heH,heC⟩
          rw [←hc] at heH
          exact Set.mem_iUnion.mp (heH.resolve_left heC)
        · rintro ⟨i,hi⟩
          exact ⟨(p i).toSubgraph.edgeSet_subset hi,
            fun heC ↦ Set.disjoint_left.mp (hCp i) heC hi⟩ }
  exact cycle_remainder_ports_omit_two C hC T u v hcard hH

end Erdos583NearCompleteCorePortsDevelopment
