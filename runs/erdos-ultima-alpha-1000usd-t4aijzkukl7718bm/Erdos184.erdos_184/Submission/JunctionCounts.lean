import Submission.CoreJunctionKernel

/-! Cardinal bounds and exact incidence counts for extracted junctions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V K : Type*} [Fintype V] [Fintype K]

lemma localJunction_card (B : K → Set V) (i : K) :
    Fintype.card (LocalJunction B i) =
      {x | x ∈ B i ∧ ∃ j, j ≠ i ∧ x ∈ B j}.ncard := by
  rw [← Nat.card_eq_fintype_card,Nat.card_congr (localJunctionEquiv B i)]
  exact Nat.card_coe_set_eq _

lemma localJunction_card_le (B : K → Set V) (b : ℕ)
    (hB : ∀ i j, i ≠ j → (B i ∩ B j).ncard ≤ b) (i : K) :
    Fintype.card (LocalJunction B i) ≤ b * (Fintype.card K - 1) := by
  rw [localJunction_card,Set.ncard_eq_toFinset_card']
  have he : {x | x ∈ B i ∧ ∃ j, j ≠ i ∧ x ∈ B j}.toFinset =
      (Finset.univ.erase i).biUnion (fun j => (B i ∩ B j).toFinset) := by
    ext x
    simp only [Set.mem_toFinset,Set.mem_setOf_eq,Finset.mem_biUnion,Finset.mem_erase,
      Finset.mem_univ,and_true,Set.mem_inter_iff]
    aesop
  rw [he]
  have hh := Finset.card_biUnion_le_card_mul (Finset.univ.erase i)
    (fun j => (B i ∩ B j).toFinset) b (by
      intro j hj
      rw [← Set.ncard_eq_toFinset_card']
      exact hB i j (Finset.mem_erase.mp hj).1.symm)
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Nat.mul_comm] using hh

noncomputable def junctionIncidenceEquiv (B : K → Set V) :
    (Σ i, LocalJunction B i) ≃ (Σ w : Junction B, {i : K // w.val ∈ B i}) where
  toFun z := ⟨z.2.val,⟨z.1,z.2.property⟩⟩
  invFun z := ⟨z.2.val,⟨z.1,z.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma sum_localJunction_card (B : K → Set V)
    (hB : ∀ w : Junction B, Fintype.card {i : K // w.val ∈ B i} = 2) :
    ∑ i, Fintype.card (LocalJunction B i) = 2 * Fintype.card (Junction B) := by
  have he := Fintype.card_congr (junctionIncidenceEquiv B)
  simp only [Fintype.card_sigma,hB] at he
  simpa [Nat.mul_comm] using he

lemma junction_card_le (B : K → Set V)
    (hpair : ∀ i j, i ≠ j → (B i ∩ B j).ncard ≤ 2)
    (hB : ∀ w : Junction B, Fintype.card {i : K // w.val ∈ B i} = 2) :
    Fintype.card (Junction B) ≤ Fintype.card K * (Fintype.card K - 1) := by
  have hh : (∑ i, Fintype.card (LocalJunction B i)) ≤
      ∑ _i : K, 2 * (Fintype.card K - 1) :=
    Finset.sum_le_sum (fun i _ => localJunction_card_le B 2 hpair i)
  rw [sum_localJunction_card B hB] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  nlinarith

variable {G : SimpleGraph V}

lemma ContactLayout.local_card {m : K → ℕ}
    {root : K → V} {C : ∀ i, G.Walk (root i) (root i)}
    {place : ∀ i, Fin (m i) → Junction (fun j => {x | x ∈ (C j).support})}
    (L : ContactLayout m place Subtype.val root C)
    (hplace : ∀ i, Function.Injective (place i)) (i : K) :
    Fintype.card (LocalJunction (fun j => {x | x ∈ (C j).support}) i) = m i := by
  let f : Fin (m i) → LocalJunction (fun j => {x | x ∈ (C j).support}) i :=
    fun j => ⟨place i j,L.mem ⟨j,rfl⟩⟩
  have hinj : Function.Injective f := by
    intro j k hjk
    exact hplace i (congrArg Subtype.val hjk)
  have hsur : Function.Surjective f := by
    intro w
    obtain ⟨j,hj⟩ := (L.points i w.val).mp w.property
    exact ⟨j,Subtype.ext hj⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsur⟩)).symm

#print axioms junction_card_le
#print axioms ContactLayout.local_card
end Erdos184Work.CycleSegments


namespace Erdos184Work.MaximumCoreFamilies
open CycleSegments MaximumCycles
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma walk_incidence_card (D : Finset G.Subgraph) (root : D → V)
    (C : ∀ i, G.Walk (root i) (root i)) (he : ∀ i, (C i).toSubgraph = i.val) (x : V) :
    Fintype.card {i : D // x ∈ (C i).support} = (D.filter (fun H => x ∈ H.verts)).card := by
  have hs (i : D) : x ∈ (C i).support ↔ x ∈ i.val.verts := by
    rw [← Walk.mem_verts_toSubgraph,he i]
  let e : {i : D // x ∈ (C i).support} ≃ (D.filter (fun H => x ∈ H.verts)) := {
    toFun := fun i => ⟨i.val.val,Finset.mem_filter.mpr ⟨i.val.property,(hs i.val).mp i.property⟩⟩
    invFun := fun i => ⟨⟨i.val,(Finset.mem_filter.mp i.property).1⟩,
      (hs _).mpr (Finset.mem_filter.mp i.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

lemma junction_two_incidence {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4) (root : D → V)
    (C : ∀ i, G.Walk (root i) (root i)) (he : ∀ i, (C i).toSubgraph = i.val)
    (w : Junction (fun j => {x | x ∈ (C j).support})) :
    Fintype.card {i : D // w.val ∈ (C i).support} = 2 := by
  rw [walk_incidence_card D root C he w.val]
  obtain ⟨i,j,hij,hi,hj⟩ := w.property
  have hi' : w.val ∈ i.val.verts := by rwa [← he i,Walk.mem_verts_toSubgraph]
  have hj' : w.val ∈ j.val.verts := by rwa [← he j,Walk.mem_verts_toSubgraph]
  have hneq : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hsub : ({i.val,j.val} : Finset G.Subgraph) ⊆ D.filter (fun H => w.val ∈ H.verts) := by
    intro H hH
    simp only [Finset.mem_insert,Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨i.property,hi'⟩
    · exact Finset.mem_filter.mpr ⟨j.property,hj'⟩
  have hlo := Finset.card_le_card hsub
  rw [Finset.card_pair hneq] at hlo
  have hc := piece_incidence_count hD.1 hD.2.1 w.val
  have hhi := hdeg w.val
  omega

lemma maximum_junction_bounds {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4) (root : D → V)
    (C : ∀ i, G.Walk (root i) (root i)) (he : ∀ i, (C i).toSubgraph = i.val) :
    Fintype.card (Junction (fun j => {x | x ∈ (C j).support})) ≤ D.card * (D.card-1) ∧
    ∀ i : D, Fintype.card (LocalJunction (fun j => {x | x ∈ (C j).support}) i) ≤ 2*(D.card-1) := by
  have hs (i : D) : {x | x ∈ (C i).support} = i.val.verts := by
    ext x
    rw [Set.mem_setOf_eq,← Walk.mem_verts_toSubgraph,he i]
  have hp (i j : D) (hij : i ≠ j) :
      ({x | x ∈ (C i).support} ∩ {x | x ∈ (C j).support}).ncard ≤ 2 := by
    rw [hs i,hs j]
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2
      i.val j.val i.property j.property (fun h => hij (Subtype.ext h))
  constructor
  · simpa only [Fintype.card_coe] using junction_card_le (fun j => {x | x ∈ (C j).support}) hp
      (by
        intro w
        simpa only [← Nat.card_eq_fintype_card,Set.mem_setOf_eq] using
          junction_two_incidence hD hdeg root C he w)
  · intro i
    simpa only [Fintype.card_coe] using localJunction_card_le
      (fun j => {x | x ∈ (C j).support}) 2 hp i

#print axioms maximum_junction_bounds
end Erdos184Work.MaximumCoreFamilies
