import Submission.CycleEdgeAbsorption

/-! The part of a cycle in an independent set occupies at most half the cycle. -/
namespace Erdos583CycleIndependentDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {a : V}

lemma cycle_independent_card [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) (S : Set V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y) :
    2*(C.toSubgraph.verts ∩ S).ncard ≤ C.length := by
  classical
  have hlen := hC.three_le_length
  letI : NeZero C.length := ⟨by omega⟩
  let v (i : Fin C.length) := C.getVert i.val
  have hv : Function.Injective v := by
    intro i j he
    exact Fin.ext (hC.getVert_injOn' (by change i.val ≤ C.length-1; have := i.isLt; omega)
      (by change j.val ≤ C.length-1; have := j.isLt; omega) he)
  have hvC (x : V) : x ∈ C.toSubgraph.verts ↔ ∃ i, v i=x := by
    rw [Walk.mem_verts_toSubgraph]
    constructor
    · intro hx
      obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      by_cases he : j=C.length
      · refine ⟨0,?_⟩
        simpa only [he,Walk.getVert_length,v,Fin.val_zero,Walk.getVert_zero] using hj
      · exact ⟨⟨j,by omega⟩,hj⟩
    · rintro ⟨i,rfl⟩
      exact C.getVert_mem_support _
  have hn (i : Fin C.length) : C.toSubgraph.Adj (v i) (v (i+1)) := by
    have hh := C.toSubgraph_adj_getVert i.isLt
    have he : C.getVert (i.val+1)=v (i+1) := by
      change C.getVert (i.val+1)=C.getVert ((i+1).val)
      rw [Fin.val_add,Fin.val_one', Nat.mod_eq_of_lt (show 1 < C.length by omega)]
      by_cases h : i.val+1=C.length
      · rw [h,Nat.mod_self,Walk.getVert_length,Walk.getVert_zero]
      · rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    rwa [he] at hh
  let A := Finset.univ.filter fun i ↦ v i ∈ S
  have hAi : (A.image v : Set V)=C.toSubgraph.verts ∩ S := by
    ext x
    simp only [Finset.mem_coe,Finset.mem_image,A,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_inter_iff,hvC]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,rfl⟩,hi⟩
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,hi,rfl⟩
  have hcard : (C.toSubgraph.verts ∩ S).ncard=A.card := by
    rw [←hAi,Set.ncard_coe_finset,Finset.card_image_of_injective _ hv]
  have hsub : A.image (fun i ↦ i+1) ⊆ Finset.univ \ A := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hh
    exact hS _ (Finset.mem_filter.mp hi).2 _ (Finset.mem_filter.mp hh).2 (hn i)
  have hb := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun i j h ↦ add_right_cancel h),Finset.card_sdiff_of_subset (Finset.subset_univ A),Finset.card_univ,Fintype.card_fin] at hb
  rw [hcard]
  omega

lemma cycle_length_le_twice_complement [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) (S : Set V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y) :
    C.length ≤ 2*Sᶜ.ncard := by
  have hb := cycle_independent_card C hC S hS
  have he := Set.ncard_inter_add_ncard_diff_eq_ncard C.toSubgraph.verts S
  have hd : (C.toSubgraph.verts \ S).ncard ≤ Sᶜ.ncard := Set.ncard_le_ncard (fun _ hx ↦ hx.2)
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  rw [hv] at he
  omega


lemma cycle_independent_inter_le_complement [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) (S : Set V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y) :
    (C.toSubgraph.verts ∩ S).ncard ≤ Sᶜ.ncard := by
  have hb := cycle_independent_card C hC S hS
  have he := Set.ncard_inter_add_ncard_diff_eq_ncard C.toSubgraph.verts S
  have hd : (C.toSubgraph.verts \ S).ncard ≤ Sᶜ.ncard := Set.ncard_le_ncard (fun _ hx ↦ hx.2)
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  rw [hv] at he
  omega

end Erdos583CycleIndependentDevelopment
