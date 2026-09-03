import Submission.NonAlternate220Lift
import Submission.FourPointSegmentation

/-! Minimum-count exclusion of nonalternating disjoint contacts. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.NonAlternate220
open PathSubstitution CycleSegments
set_option maxHeartbeats 2000000
abbrev sizes : Fin 3 → ℕ := ![4,2,2]
def place : (k : Fin 3) → Fin (sizes k) → Fin 4
  | 0 => ![0,1,2,3]
  | 1 => ![0,1]
  | 2 => ![2,3]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src4
  | 1 => src2
  | 2 => src2
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst4
  | 1 => dst2
  | 2 => dst2
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl

def location : Fin 8 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨0,⟨2,by decide⟩⟩
  | 3 => ⟨0,⟨3,by decide⟩⟩
  | 4 => ⟨1,⟨0,by decide⟩⟩
  | 5 => ⟨1,⟨1,by decide⟩⟩
  | 6 => ⟨2,⟨0,by decide⟩⟩
  | 7 => ⟨2,⟨1,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_three {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 4 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G = 3 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_three (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

lemma contact_number_three {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 4 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (S0 : Segmentation (C 0) ![vertex 0,vertex 1,vertex 2,vertex 3] src4 dst4)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G = 3 := by
  obtain ⟨S1⟩ := two_segments_any (C 1) (hC 1)
    (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 1) (w := 1) (by decide))
    (L.ne (by decide : (0 : Fin 4) ≠ 1))
  obtain ⟨S2⟩ := two_segments_any (C 2) (hC 2)
    (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide))
    (L.ne (by decide : (2 : Fin 4) ≠ 3))
  have hs0 : vertex ∘ place 0 = ![vertex 0,vertex 1,vertex 2,vertex 3] := by funext i; fin_cases i <;> rfl
  have hs1 : vertex ∘ place 1 = ![vertex 0,vertex 1] := by funext i; fin_cases i <;> rfl
  have hs2 : vertex ∘ place 2 = ![vertex 2,vertex 3] := by funext i; fin_cases i <;> rfl
  have hs : ∀ k, Nonempty (Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k)) := by
    intro k
    fin_cases k
    · change Nonempty (Segmentation (C 0) (vertex ∘ place 0) src4 dst4)
      rw [hs0]; exact ⟨S0⟩
    · change Nonempty (Segmentation (C 1) (vertex ∘ place 1) src2 dst2)
      rw [hs1]; exact ⟨S1⟩
    · change Nonempty (Segmentation (C 2) (vertex ∘ place 2) src2 dst2)
      rw [hs2]; exact ⟨S2⟩
  let S k := Classical.choice (hs k)
  exact assembled_number_three vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover

def swap : Fin 4 → Fin 4 := ![0,1,3,2]
lemma swap_injective : Function.Injective swap := by decide
lemma swap_swap : ∀ w, swap (swap w) = w := by decide
lemma swap_place : ∀ k w, (∃ i, place k i = swap w) ↔ ∃ i, place k i = w := by decide

lemma swapped_layout {V : Type*} {G : SimpleGraph V}
    (vertex : Fin 4 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (L : ContactLayout sizes place vertex root C) :
    ContactLayout sizes place (vertex ∘ swap) root C := by
  refine ⟨L.injective.comp swap_injective,?_,?_⟩
  · intro k w
    exact (L.points k (swap w)).trans (swap_place k w)
  · intro k l hkl x hx hy
    obtain ⟨w,hw⟩ := L.meet k l hkl x hx hy
    exact ⟨swap w,by simp only [Function.comp_apply,swap_swap,hw]⟩

lemma alternating_segmentation_of_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 4 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (hn : Critical.number G ≤ 2) :
    Nonempty (Segmentation (C 0) ![vertex 0,vertex 2,vertex 1,vertex 3] src4 dst4) := by
  have hp (w : Fin 4) : vertex w ∈ (C 0).support := L.mem ⟨w,by fin_cases w <;> rfl⟩
  obtain ⟨k,hS⟩ := four_segments_orders_any (C 0) (hC 0) (hp 0) (hp 1) (hp 2) (hp 3)
    (L.ne (by decide : (0 : Fin 4) ≠ 1))
  fin_cases k
  · obtain ⟨S⟩ := hS
    have hh := contact_number_three vertex root C hC L S hdisC hcover
    omega
  · obtain ⟨S⟩ := hS
    have hh := contact_number_three (vertex ∘ swap) root C hC (swapped_layout vertex root C L) S hdisC hcover
    omega
  · exact hS

#print axioms alternating_segmentation_of_number_le_two
end Erdos184Work.NonAlternate220
