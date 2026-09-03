import Submission.CycleSegments

/-! Assembling the four canonical three-cycle junction models from local cycle segments. -/

open SimpleGraph
namespace Erdos184Work.ThreeCycleKernels
open PathSubstitution CycleSegments
namespace DoubleTriangle
abbrev sizes : Fin 3 → ℕ := ![2,2,2]
def place : (k : Fin 3) → Fin (sizes k) → Fin 3
  | 0 => ![0,1]
  | 1 => ![0,2]
  | 2 => ![1,2]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src2
  | 1 => src2
  | 2 => src2
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst2
  | 1 => dst2
  | 2 => dst2
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 6 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨1,⟨0,by decide⟩⟩
  | 3 => ⟨1,⟨1,by decide⟩⟩
  | 4 => ⟨2,⟨0,by decide⟩⟩
  | 5 => ⟨2,⟨1,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 3 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end DoubleTriangle

namespace MatchedFour
abbrev sizes : Fin 3 → ℕ := ![3,3,2]
def place : (k : Fin 3) → Fin (sizes k) → Fin 4
  | 0 => ![0,1,2]
  | 1 => ![0,1,3]
  | 2 => ![2,3]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src3
  | 1 => src3
  | 2 => src2
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst3
  | 1 => dst3
  | 2 => dst2
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 8 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨0,⟨2,by decide⟩⟩
  | 3 => ⟨1,⟨0,by decide⟩⟩
  | 4 => ⟨1,⟨1,by decide⟩⟩
  | 5 => ⟨1,⟨2,by decide⟩⟩
  | 6 => ⟨2,⟨0,by decide⟩⟩
  | 7 => ⟨2,⟨1,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 4 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end MatchedFour

namespace CompleteFive
abbrev sizes : Fin 3 → ℕ := ![4,3,3]
def place : (k : Fin 3) → Fin (sizes k) → Fin 5
  | 0 => ![0,2,1,3]
  | 1 => ![0,1,4]
  | 2 => ![2,3,4]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src4
  | 1 => src3
  | 2 => src3
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst4
  | 1 => dst3
  | 2 => dst3
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 10 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨0,⟨2,by decide⟩⟩
  | 3 => ⟨0,⟨3,by decide⟩⟩
  | 4 => ⟨1,⟨0,by decide⟩⟩
  | 5 => ⟨1,⟨1,by decide⟩⟩
  | 6 => ⟨1,⟨2,by decide⟩⟩
  | 7 => ⟨2,⟨0,by decide⟩⟩
  | 8 => ⟨2,⟨1,by decide⟩⟩
  | 9 => ⟨2,⟨2,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 5 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end CompleteFive

namespace Octahedron
abbrev sizes : Fin 3 → ℕ := ![4,4,4]
def place : (k : Fin 3) → Fin (sizes k) → Fin 6
  | 0 => ![0,2,1,3]
  | 1 => ![0,4,1,5]
  | 2 => ![2,4,3,5]
def localSrc : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => src4
  | 1 => src4
  | 2 => src4
def localDst : (k : Fin 3) → Fin (sizes k) → Fin (sizes k)
  | 0 => dst4
  | 1 => dst4
  | 2 => dst4
lemma local_ne : ∀ k i, place k (localSrc k i) ≠ place k (localDst k i) := by decide
lemma local_src_surjective : ∀ k, Function.Surjective (localSrc k) := by
  intro k i
  fin_cases k <;> refine ⟨i,?_⟩ <;> fin_cases i <;> rfl
def location : Fin 12 → (Σ k : Fin 3, Fin (sizes k))
  | 0 => ⟨0,⟨0,by decide⟩⟩
  | 1 => ⟨0,⟨1,by decide⟩⟩
  | 2 => ⟨0,⟨2,by decide⟩⟩
  | 3 => ⟨0,⟨3,by decide⟩⟩
  | 4 => ⟨1,⟨0,by decide⟩⟩
  | 5 => ⟨1,⟨1,by decide⟩⟩
  | 6 => ⟨1,⟨2,by decide⟩⟩
  | 7 => ⟨1,⟨3,by decide⟩⟩
  | 8 => ⟨2,⟨0,by decide⟩⟩
  | 9 => ⟨2,⟨1,by decide⟩⟩
  | 10 => ⟨2,⟨2,by decide⟩⟩
  | 11 => ⟨2,⟨3,by decide⟩⟩
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

lemma assembled_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 6 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  let F := assemble_segments sizes vertex hinj place localSrc localDst local_ne local_src_surjective
    root C hC S hdisC hpoints hmeet
  apply subdivision_number_le_two (reindexFamily F locationEquiv)
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover sizes vertex hinj place localSrc localDst local_ne local_src_surjective
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

#print axioms assembled_number_le_two
end Octahedron

end Erdos184Work.ThreeCycleKernels
