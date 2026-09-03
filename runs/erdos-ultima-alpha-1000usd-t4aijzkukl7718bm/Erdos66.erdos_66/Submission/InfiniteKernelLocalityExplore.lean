import Submission.UniversalKernelAccuracyExplore

/-! Locality for genuine infinite coarse sets. Pair counts are cardinalities
of the sets of first endpoints, not a choice of finite approximants. -/
namespace Erdos66InfiniteKernelLocality
open Erdos66OriginRepair Erdos66DisjointPaletteAssembly
open scoped Classical
set_option maxHeartbeats 2000000

variable {G ι : Type*} [AddCommGroup G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι]

noncomputable def setPairCount {H : Type*} [AddCommGroup H]
    (A B : Set H) (z : H) : ℕ :=
  {x | x ∈ A ∧ z-x ∈ B}.ncard

def natSupport (B : Set ℕ) : Set ℤ := {x | 0 ≤ x ∧ x.toNat ∈ B}

noncomputable def coarseCut (B : Set ℕ) (n : ℕ) : Finset ℤ :=
  (Finset.Icc 0 (n:ℤ)).filter (fun x ↦ x.toNat ∈ B)

lemma mem_coarseCut (B : Set ℕ) (n : ℕ) (x : ℤ) :
    x ∈ coarseCut B n ↔ x ∈ natSupport B ∧ x ≤ n := by
  simp only [coarseCut,Finset.mem_filter,Finset.mem_Icc,natSupport,Set.mem_setOf_eq]
  tauto

/-- The coarse family may be infinite, and its members may overlap. -/
def infiniteAssembly (P : ι → Finset G) (B : ι → Set ℕ) : Set (G×ℤ) :=
  {z | ∃ i, z.1 ∈ P i ∧ z.2 ∈ natSupport (B i)}

lemma mem_assembly_cut (P : ι → Finset G) (B : ι → Set ℕ)
    (n : ℕ) (z : G×ℤ) :
    z ∈ assembly P (fun i ↦ coarseCut (B i) n) ↔
      z ∈ infiniteAssembly P B ∧ z.2 ≤ n := by
  simp only [assembly,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_product,mem_coarseCut,infiniteAssembly,Set.mem_setOf_eq]
  constructor
  · rintro ⟨i,hi,hB,hn⟩
    exact ⟨⟨i,hi,hB⟩,hn⟩
  · rintro ⟨⟨i,hi,hB⟩,hn⟩
    exact ⟨i,hi,hB,hn⟩

lemma infiniteAssembly_nonneg (P : ι → Finset G) (B : ι → Set ℕ)
    {z : G×ℤ} (hz : z ∈ infiniteAssembly P B) : 0 ≤ z.2 := by
  obtain ⟨i,hi,hB⟩ := hz
  exact hB.1

/-- Truncation at the target leaves every actual pair unchanged. The palette
need not be disjoint for this locality identity. -/
lemma assembly_count_locality (P : ι → Finset G) (B : ι → Set ℕ)
    (n : ℕ) (z : G) :
    pairCount (assembly P (fun i ↦ coarseCut (B i) n))
      (assembly P (fun i ↦ coarseCut (B i) n)) (z,(n:ℤ)) =
      setPairCount (infiniteAssembly P B) (infiniteAssembly P B) (z,(n:ℤ)) := by
  let C := assembly P (fun i ↦ coarseCut (B i) n)
  have he : {x : G×ℤ | x ∈ infiniteAssembly P B ∧
      (z,(n:ℤ))-x ∈ infiniteAssembly P B} =
      (↑(C.filter (fun x ↦ (z,(n:ℤ))-x ∈ C)) : Set (G×ℤ)) := by
    ext x
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter]
    constructor
    · rintro ⟨hx,hy⟩
      have hx0 := infiniteAssembly_nonneg P B hx
      have hy0 := infiniteAssembly_nonneg P B hy
      change 0 ≤ (n:ℤ)-x.2 at hy0
      constructor
      · exact (mem_assembly_cut P B n x).mpr ⟨hx,by omega⟩
      · exact (mem_assembly_cut P B n ((z,(n:ℤ))-x)).mpr ⟨hy,by
          change (n:ℤ)-x.2 ≤ n
          omega⟩
    · rintro ⟨hx,hy⟩
      exact ⟨((mem_assembly_cut P B n x).mp hx).1,
        ((mem_assembly_cut P B n ((z,(n:ℤ))-x)).mp hy).1⟩
  unfold setPairCount
  rw [he,Set.ncard_coe_finset]
  rfl

lemma coarse_count_locality (B C : Set ℕ) (n : ℕ) :
    pairCount (coarseCut B n) (coarseCut C n) (n:ℤ) =
      setPairCount (natSupport B) (natSupport C) (n:ℤ) := by
  have he : {x : ℤ | x ∈ natSupport B ∧ (n:ℤ)-x ∈ natSupport C} =
      (↑((coarseCut B n).filter (fun x ↦ (n:ℤ)-x ∈ coarseCut C n)) : Set ℤ) := by
    ext x
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,mem_coarseCut]
    constructor
    · rintro ⟨hx,hy⟩
      exact ⟨⟨hx,by have := hy.1; omega⟩,⟨hy,by have := hx.1; omega⟩⟩
    · tauto
  unfold setPairCount
  rw [he,Set.ncard_coe_finset]
  rfl

variable {α : Type*}

noncomputable def infiniteKernel (B : α → Set ℕ) (n : ℕ) (x y : α) : ℝ :=
  (setPairCount (natSupport (B x)) (natSupport (B y)) (n:ℤ):ℝ)

lemma infiniteKernel_eq_finite [Fintype α] [Nonempty α] [DecidableEq α]
    (B : α → Set ℕ) (n : ℕ) :
    infiniteKernel B n =
      Erdos66ActualColorRootTransfer.coarseKernel (fun x ↦ coarseCut (B x) n) (n:ℤ) := by
  funext x y
  simp only [infiniteKernel,Erdos66ActualColorRootTransfer.coarseKernel,
    coarse_count_locality]


/-- These coarse counts are the ordinary ordered natural-number counts. -/
lemma coarse_count_antidiagonal (B C : Set ℕ) (n : ℕ) :
    setPairCount (natSupport B) (natSupport C) (n:ℤ) =
      ((Finset.antidiagonal n).filter (fun ab ↦ ab.1 ∈ B ∧ ab.2 ∈ C)).card := by
  rw [←coarse_count_locality]
  symm
  unfold pairCount
  apply Finset.card_bij (fun ab _ ↦ (ab.1:ℤ))
  · intro ab hab
    simp only [Finset.mem_filter,Finset.mem_antidiagonal] at hab
    have he : (n:ℤ)-(ab.1:ℤ)=(ab.2:ℤ) := by omega
    simp only [Finset.mem_filter,mem_coarseCut,he,natSupport,Set.mem_setOf_eq,
      Int.natCast_nonneg,Int.toNat_natCast,true_and]
    exact ⟨⟨hab.2.1,by omega⟩,⟨hab.2.2,by omega⟩⟩
  · intro ab hab cd hcd he
    simp only [Finset.mem_filter,Finset.mem_antidiagonal] at hab hcd
    apply Prod.ext <;> dsimp at * <;> omega
  · intro z hz
    simp only [Finset.mem_filter,mem_coarseCut,natSupport,Set.mem_setOf_eq] at hz
    refine ⟨(z.toNat,((n:ℤ)-z).toNat),?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_antidiagonal]
      exact ⟨by omega,hz.1.1.2,hz.2.1.2⟩
    · exact Int.toNat_of_nonneg hz.1.1.1

lemma coarse_count_self (B : Set ℕ) (n : ℕ) :
    setPairCount (natSupport B) (natSupport B) (n:ℤ) =
      AdditiveCombinatorics.sumRep B n := by
  rw [coarse_count_antidiagonal,AdditiveCombinatorics.sumRep_def]

end Erdos66InfiniteKernelLocality
