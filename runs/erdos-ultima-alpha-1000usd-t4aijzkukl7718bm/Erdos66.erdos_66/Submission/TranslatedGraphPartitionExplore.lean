import Submission.CompletePartitionColorTransferExplore

/-! Complete partitions by vertical translates of an arbitrary graph. The
all-target estimate needs only a bound on the graph's sum fibers. -/
namespace Erdos66TranslatedGraphPartition
open Erdos66OriginRepair Erdos66DisjointPaletteAssembly Erdos66FiberColorEnergy
open scoped Classical
set_option maxHeartbeats 2400000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def graphSlice (f : F → F) (u : F) : Finset (F×F) :=
  Finset.univ.image (fun x ↦ (x,f x+u))

lemma mem_graphSlice (f : F → F) (u : F) (z : F×F) : z∈graphSlice f u ↔ z.2=f z.1+u := by
  simp only [graphSlice,Finset.mem_image,Finset.mem_univ,true_and,Prod.ext_iff]
  constructor
  · rintro ⟨x,hx,hy⟩; simpa only [hx] using hy.symm
  · intro hz; exact ⟨z.1,rfl,hz.symm⟩

lemma graphSlice_disjoint (f : F → F) {u v : F} (huv : u≠v) :
    Disjoint (graphSlice f u) (graphSlice f v) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  rw [mem_graphSlice] at hz hz'
  exact huv (add_left_cancel (hz.symm.trans hz'))

lemma graphSlice_cover (f : F → F) {n : ℕ} (ρ : Fin n ≃ F) :
    Finset.univ.biUnion (fun i ↦ graphSlice f (ρ i))=Finset.univ := by
  ext z
  simp only [Finset.mem_univ,iff_true,Finset.mem_biUnion]
  refine ⟨ρ.symm (z.2-f z.1),True.intro,?_⟩
  rw [mem_graphSlice,ρ.apply_symm_apply]
  ring

lemma graphSlice_card (f : F → F) (u : F) : (graphSlice f u).card=Fintype.card F := by
  rw [graphSlice,Finset.card_image_of_injective _ (fun x y he ↦ congrArg Prod.fst he),Finset.card_univ]

noncomputable def sumCoeff (f : F → F) (u t s : F) : ℕ :=
  Fintype.card {x : F // f x+f (t-x)=s-u}

def HasBoundedSums (f : F → F) (D : ℕ) : Prop :=
  ∀ t s : F, Fintype.card {x : F // f x+f (t-x)=s}≤D

lemma sumCoeff_le {f : F → F} {D : ℕ} (hf : HasBoundedSums f D) (u t s : F) :
    sumCoeff f u t s≤D := hf t (s-u)

lemma graphSlice_pairCount (f : F → F) (u v t s : F) :
    pairCount (graphSlice f u) (graphSlice f v) (t,s)=sumCoeff f (u+v) t s := by
  unfold pairCount graphSlice
  rw [Finset.filter_image,Finset.card_image_of_injective _ (fun x y he ↦ congrArg Prod.fst he)]
  rw [sumCoeff,Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro x hx
  change ((t,s)-(x,f x+u)∈graphSlice f v) ↔ _
  rw [mem_graphSlice]
  dsimp only [Prod.fst_sub,Prod.snd_sub,Prod.fst,Prod.snd]
  constructor <;> intro he <;> linear_combination -he

noncomputable def graphSum (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (V : Fin n → Fin n → ℝ) (t s : F) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, V i j*(sumCoeff f (ρ i+ρ j) t s:ℝ)

lemma graphSum_one (f : F → F) {n : ℕ} (ρ : Fin n ≃ F) (t s : F) :
    graphSum f ρ (fun _ _ ↦ 1) t s=(n:ℝ)^2 := by
  have he := pairCount_biUnion_self Finset.univ (fun i ↦ graphSlice f (ρ i))
    (fun _ _ _ _ hij ↦ graphSlice_disjoint f (fun he ↦ hij (ρ.injective he))) (t,s)
  rw [graphSlice_cover f ρ] at he
  simp_rw [graphSlice_pairCount] at he
  have hcard : Fintype.card F=n := by simpa only [Fintype.card_fin] using (Fintype.card_congr ρ).symm
  have hc : pairCount (Finset.univ:Finset (F×F)) Finset.univ (t,s)=n^2 := by
    simp [pairCount,hcard,pow_two]
  rw [hc] at he
  unfold graphSum
  simp only [one_mul]
  exact_mod_cast he.symm

lemma graphSum_fibers (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (V : Fin n → Fin n → ℝ) (t s : F) :
    graphSum f ρ V t s=∑ q : F, fiber n (fun i j ↦ ρ i+ρ j) V q*(sumCoeff f q t s:ℝ) :=
  (sum_fiber_mul (fun i j ↦ ρ i+ρ j) V (fun q ↦ (sumCoeff f q t s:ℝ))).symm

/-- The controlling energy does not depend on the graph f. The graph may
therefore be chosen later, provided its sum fibers obey the stated bound. -/
theorem graphSum_sq_le_energy (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (D : ℕ) (hf : HasBoundedSums f D) (V : Fin n → Fin n → ℝ) (t s : F) :
    (graphSum f ρ V t s)^2≤(D:ℝ)^2*(n:ℝ)*energy n (fun i j ↦ ρ i+ρ j) V := by
  rw [graphSum_fibers]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fiber n (fun i j ↦ ρ i+ρ j) V) (fun q ↦ (sumCoeff f q t s:ℝ))
  have hcoeff (q : F) : (sumCoeff f q t s:ℝ)^2≤(D:ℝ)^2 := by
    have hle : (sumCoeff f q t s:ℝ)≤D := by exact_mod_cast sumCoeff_le hf q t s
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
  have hsum : (∑ q : F, (sumCoeff f q t s:ℝ)^2)≤(D:ℝ)^2*(n:ℝ) := by
    have he := Finset.sum_le_sum (fun q (_ : q∈Finset.univ) ↦ hcoeff q)
    have hcard : Fintype.card F=n := by simpa only [Fintype.card_fin] using (Fintype.card_congr ρ).symm
    simpa only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,mul_comm] using he
  have hnonneg : 0≤energy n (fun i j ↦ ρ i+ρ j) V := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  change _ ≤ energy n (fun i j ↦ ρ i+ρ j) V*_ at hcs
  exact hcs.trans (by nlinarith only [hmul])

end Erdos66TranslatedGraphPartition
