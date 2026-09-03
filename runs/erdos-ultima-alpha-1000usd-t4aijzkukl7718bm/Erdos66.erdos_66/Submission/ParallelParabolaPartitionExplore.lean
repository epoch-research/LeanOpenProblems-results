import Submission.FiberColorEnergyExplore
import Submission.DisjointPaletteAssemblyExplore

/-! The parallel parabolas form a complete disjoint partition. Their mixed
counts depend only on the sum of their labels. No origin repair is needed. -/
namespace Erdos66ParallelParabolaPartition
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66FiniteField
  Erdos66DisjointPaletteAssembly Erdos66FiberColorEnergy
open scoped Classical
set_option maxHeartbeats 2600000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def parallelCurve (u : F) : Finset (F×F) :=
  Finset.univ.image (fun x ↦ (x,x^2+u))

lemma mem_parallelCurve (u : F) (z : F×F) : z∈parallelCurve u ↔ z.2=z.1^2+u := by
  simp only [parallelCurve,Finset.mem_image,Finset.mem_univ,true_and,Prod.ext_iff]
  constructor
  · rintro ⟨x,hx,hy⟩; simpa only [hx] using hy.symm
  · intro hz; exact ⟨z.1,rfl,hz.symm⟩

lemma parallelCurve_disjoint {u v : F} (huv : u≠v) : Disjoint (parallelCurve u) (parallelCurve v) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  rw [mem_parallelCurve] at hz hz'
  exact huv (add_left_cancel (hz.symm.trans hz'))

lemma parallelCurve_cover {n : ℕ} (ρ : Fin n ≃ F) :
    Finset.univ.biUnion (fun i ↦ parallelCurve (ρ i))=Finset.univ := by
  ext z
  simp only [Finset.mem_univ,iff_true,Finset.mem_biUnion]
  refine ⟨ρ.symm (z.2-z.1^2),True.intro,?_⟩
  rw [mem_parallelCurve,ρ.apply_symm_apply]
  ring

lemma parallelCurve_card (u : F) : (parallelCurve u).card=Fintype.card F := by
  rw [parallelCurve,Finset.card_image_of_injective _ (fun x y he ↦ congrArg Prod.fst he),Finset.card_univ]

noncomputable def rootCoeff (u t s : F) : ℕ :=
  Fintype.card {x : F // x^2+(t-x)^2=s-u}

lemma parallelCurve_pairCount (u v t s : F) :
    pairCount (parallelCurve u) (parallelCurve v) (t,s)=rootCoeff (u+v) t s := by
  unfold pairCount parallelCurve
  rw [Finset.filter_image,Finset.card_image_of_injective _ (fun x y he ↦ congrArg Prod.fst he)]
  rw [rootCoeff,Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro x hx
  change ((t,s)-(x,x^2+u)∈parallelCurve v) ↔ _
  rw [mem_parallelCurve]
  dsimp only [Prod.fst_sub,Prod.snd_sub,Prod.fst,Prod.snd]
  constructor <;> intro he <;> linear_combination -he

lemma rootCoeff_identity (hF : ringChar F≠2) (u t s : F) :
    (rootCoeff u t s:ℝ)=1+(quadraticChar F (2*(s-u)-t^2):ℝ) := by
  have htwo : (2:F)≠0 := Ring.two_ne_zero hF
  have he := parabola_sum_count hF (1:F) 1 t (s-u) one_ne_zero one_ne_zero (by intro hh; apply htwo; linear_combination hh)
  norm_num at he
  unfold rootCoeff
  exact_mod_cast he

lemma rootCoeff_le_two (hF : ringChar F≠2) (u t s : F) : rootCoeff u t s≤2 := by
  have he := rootCoeff_identity hF u t s
  have hc : (quadraticChar F (2*(s-u)-t^2):ℝ)≤1 := by
    have hc := quadraticChar_abs_le_one (F := F) (2*(s-u)-t^2)
    have hc' := (le_abs_self _).trans hc
    exact_mod_cast hc'
  have hle : (rootCoeff u t s:ℝ)≤2 := by linarith
  exact_mod_cast hle

noncomputable def rootSum {n : ℕ} (ρ : Fin n ≃ F) (V : Fin n → Fin n → ℝ) (t s : F) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, V i j*(rootCoeff (ρ i+ρ j) t s:ℝ)

lemma labelSum_symm {n : ℕ} (ρ : Fin n ≃ F) (i j : Fin n) : ρ i+ρ j=ρ j+ρ i := add_comm _ _

lemma labelSum_cancel {n : ℕ} (ρ : Fin n ≃ F) (i j k : Fin n) (he : ρ i+ρ j=ρ i+ρ k) : j=k :=
  ρ.injective (add_left_cancel he)

lemma labelSum_diag_injective {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    Function.Injective (fun i ↦ ρ i+ρ i) := by
  intro i j hij
  apply ρ.injective
  apply (mul_left_injective₀ (Ring.two_ne_zero hF))
  simpa only [mul_two] using hij

lemma rootSum_one {n : ℕ} (ρ : Fin n ≃ F) (t s : F) :
    rootSum ρ (fun _ _ ↦ 1) t s=(n:ℝ)^2 := by
  have he := pairCount_biUnion_self Finset.univ (fun i ↦ parallelCurve (ρ i))
    (fun _ _ _ _ hij ↦ parallelCurve_disjoint (fun he ↦ hij (ρ.injective he))) (t,s)
  rw [parallelCurve_cover ρ] at he
  simp_rw [parallelCurve_pairCount] at he
  have hcard : Fintype.card F=n := by simpa only [Fintype.card_fin] using (Fintype.card_congr ρ).symm
  have hc : pairCount (Finset.univ:Finset (F×F)) Finset.univ (t,s)=n^2 := by
    simp [pairCount,hcard,pow_two]
  rw [hc] at he
  unfold rootSum
  simp only [one_mul]
  exact_mod_cast he.symm

lemma rootSum_fibers {n : ℕ} (ρ : Fin n ≃ F) (V : Fin n → Fin n → ℝ) (t s : F) :
    rootSum ρ V t s=∑ q : F, fiber n (fun i j ↦ ρ i+ρ j) V q*(rootCoeff q t s:ℝ) :=
  (sum_fiber_mul (fun i j ↦ ρ i+ρ j) V (fun q ↦ (rootCoeff q t s:ℝ))).symm

/-- One label-fiber energy controls every fine field-plane target. -/
theorem rootSum_sq_le_energy {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (V : Fin n → Fin n → ℝ) (t s : F) :
    (rootSum ρ V t s)^2≤4*(n:ℝ)*energy n (fun i j ↦ ρ i+ρ j) V := by
  rw [rootSum_fibers]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fiber n (fun i j ↦ ρ i+ρ j) V) (fun q ↦ (rootCoeff q t s:ℝ))
  have hcoeff (q : F) : (rootCoeff q t s:ℝ)^2≤4 := by
    have h0 : (0:ℝ)≤rootCoeff q t s := Nat.cast_nonneg _
    have h2 : (rootCoeff q t s:ℝ)≤2 := by exact_mod_cast rootCoeff_le_two hF q t s
    nlinarith
  have hsum : (∑ q : F, (rootCoeff q t s:ℝ)^2)≤4*(n:ℝ) := by
    have he := Finset.sum_le_sum (fun q (_ : q∈Finset.univ) ↦ hcoeff q)
    have hcard : Fintype.card F=n := by simpa only [Fintype.card_fin] using (Fintype.card_congr ρ).symm
    simpa only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,mul_comm] using he
  have hnonneg : 0≤energy n (fun i j ↦ ρ i+ρ j) V := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  change _ ≤ energy n (fun i j ↦ ρ i+ρ j) V*_ at hcs
  exact hcs.trans (by nlinarith only [hmul])

end Erdos66ParallelParabolaPartition
