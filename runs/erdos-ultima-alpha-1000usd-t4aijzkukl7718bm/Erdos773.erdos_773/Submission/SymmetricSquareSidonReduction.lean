import FormalConjecturesUtil

/-!
# Reflection-symmetric reduction for Sidon subsets of the squares

Every finite root set in `[1,N]` has a reflection-symmetric subset of size
at least its squared cardinality divided by `2*N`. Thus the near-linear
square-Sidon conjecture is equivalent to its reflection-symmetric version.
Neither version is proved here. No fullness or distribution assumption is
placed on the original root set.
-/
namespace Erdos773.SymmetricSquareSidonReduction
open Finset Filter
set_option maxHeartbeats 1000000

/-- Reflection about `s/2`, with the upper bound needed for natural subtraction. -/
def Symmetric (s : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, a ≤ s ∧ s-a ∈ A

/-- The part of `A` paired by reflection about `s/2`. -/
def symmetricPart (A : Finset ℕ) (s : ℕ) : Finset ℕ :=
  A.filter (fun a => a ≤ s ∧ s-a ∈ A)

lemma symmetricPart_subset (A : Finset ℕ) (s : ℕ) : symmetricPart A s ⊆ A :=
  filter_subset _ _

lemma symmetricPart_symmetric (A : Finset ℕ) (s : ℕ) :
    Symmetric s (symmetricPart A s) := by
  intro a ha
  obtain ⟨ha,has,hsa⟩ := mem_filter.mp ha
  refine ⟨has,mem_filter.mpr ⟨hsa,by omega,?_⟩⟩
  simpa only [Nat.sub_sub_self has] using ha

lemma sum_fiber_card (A : Finset ℕ) (s : ℕ) :
    ((A ×ˢ A).filter (fun p => p.1+p.2=s)).card = (symmetricPart A s).card := by
  let F := (A ×ˢ A).filter (fun p => p.1+p.2=s)
  have hinj : Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
    intro a ha b hb he
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    exact Prod.ext he (by omega)
  have himg : F.image Prod.fst = symmetricPart A s := by
    ext a
    constructor
    · intro ha
      obtain ⟨⟨b,c⟩,hp,rfl⟩ := mem_image.mp ha
      obtain ⟨hp,he⟩ := mem_filter.mp hp
      obtain ⟨hb,hc⟩ := mem_product.mp hp
      exact mem_filter.mpr ⟨hb,by dsimp at he ⊢; omega,by simpa only [show s-b=c by dsimp at he; omega] using hc⟩
    · intro ha
      obtain ⟨ha,has,hsa⟩ := mem_filter.mp ha
      exact mem_image.mpr ⟨(a,s-a),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hsa⟩,by omega⟩,rfl⟩
  rw [← himg,card_image_of_injOn hinj]

/-- Count ordered pairs by their root sum; diagonal pairs are included. -/
theorem pair_count (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    A.card^2 = ∑ s ∈ Icc 1 (2*N), (symmetricPart A s).card := by
  have hmap (p : ℕ × ℕ) (hp : p ∈ A ×ˢ A) : p.1+p.2 ∈ Icc 1 (2*N) := by
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    obtain ⟨ha1,haN⟩ := mem_Icc.mp (hA ha)
    obtain ⟨hb1,hbN⟩ := mem_Icc.mp (hA hb)
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have h := card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1+p.2)
    (s := A ×ˢ A) (t := Icc 1 (2*N)) hmap
  simpa only [card_product,← pow_two,sum_fiber_card] using h

/-- A reflection-symmetric subset with a quantitative cardinality bound. -/
theorem exists_large_symmetric_part (N : ℕ) (hN : 0 < N)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    ∃ s ∈ Icc 1 (2*N), ∃ B ⊆ A, Symmetric s B ∧
      A.card^2 ≤ 2*N*B.card := by
  obtain ⟨s,hs,hmax⟩ := exists_max_image (Icc 1 (2*N))
    (fun s => (symmetricPart A s).card) (nonempty_Icc.mpr (by omega))
  refine ⟨s,hs,symmetricPart A s,symmetricPart_subset A s,
    symmetricPart_symmetric A s,?_⟩
  rw [pair_count N A hA]
  calc
    _ ≤ ∑ _t ∈ Icc 1 (2*N), (symmetricPart A s).card := sum_le_sum hmax
    _ = _ := by simp

lemma square_sidon_subset {A B : Finset ℕ} (hBA : B ⊆ A)
    (hA : IsSidon (A.image (fun n => n^2) : Set ℕ)) :
    IsSidon (B.image (fun n => n^2) : Set ℕ) := by
  apply Set.IsSidon.subset hA
  exact_mod_cast image_subset_image hBA

/-- This extraction preserves actual square-Sidonness by containment. -/
theorem extract_symmetric_sidon (N : ℕ) (hN : 0 < N)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hSidon : IsSidon (A.image (fun n => n^2) : Set ℕ)) :
    ∃ s ∈ Icc 1 (2*N), ∃ B ⊆ A, Symmetric s B ∧
      IsSidon (B.image (fun n => n^2) : Set ℕ) ∧ A.card^2 ≤ 2*N*B.card := by
  obtain ⟨s,hs,B,hBA,hB,hcard⟩ := exists_large_symmetric_part N hN A hA
  exact ⟨s,hs,B,hBA,hB,square_sidon_subset hBA hSidon,hcard⟩

/-- Any upper bound for all symmetric Sidon root sets gives an upper bound
for every Sidon root set. The upper-bound hypothesis is not supplied here. -/
theorem uniform_symmetric_bound_transfers (N K : ℕ) (hN : 0 < N)
    (hK : ∀ s ∈ Icc 1 (2*N), ∀ B : Finset ℕ, B ⊆ Icc 1 N →
      Symmetric s B → IsSidon (B.image (fun n => n^2) : Set ℕ) → B.card ≤ K)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hSidon : IsSidon (A.image (fun n => n^2) : Set ℕ)) :
    A.card^2 ≤ 2*N*K := by
  obtain ⟨s,hs,B,hBA,hB,hBS,hcard⟩ := extract_symmetric_sidon N hN A hA hSidon
  exact hcard.trans (Nat.mul_le_mul_left _ (hK s hs B (hBA.trans hA) hB hBS))

/-- The square-Sidon maximum has an actual maximizing root set. -/
lemma maximizing_roots (N : ℕ) :
    ∃ A ⊆ Icc 1 N, IsSidon (A.image (fun n => n^2) : Set ℕ) ∧
      A.card = maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by
  classical
  let S := (Icc 1 N).image (fun n : ℕ => n^2)
  let C := S.powerset.filter (fun B : Finset ℕ => IsSidon (B : Set ℕ))
  have hC : C.Nonempty := by
    refine ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),?_⟩⟩
    simp [IsSidon]
  obtain ⟨V,hV,hcard⟩ := exists_mem_eq_sup C hC Finset.card
  obtain ⟨hVS,hSidon⟩ := mem_filter.mp hV
  have hVS' : V ⊆ S := mem_powerset.mp hVS
  let A := (Icc 1 N).filter (fun n => n^2 ∈ V)
  have hAS : A.image (fun n => n^2) = V := by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hn).2
    · intro hx
      obtain ⟨n,hn,rfl⟩ := mem_image.mp (hVS' hx)
      exact mem_image.mpr ⟨n,mem_filter.mpr ⟨hn,hx⟩,rfl⟩
  refine ⟨A,filter_subset _ _,hAS.symm ▸ hSidon,?_⟩
  have hcardA : (A.image (fun n => n^2)).card = A.card :=
    card_image_of_injective _ (Nat.pow_left_injective (by norm_num : 2 ≠ 0))
  rw [hAS] at hcardA
  exact hcardA.symm.trans hcard.symm

/-- The unchanged quantified near-linear proposition, named only for this reduction. -/
def NearLinear : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (N : ℝ)^(1-ε) ≤ (maxSidonSubsetCard
      ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ)

/-- The same exponent target with a symmetric actual root set. -/
def SymmetricNearLinear : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∃ s ∈ Icc 1 (2*N), ∃ A ⊆ Icc 1 N, Symmetric s A ∧
      IsSidon (A.image (fun n => n^2) : Set ℕ) ∧ (N : ℝ)^(1-ε) ≤ A.card

theorem symmetric_of_near_linear (h : NearLinear) : SymmetricNearLinear := by
  intro ε hε
  have ht : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ)^(ε/2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < ε/2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).eventually_ge_atTop 2
  filter_upwards [h (ε/4) (by linarith),ht,eventually_ge_atTop 1] with N hM htwo hN
  obtain ⟨A,hA,hAS,hcardA⟩ := maximizing_roots N
  obtain ⟨s,hs,B,hBA,hB,hBS,hcard⟩ :=
    extract_symmetric_sidon N (by omega) A hA hAS
  refine ⟨s,hs,B,hBA.trans hA,hB,hBS,?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMA : (N : ℝ)^(1-ε/4) ≤ A.card := by simpa only [hcardA] using hM
  have hsq : ((N : ℝ)^(1-ε/4))^2 ≤ (A.card : ℝ)^2 := by
    nlinarith only [hMA,Real.rpow_nonneg hN0.le (1-ε/4),(Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)]
  have hscale : (N : ℝ)^(ε/2)*N*(N : ℝ)^(1-ε) = ((N : ℝ)^(1-ε/4))^2 := by
    calc
      _ = (N : ℝ)^(ε/2)*(N : ℝ)^((1 : ℝ))*(N : ℝ)^(1-ε) := by rw [Real.rpow_one]
      _ = (N : ℝ)^((ε/2+1)+(1-ε)) := by rw [Real.rpow_add hN0,Real.rpow_add hN0]
      _ = (N : ℝ)^((1-ε/4)*(2 : ℝ)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_mul hN0.le,Real.rpow_two]
  have hlo : 2*(N : ℝ)*(N : ℝ)^(1-ε) ≤ ((N : ℝ)^(1-ε/4))^2 := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htwo hN0.le) (Real.rpow_nonneg hN0.le _)
  have hcardR : (A.card : ℝ)^2 ≤ 2*N*(B.card : ℝ) := by exact_mod_cast hcard
  nlinarith only [hlo,hsq,hcardR,hN0]

theorem near_linear_of_symmetric (h : SymmetricNearLinear) : NearLinear := by
  intro ε hε
  filter_upwards [h ε hε] with N hN
  obtain ⟨s,hs,A,hA,hSym,hSidon,hcard⟩ := hN
  have hc : (A.image (fun n => n^2)).card = A.card :=
    card_image_of_injective _ (Nat.pow_left_injective (by norm_num : 2 ≠ 0))
  have hm : A.card ≤ maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by
    rw [← hc]
    exact le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image hA),hSidon⟩)
  exact hcard.trans (by exact_mod_cast hm)

/-- An equivalence, not a proof of either proposition. -/
theorem near_linear_iff_symmetric : NearLinear ↔ SymmetricNearLinear :=
  ⟨symmetric_of_near_linear,near_linear_of_symmetric⟩


/-- A real-valued finite power bound transfers with the expected exponent.
The bound for symmetric root sets remains an explicit hypothesis. -/
theorem symmetric_power_bound_transfers (N : ℕ) (hN : 0 < N) (C α : ℝ)
    (hK : ∀ s ∈ Icc 1 (2*N), ∀ B : Finset ℕ, B ⊆ Icc 1 N →
      Symmetric s B → IsSidon (B.image (fun n => n^2) : Set ℕ) →
        (B.card : ℝ) ≤ C*(N : ℝ)^α) :
    (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ)^2 ≤
      2*C*(N : ℝ)^(α+1) := by
  obtain ⟨A,hA,hAS,hcardA⟩ := maximizing_roots N
  obtain ⟨s,hs,B,hBA,hB,hBS,hcard⟩ := extract_symmetric_sidon N hN A hA hAS
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcardR : (A.card : ℝ)^2 ≤ 2*N*(B.card : ℝ) := by exact_mod_cast hcard
  have hBbound := hK s hs B (hBA.trans hA) hB hBS
  rw [← hcardA]
  calc
    _ ≤ 2*N*(B.card : ℝ) := hcardR
    _ ≤ 2*N*(C*(N : ℝ)^α) :=
      mul_le_mul_of_nonneg_left hBbound (by positivity)
    _ = _ := by rw [Real.rpow_add hN0,Real.rpow_one]; ring

/-- A fixed-power upper bound for ALL symmetric Sidon root sets would
negate the original conjecture. No such upper bound is proved in this file. -/
theorem not_near_linear_of_symmetric_power_upper (C α : ℝ) (hα : α < 1)
    (hupper : ∀ᶠ N : ℕ in atTop,
      ∀ s ∈ Icc 1 (2*N), ∀ B : Finset ℕ, B ⊆ Icc 1 N →
        Symmetric s B → IsSidon (B.image (fun n => n^2) : Set ℕ) →
          (B.card : ℝ) ≤ C*(N : ℝ)^α) : ¬ NearLinear := by
  intro h
  have hgap : (0 : ℝ) < (1-α)/2 := by linarith
  have hlarge : ∀ᶠ N : ℕ in atTop, 2*C < (N : ℝ)^((1-α)/2) :=
    ((tendsto_rpow_atTop hgap).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).eventually_gt_atTop (2*C)
  obtain ⟨N,hN,hup,hlo,hlarge⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hupper.and
      ((h ((1-α)/4) (by linarith)).and hlarge))).exists
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hup' := symmetric_power_bound_transfers N (by omega) C α hup
  have hsquare : ((N : ℝ)^(1-(1-α)/4))^2 ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ)^2 := by
    have hp := Real.rpow_nonneg hN0.le (1-(1-α)/4)
    have hm : (0 : ℝ) ≤ maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by positivity
    nlinarith only [hlo,hp,hm]
  have heq : ((N : ℝ)^(1-(1-α)/4))^2 =
      (N : ℝ)^((1-α)/2)*(N : ℝ)^(α+1) := by
    calc
      _ = (N : ℝ)^((1-(1-α)/4)*(2 : ℝ)) := by
        rw [Real.rpow_mul hN0.le,Real.rpow_two]
      _ = (N : ℝ)^(((1-α)/2)+(α+1)) := by congr 1; ring
      _ = _ := Real.rpow_add hN0 _ _
  have hstrict := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hN0 (α+1))
  rw [heq] at hsquare
  linarith only [hsquare,hup',hstrict]

end Erdos773.SymmetricSquareSidonReduction

#print axioms Erdos773.SymmetricSquareSidonReduction.extract_symmetric_sidon
#print axioms Erdos773.SymmetricSquareSidonReduction.uniform_symmetric_bound_transfers
#print axioms Erdos773.SymmetricSquareSidonReduction.near_linear_iff_symmetric

#print axioms Erdos773.SymmetricSquareSidonReduction.symmetric_power_bound_transfers
#print axioms Erdos773.SymmetricSquareSidonReduction.not_near_linear_of_symmetric_power_upper
