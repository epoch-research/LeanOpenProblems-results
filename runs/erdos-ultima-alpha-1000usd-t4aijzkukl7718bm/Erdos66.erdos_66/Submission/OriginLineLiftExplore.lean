import Submission.LineRecoloringExplore

/-! Through-origin line lifts with an explicit recoloring. Old color
membership on the zero slice is retained, but old representation counts
on that slice need not be: the exact origin correction is displayed. -/
namespace Erdos66OriginLineLift
open Erdos66LineRecoloring Erdos66OriginRepair Erdos66DisjointPaletteAssembly
  Erdos66AffineLineAssembly
open scoped Classical
set_option maxHeartbeats 2500000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def originLine (u : F) : Finset (F×F) :=
  Finset.univ.image (fun x : F ↦ (x,u*x))

lemma mem_originLine (u : F) (z : F×F) : z∈originLine u ↔ z.2=u*z.1 := by
  simp only [originLine,Finset.mem_image,Finset.mem_univ,true_and,Prod.ext_iff]
  constructor
  · rintro ⟨x,rfl,he⟩
    exact he.symm
  · intro h
    exact ⟨z.1,rfl,h.symm⟩

lemma originLine_card (u : F) : (originLine u).card=Fintype.card F := by
  rw [originLine,Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)]
  simp

lemma originLine_pair_filter (u v x y : F) :
    pairCount (originLine u) (originLine v) (x,y)=
      (Finset.univ.filter (fun z : F ↦ (u-v)*z=y-v*x)).card := by
  unfold pairCount
  rw [show originLine u=Finset.univ.image (fun z : F ↦ (z,u*z)) by rfl,
    Finset.filter_image,Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)]
  congr 1
  apply Finset.filter_congr
  intro z hz
  rw [mem_originLine]
  dsimp
  constructor <;> intro h <;> linear_combination -h

lemma originLine_pair_different (u v x y : F) (huv : u≠v) :
    pairCount (originLine u) (originLine v) (x,y)=1 := by
  rw [originLine_pair_filter]
  have hne : u-v≠0 := sub_ne_zero.mpr huv
  have hf : Finset.univ.filter (fun z : F ↦ (u-v)*z=y-v*x)={(y-v*x)/(u-v)} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    rw [eq_div_iff hne]
    constructor <;> intro h <;> simpa only [mul_comm] using h
  rw [hf,Finset.card_singleton]

lemma originLine_pair_same (u x y : F) :
    pairCount (originLine u) (originLine u) (x,y)=
      if y=u*x then Fintype.card F else 0 := by
  rw [originLine_pair_filter]
  have he : (0:F)=y-u*x ↔ y=u*x := by
    constructor <;> intro h <;> linear_combination -h
  simp only [sub_self,zero_mul,he]
  split_ifs with h <;> simp [h]

lemma concurrent_nonzero_card (x y : F) (hz : (x,y)≠0) :
    (Finset.univ.filter (fun u : F ↦ y=u*x)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hu := (Finset.mem_filter.mp hu).2
  have hv := (Finset.mem_filter.mp hv).2
  by_cases hx : x=0
  · have hy : y=0 := by simpa only [hx,mul_zero] using hu
    exact False.elim (hz (Prod.ext hx hy))
  · exact mul_right_cancel₀ hx (hu.symm.trans hv)

noncomputable def weightedCount (K : F → F → ℝ) (x y : F) : ℝ :=
  ∑ u : F, ∑ v : F, K u v*(pairCount (originLine u) (originLine v) (x,y):ℝ)

lemma weighted_identity (K : F → F → ℝ) (x y : F) :
    weightedCount K x y-(∑ u : F, ∑ v : F, K u v)=
      (Fintype.card F:ℝ)*(∑ u : F, if y=u*x then K u u else 0)-∑ u : F, K u u := by
  unfold weightedCount
  rw [←Finset.sum_sub_distrib]
  have he (u : F) :
      (∑ v : F, K u v*(pairCount (originLine u) (originLine v) (x,y):ℝ))-
        (∑ v : F, K u v)=
        (Fintype.card F:ℝ)*(if y=u*x then K u u else 0)-K u u := by
    rw [←Finset.sum_sub_distrib]
    calc
      _ = ∑ v : F, if u=v then
          (Fintype.card F:ℝ)*(if y=u*x then K u u else 0)-K u u else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases huv : u=v
        · subst v
          rw [if_pos rfl,originLine_pair_same]
          split_ifs <;> push_cast <;> ring
        · rw [if_neg huv,originLine_pair_different u v x y huv]
          norm_num
      _ = _ := by simp
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]

lemma weighted_nonzero_error (K : F → F → ℝ) (g : ℝ) (hg : 0≤g)
    (hK : ∀ u, 0≤K u u ∧ K u u≤g) (x y : F) (hz : (x,y)≠0) :
    |weightedCount K x y-(∑ u : F, ∑ v : F, K u v)|≤Fintype.card F*g := by
  rw [weighted_identity]
  have h₀ : 0≤∑ u : F, K u u := Finset.sum_nonneg (fun u _ ↦ (hK u).1)
  have h₁ : (∑ u : F, K u u)≤Fintype.card F*g := by
    calc
      _ ≤ ∑ _u : F, g := Finset.sum_le_sum (fun u _ ↦ (hK u).2)
      _ = _ := by simp
  have h₂ : 0≤∑ u : F, if y=u*x then K u u else 0 := by
    apply Finset.sum_nonneg
    intro u hu
    split_ifs
    · exact (hK u).1
    · rfl
  have h₃ : (∑ u : F, if y=u*x then K u u else 0)≤g := by
    rw [←Finset.sum_filter]
    calc
      _ ≤ ∑ _u∈Finset.univ.filter (fun u : F ↦ y=u*x), g :=
        Finset.sum_le_sum (fun u _ ↦ (hK u).2)
      _ ≤ 1*g := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast concurrent_nonzero_card x y hz) hg
      _ = _ := one_mul _
  have hp : (0:ℝ)≤Fintype.card F := by positivity
  rw [abs_le]
  constructor <;> nlinarith

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def originLift (A : F → Finset G) : Finset (G×(F×F)) :=
  assembly A originLine

omit [AddCommGroup G] in
lemma mem_originLift (A : F → Finset G) (a : G) (x y : F) :
    (a,(x,y))∈originLift A ↔ ∃ u : F, a∈A u ∧ y=u*x := by
  simp only [originLift,assembly,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_product,mem_originLine]

omit [AddCommGroup G] in
lemma originLift_eq_recolored (A : F → Finset G) (α : F) :
    originLift A=Finset.univ.biUnion (recolored A 0 α) := by
  ext ⟨a,x,y⟩
  rw [mem_originLift,union_recolored_membership]
  simp only [zero_mul,add_zero]

lemma originLift_card (A : F → Finset G)
    (hA : Pairwise (fun u v ↦ Disjoint (A u) (A v))) :
    (originLift A).card=Fintype.card F*(oldSet A).card := by
  rw [originLift_eq_recolored A 1]
  exact union_recolored_card A hA 0 1 one_ne_zero

lemma originLift_pairCount (A : F → Finset G)
    (hA : Pairwise (fun u v ↦ Disjoint (A u) (A v))) (t : G) (x y : F) :
    (pairCount (originLift A) (originLift A) (t,(x,y)):ℝ)=
      weightedCount (fun u v ↦ (pairCount (A u) (A v) t:ℝ)) x y := by
  rw [originLift,assembly_pairCount A hA]
  simp only [Nat.cast_sum,Nat.cast_mul,weightedCount]

/-- Unlike the translated-line lift, the nonzero-target error is q*g. -/
theorem originLift_nonzero_error (A : F → Finset G)
    (hA : Pairwise (fun u v ↦ Disjoint (A u) (A v))) (t : G) (g : ℝ)
    (hg : 0≤g) (hcap : ∀ u, (pairCount (A u) (A u) t:ℝ)≤g)
    (x y : F) (hz : (x,y)≠0) :
    |(pairCount (originLift A) (originLift A) (t,(x,y)):ℝ)-
      pairCount (oldSet A) (oldSet A) t|≤Fintype.card F*g := by
  rw [originLift_pairCount A hA,oldSet_pairCount A hA]
  push_cast
  exact weighted_nonzero_error (fun u v ↦ (pairCount (A u) (A v) t:ℝ)) g hg
    (fun u ↦ ⟨Nat.cast_nonneg (pairCount (A u) (A u) t),hcap u⟩) x y hz

/-- Crucial caveat: preserving zero-slice MEMBERSHIP does not preserve its
representation counts in this finite product group. -/
theorem originLift_zero_count (A : F → Finset G)
    (hA : Pairwise (fun u v ↦ Disjoint (A u) (A v))) (t : G) :
    (pairCount (originLift A) (originLift A) (t,((0:F),0)):ℝ)=
      (pairCount (oldSet A) (oldSet A) t:ℝ)+
        ((Fintype.card F:ℝ)-1)*(∑ u : F, (pairCount (A u) (A u) t:ℝ)) := by
  rw [originLift_pairCount A hA,oldSet_pairCount A hA]
  push_cast
  have hh := weighted_identity (fun u v ↦ (pairCount (A u) (A v) t:ℝ)) 0 0
  simp only [mul_zero,ite_true] at hh
  linarith

/-- The global self-convolution mean is unchanged, despite the origin
correction. This is still a finite-group identity, with no carry assertion. -/
theorem originLift_mean_preserved [Fintype G] (A : F → Finset G)
    (hA : Pairwise (fun u v ↦ Disjoint (A u) (A v))) :
    ((originLift A).card:ℝ)^2/Fintype.card (G×(F×F))=
      ((oldSet A).card:ℝ)^2/Fintype.card G := by
  rw [originLift_card A hA]
  simp only [Nat.cast_mul,Fintype.card_prod]
  have hF : (Fintype.card F:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end Erdos66OriginLineLift
