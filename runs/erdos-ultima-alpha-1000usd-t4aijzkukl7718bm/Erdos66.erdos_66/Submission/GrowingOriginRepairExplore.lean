import Submission.GrowingFieldSliceExplore

/-! Origin repair can be enlarged without changing the old field-plane slice.
These results concern actual finite sets in additive field planes. -/
namespace Erdos66GrowingOriginRepair
open Erdos66GrowingFieldSlice Erdos66OddExtensionFlatSet
  Erdos66FiniteField Erdos66OriginRepair Erdos66ParabolaRepair Erdos66Coset
open scoped Classical
set_option maxHeartbeats 2800000

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

omit [DecidableEq F] in
lemma exists_faithful_scalar_enlargement (T : Finset F) (m : ℕ)
    (hTm : T.card≤ m) (hm : m - T.card≤Fintype.card K-Fintype.card F) :
    ∃ Q : Finset K, Q.card=m ∧ T.image (algebraMap F K)⊆Q ∧
      ∀ x : F, algebraMap F K x∈Q ↔ x∈T := by
  let R := scalarRange (F:=F) (K:=K)
  have hc : (Finset.univ\R).card=Fintype.card K-Fintype.card F := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R),Finset.card_univ]
    exact congrArg (fun n ↦ Fintype.card K-n) scalarRange_card
  obtain ⟨D,hD,hcard⟩ := Finset.exists_subset_card_eq (s:=Finset.univ\R)
    (n:=m-T.card) (by rw [hc]; exact hm)
  let T' := T.image (algebraMap F K)
  have hTd : Disjoint T' D := by
    apply Finset.disjoint_left.mpr
    intro x hx hd
    exact (Finset.mem_sdiff.mp (hD hd)).2 (image_mem_scalarRange T hx)
  have hn (x : F) : algebraMap F K x∉D := by
    intro hx
    exact (Finset.mem_sdiff.mp (hD hx)).2 ((mem_scalarRange _).mpr ⟨x,rfl⟩)
  refine ⟨T'∪D,?_,Finset.subset_union_left,?_⟩
  · rw [Finset.card_union_of_disjoint hTd,Finset.card_image_of_injective _
      (algebraMap F K).injective,hcard]
    omega
  · intro x
    simp only [Finset.mem_union,hn x,or_false]
    exact Finset.mem_image.trans ⟨fun ⟨y,hy,he⟩ ↦
      (algebraMap F K).injective he ▸ hy,fun hx ↦ ⟨x,hx,rfl⟩⟩

omit [Fintype K] in
lemma mem_partialCurve (w : K) (Q : Finset K) (z : K×K) :
    z∈partialCurve w Q ↔ z.1∈Q ∧ z.2=z.1^2/w := by
  simp only [partialCurve,Finset.mem_image,Prod.ext_iff]
  constructor
  · rintro ⟨x,hx,hxz,hy⟩
    exact ⟨hxz ▸ hx,by simpa only [hxz] using hy.symm⟩
  · rintro ⟨hx,hy⟩
    exact ⟨z.1,hx,rfl,hy.symm⟩

omit [Fintype F] [Fintype K] in
lemma partialCurve_old_slice (w : F) (T : Finset F) (Q : Finset K)
    (hQ : ∀ x : F, algebraMap F K x∈Q ↔ x∈T) (z : F×F) :
    planeMap z∈partialCurve (algebraMap F K w) Q ↔ z∈partialCurve w T := by
  rw [mem_partialCurve,mem_partialCurve]
  dsimp only [planeMap]
  rw [hQ,←map_pow,←map_div₀,(algebraMap F K).injective.eq_iff]

lemma mem_neg_image {G : Type*} [AddCommGroup G] [DecidableEq G]
    (D : Finset G) (x : G) : x∈D.image Neg.neg ↔ -x∈D := by
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa only [neg_neg] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨-x,hx,neg_neg x⟩

omit [Fintype F] [Fintype K] in
lemma repairPoints_old_slice (w : F) (T : Finset F) (Q : Finset K)
    (hQ : ∀ x : F, algebraMap F K x∈Q ↔ x∈T) (z : F×F) :
    planeMap z∈repairPoints (algebraMap F K w) Q ↔ z∈repairPoints w T := by
  simp only [repairPoints,Finset.mem_union,mem_neg_image]
  have he : -(planeMap (K:=K) z)=planeMap (-z) := by simp [planeMap]
  rw [he,partialCurve_old_slice w T Q hQ z,partialCurve_old_slice w T Q hQ (-z)]

/-- The enlarged finite set has growing mean and an exact old slice,
INCLUDING its old origin repair. The field-size and repair-capacity
conditions are kept explicit. -/
theorem exists_growing_repaired_slice (hd : Odd (Module.finrank F K))
    (hK : ringChar K≠2) (U : Finset F) (hne : U.Nonempty)
    (hU : ∀ u∈U, u≠0) (hUU : ∀ u∈U, ∀ v∈U, u+v≠0)
    (w : F) (hw : w≠0) (hwU : w∉U) (hnwU : -w∉U)
    (T : Finset F) (hT : (0:F)∉T)
    (W S : Finset K) (hS : ∀ x∈W, ∀ y∈W, x+y∈S)
    (hsize : 2*(Fintype.card F*W.card+S.card)<Fintype.card K)
    (hTm : T.card≤(U.card+W.card)^2/2)
    (hcapacity : (U.card+W.card)^2/2-T.card≤Fintype.card K-Fintype.card F) :
    ∃ (B : Finset (K×K)) (E : ℝ),
      (∀ z : F×F, planeMap z∈B ↔ z∈parabolaSet U∪repairPoints w T) ∧
      0≤E ∧ E^2≤8*S.card*(W.card:ℝ)^2 ∧
      pairCount B B 0=1+2*((U.card+W.card)^2/2) ∧
      ∀ z : K×K, |(pairCount B B z:ℝ)-((U.card:ℝ)+W.card)^2| ≤
        (∑ a : F, |(charFiber U a:ℝ)|)+E+2*(U.card:ℝ)*W.card+
          10*((U.card:ℝ)+W.card)+9 := by
  obtain ⟨Z,E,hsub,hcard,hscalar,hZ,hZZ,hslice,hE,hE2,hbudget,hcounts⟩ :=
    exists_growing_slice_parameters hd hK U hne hU hUU W S hS hsize
  obtain ⟨Q,hQcard,hQsub,hQ⟩ := exists_faithful_scalar_enlargement T
    ((U.card+W.card)^2/2) hTm hcapacity
  let f := algebraMap F K
  have hw' : f w≠0 := (map_ne_zero f).mpr hw
  have hwZ : f w∉Z := fun hz ↦ hwU ((hscalar w).mp hz)
  have hnwZ : -(f w)∉Z := by
    rw [←map_neg]
    exact fun hz ↦ hnwU ((hscalar (-w)).mp hz)
  have hQ0 : (0:K)∉Q := by
    intro hz
    apply hT
    exact (hQ 0).mp (by simpa only [map_zero] using hz)
  have hZne : Z.Nonempty := (hne.image f).mono hsub
  let B := parabolaSet Z∪repairPoints (f w) Q
  obtain ⟨hzero,hother⟩ := parabola_origin_repair hK Z hZ hZZ hZne
    (f w) hw' hwZ hnwZ Q hQ0
  have hzero' : pairCount B B 0=1+2*((U.card+W.card)^2/2) := by
    simpa only [hQcard] using hzero
  refine ⟨B,E,?_,hE,hE2,hzero',?_⟩
  · intro z
    simp only [B,f,Finset.mem_union,hslice z,
      repairPoints_old_slice w T Q hQ z]
  · intro z
    by_cases hz : z=0
    · subst z
      rw [hzero']
      have hm₁ : (U.card+W.card)^2 ≤ 1+2*((U.card+W.card)^2/2) := by omega
      have hm₂ : 1+2*((U.card+W.card)^2/2) ≤ (U.card+W.card)^2+1 := by omega
      have hm₁' : ((U.card:ℝ)+W.card)^2 ≤
          (1+2*((U.card+W.card)^2/2):ℕ) := by exact_mod_cast hm₁
      have hm₂' : ((1+2*((U.card+W.card)^2/2):ℕ):ℝ) ≤
          ((U.card:ℝ)+W.card)^2+1 := by exact_mod_cast hm₂
      have he : |((1+2*((U.card+W.card)^2/2):ℕ):ℝ)-
          ((U.card:ℝ)+W.card)^2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hp : 0 ≤ ∑ a : F, |(charFiber U a:ℝ)| :=
        Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
      have hu : (0:ℝ)≤U.card := Nat.cast_nonneg _
      have hv : (0:ℝ)≤W.card := Nat.cast_nonneg _
      nlinarith only [he,hp,hE,hu,hv,mul_nonneg hu hv]
    · obtain ⟨hl,hu⟩ := hother z hz
      have hl' : (pairCount (parabolaSet Z) (parabolaSet Z) z:ℝ)≤pairCount B B z :=
        by exact_mod_cast hl
      have hu' : (pairCount B B z:ℝ) ≤
          pairCount (parabolaSet Z) (parabolaSet Z) z+8*((U.card:ℝ)+W.card)+8 := by
        rw [hcard] at hu
        exact_mod_cast hu
      have hc := hcounts z hz
      rw [abs_le] at hc ⊢
      constructor <;> linarith

end Erdos66GrowingOriginRepair
