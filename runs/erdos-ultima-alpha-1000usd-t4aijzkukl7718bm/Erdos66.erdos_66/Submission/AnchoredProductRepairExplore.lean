import Submission.ProductProjectionRepairExplore

/-! Anchoring the repair in the old plane preserves its entire coordinate
slice and the representation counts there. No natural-number embedding is
asserted. -/
namespace Erdos66AnchoredProductRepair
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66SharedParameterSet
  Erdos66ProductProjectionRepair
open scoped Classical
set_option maxHeartbeats 1200000

section Slice
variable {G H : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H]

/-- If cancellation of the new coordinate only occurs in the old slice,
then all old-slice representation counts are preserved. -/
lemma pairCount_slice (A : Finset (G × H)) (B : Finset G)
    (hslice : ∀ x, (x,0)∈A ↔ x∈B)
    (hcancel : ∀ x∈A, ∀ y∈A, x.2+y.2=0 → x.2=0) (z : G) :
    pairCount A A (z,0) = pairCount B B z := by
  unfold pairCount
  apply Finset.card_bij (fun x _ ↦ x.1)
  · intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_filter.mp hx
    have hx0 : x.2=0 := hcancel x hx ((z,0)-x) hy (by simp)
    have he : x=(x.1,0) := Prod.ext rfl hx0
    rw [he] at hx hy
    exact Finset.mem_filter.mpr ⟨(hslice _).mp hx,(hslice _).mp (by simpa using hy)⟩
  · intro x hx y hy hxy
    have hx0 : x.2=0 := hcancel x (Finset.mem_filter.mp hx).1 ((z,0)-x)
      (Finset.mem_filter.mp hx).2 (by simp)
    have hy0 : y.2=0 := hcancel y (Finset.mem_filter.mp hy).1 ((z,0)-y)
      (Finset.mem_filter.mp hy).2 (by simp)
    exact Prod.ext hxy (hx0.trans hy0.symm)
  · intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_filter.mp hx
    refine ⟨(x,0),Finset.mem_filter.mpr ⟨(hslice _).mpr hx,?_⟩,rfl⟩
    simpa using (hslice _).mpr hy

lemma anchored_mem (D : Finset G) (z : G × H) :
    z∈D ×ˢ ({0} : Finset H) ↔ z.1∈D ∧ z.2=0 := by simp only [Finset.mem_product,Finset.mem_singleton]

lemma anchored_symmetric (D : Finset G) (hD : ∀ x∈D, -x∈D) :
    ∀ z∈D ×ˢ ({0} : Finset H), -z∈D ×ˢ ({0} : Finset H) := by
  intro z hz
  obtain ⟨hz,hz0⟩ := (anchored_mem D z).mp hz
  exact (anchored_mem D (-z)).mpr ⟨hD z.1 hz,by simpa using congrArg Neg.neg hz0⟩

lemma anchored_fst_inj (D : Finset G) :
    Set.InjOn Prod.fst ((D ×ˢ ({0} : Finset H) : Finset (G × H)) : Set (G × H)) := by
  intro x hx y hy he
  change x∈D ×ˢ ({0} : Finset H) at hx
  change y∈D ×ˢ ({0} : Finset H) at hy
  exact Prod.ext he (((anchored_mem D x).mp hx).2.trans ((anchored_mem D y).mp hy).2.symm)

lemma anchored_self_count (D : Finset G) (z : G) (w : H) :
    pairCount (D ×ˢ ({0} : Finset H)) (D ×ˢ ({0} : Finset H)) (z,w) =
      if w=0 then pairCount D D z else 0 := by
  rw [pairCount_product]
  by_cases hw : w=0
  · subst w; simp [pairCount,Finset.filter_singleton]
  · simp [pairCount,hw,Finset.filter_singleton]

end Slice

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [DecidableEq K]

lemma sharedSet_slice (h : ℕ) (u : ℕ → F) (v : ℕ → K) (x : F × F) :
    (x,0)∈sharedSet h u v ↔ x∈parabolaSet ((Finset.range h).image u) := by
  simp only [sharedSet,Finset.mem_biUnion,productCurve,Finset.mem_product]
  simp only [show ∀ v : K, (0 : K × K)∈curve v from fun v ↦ by simp [mem_curve],and_true]
  rw [parabolaSet_eq_biUnion]
  simp only [Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨i,hi,hx⟩
    exact ⟨u i,⟨i,hi,rfl⟩,hx⟩
  · rintro ⟨a,⟨i,hi,rfl⟩,hx⟩
    exact ⟨i,hi,hx⟩

lemma curves_cancel_only_at_zero {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u+v ≠ 0) {x y : K × K} (hx : x∈curve u) (hy : y∈curve v)
    (he : x+y=0) : x=0 := by
  have hx' : x∈curve (-v) := (eq_neg_of_add_eq_zero_left he).symm ▸ neg_mem_curve v hy
  apply curve_intersection hu (neg_ne_zero.mpr hv) _ hx hx'
  intro he
  apply huv
  rw [he,neg_add_cancel]

lemma sharedSet_cancel_new (h : ℕ) (u : ℕ → F) (v : ℕ → K)
    (hv : ∀ i<h, v i ≠ 0) (hvv : ∀ i<h, ∀ j<h, v i+v j ≠ 0)
    (x : (F × F) × (K × K)) (hx : x∈sharedSet h u v)
    (y : (F × F) × (K × K)) (hy : y∈sharedSet h u v)
    (he : x.2+y.2=0) : x.2=0 := by
  obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨j,hj,hyj⟩ := Finset.mem_biUnion.mp hy
  exact curves_cancel_only_at_zero (hv i (Finset.mem_range.mp hi)) (hv j (Finset.mem_range.mp hj))
    (hvv i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj))
    (Finset.mem_product.mp hxi).2 (Finset.mem_product.mp hyj).2 he

noncomputable def anchoredSet (h : ℕ) (u : ℕ → F) (v : ℕ → K) (D : Finset (F × F)) :
    Finset ((F × F) × (K × K)) := sharedSet h u v ∪ (D ×ˢ {0})

lemma anchoredSet_slice (h : ℕ) (u : ℕ → F) (v : ℕ → K) (D : Finset (F × F)) (x : F × F) :
    (x,0)∈anchoredSet h u v D ↔ x∈parabolaSet ((Finset.range h).image u) ∪ D := by
  simp only [anchoredSet,Finset.mem_union,sharedSet_slice,Finset.mem_product,Finset.mem_singleton,
    and_true]

lemma anchoredSet_cancel_new (h : ℕ) (u : ℕ → F) (v : ℕ → K) (D : Finset (F × F))
    (hv : ∀ i<h, v i ≠ 0) (hvv : ∀ i<h, ∀ j<h, v i+v j ≠ 0)
    (x : (F × F) × (K × K)) (hx : x∈anchoredSet h u v D)
    (y : (F × F) × (K × K)) (hy : y∈anchoredSet h u v D)
    (he : x.2+y.2=0) : x.2=0 := by
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact sharedSet_cancel_new h u v hv hvv x hx y hy he
    · have hy0 := ((anchored_mem D y).mp hy).2
      simpa only [hy0,add_zero] using he
  · exact ((anchored_mem D x).mp hx).2

/-- Both membership and representation counts in the old slice are exactly
unchanged, even though the repair lacks an injective new projection. -/
theorem anchoredSet_preserves_counts (h : ℕ) (u : ℕ → F) (v : ℕ → K) (D : Finset (F × F))
    (hv : ∀ i<h, v i ≠ 0) (hvv : ∀ i<h, ∀ j<h, v i+v j ≠ 0) (z : F × F) :
    pairCount (anchoredSet h u v D) (anchoredSet h u v D) (z,0) =
      pairCount (parabolaSet ((Finset.range h).image u) ∪ D)
        (parabolaSet ((Finset.range h).image u) ∪ D) z :=
  pairCount_slice _ _ (anchoredSet_slice h u v D) (anchoredSet_cancel_new h u v D hv hvv) z

lemma anchored_disjoint (h : ℕ) (u : ℕ → F) (v : ℕ → K) (D : Finset (F × F))
    (hD : Disjoint (parabolaSet ((Finset.range h).image u)) D) :
    Disjoint (sharedSet h u v) (D ×ˢ ({0} : Finset (K × K))) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzd
  exact Finset.disjoint_left.mp hD
    (sharedSet_fst_subset h u v (Finset.mem_image.mpr ⟨z,hz,rfl⟩))
    ((anchored_mem D z).mp hzd).1

lemma anchored_cross_old_zero (h : ℕ) (u : ℕ → F) (v : ℕ → K) (D : Finset (F × F))
    (hdis : Disjoint (parabolaSet ((Finset.range h).image u)) D)
    (hsym : ∀ x∈D, -x∈D) (z : K × K) :
    pairCount (D ×ˢ ({0} : Finset (K × K))) (sharedSet h u v) (0,z) = 0 := by
  rw [pairCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro x hx hy
  have hxD := ((anchored_mem D x).mp hx).1
  have hyP := sharedSet_fst_subset h u v (Finset.mem_image.mpr ⟨(0,z)-x,hy,rfl⟩)
  simp only [Prod.fst_sub,zero_sub] at hyP
  exact Finset.disjoint_left.mp hdis hyP (hsym x.1 hxD)

/-- The same O(h) repair cost holds for an anchored old-plane repair. -/
theorem anchored_repair_bound (h : ℕ) (u : ℕ → F) (v : ℕ → K)
    (hF : ringChar F ≠ 2) (hu : ∀ i<h, u i ≠ 0)
    (w : F) (hw : w ≠ 0) (D : Finset (F × F))
    (hdis : Disjoint (parabolaSet ((Finset.range h).image u)) D)
    (hsym : ∀ x∈D, -x∈D) (hsub : D ⊆ parabolaSet {w,-w})
    (z : (F × F) × (K × K)) (hz : z ≠ 0) :
    pairCount (sharedSet h u v) (sharedSet h u v) z ≤
      pairCount (anchoredSet h u v D) (anchoredSet h u v D) z ∧
    pairCount (anchoredSet h u v D) (anchoredSet h u v D) z ≤
      pairCount (sharedSet h u v) (sharedSet h u v) z+8*h+8 := by
  have hU : ∀ a∈(Finset.range h).image u, a ≠ 0 := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact hu i (Finset.mem_range.mp hi)
  have hW : ∀ a∈({w,-w} : Finset F), a ≠ 0 := by simpa using And.intro hw (neg_ne_zero.mpr hw)
  have hproj : (D ×ˢ ({0} : Finset (K × K))).image Prod.fst ⊆ parabolaSet {w,-w} := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact hsub ((anchored_mem D z).mp hz).1
  have hc : pairCount (D ×ˢ ({0} : Finset (K × K))) (sharedSet h u v) z ≤ 4*h := by
    by_cases hz1 : z.1=0
    · have he : z=(0,z.2) := Prod.ext hz1 rfl
      rw [he,anchored_cross_old_zero h u v D hdis hsym]
      omega
    · have he := pairCount_le_of_projection (AddMonoidHom.fst (F × F) (K × K)) _ _
        (anchored_fst_inj D) _ _ hproj (sharedSet_fst_subset h u v) z
      exact he.trans (by simpa using (small_union_curve_bound hF _ _ hW hU 2 h Finset.card_le_two
        (Finset.card_image_le.trans_eq (Finset.card_range _)) z.1 hz1))
  have hd : pairCount (D ×ˢ ({0} : Finset (K × K))) (D ×ˢ ({0} : Finset (K × K))) z ≤ 8 := by
    by_cases hz2 : z.2=0
    · have hz1 : z.1 ≠ 0 := fun he ↦ hz (Prod.ext he hz2)
      rw [show z=(z.1,z.2) from rfl,anchored_self_count,if_pos hz2]
      exact (pairCount_mono hsub hsub _).trans (by simpa using
        (small_union_curve_bound hF _ _ hW hW 2 2 Finset.card_le_two Finset.card_le_two z.1 hz1))
    · rw [show z=(z.1,z.2) from rfl,anchored_self_count,if_neg hz2]
      omega
  rw [anchoredSet,pairCount_union_self _ _ _ (anchored_disjoint h u v D hdis)]
  constructor <;> omega

end Erdos66AnchoredProductRepair
