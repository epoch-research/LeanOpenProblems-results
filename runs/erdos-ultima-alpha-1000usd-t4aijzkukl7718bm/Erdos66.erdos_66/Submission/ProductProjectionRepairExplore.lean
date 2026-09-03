import Submission.SharedParameterSetExplore

/-! An origin repair in a product of two field planes, controlled by
injective coordinate projections. No integer-prefix assertion is made. -/
namespace Erdos66ProductProjectionRepair
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66SharedParameterSet
open scoped Classical
set_option maxHeartbeats 1000000

section Projection
variable {G H : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H]

lemma pairCount_image_le (π : G →+ H) (A B : Finset G) (hπ : Set.InjOn π A) (z : G) :
    pairCount A B z ≤ pairCount (A.image π) (B.image π) (π z) := by
  let T := A.filter (fun a ↦ z-a∈B)
  have ht : (T.image π) ⊆ (A.image π).filter (fun a ↦ π z-a∈B.image π) := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,?_⟩
    exact Finset.mem_image.mpr ⟨z-x,hzx,map_sub π z x⟩
  calc
    pairCount A B z = T.card := rfl
    _ = (T.image π).card := (Finset.card_image_of_injOn (fun x hx y hy hxy ↦
      hπ (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)).symm
    _ ≤ _ := Finset.card_le_card ht

lemma pairCount_le_of_projection (π : G →+ H) (A B : Finset G)
    (hπ : Set.InjOn π A) (C D : Finset H)
    (hA : A.image π ⊆ C) (hB : B.image π ⊆ D) (z : G) :
    pairCount A B z ≤ pairCount C D (π z) :=
  (pairCount_image_le π A B hπ z).trans (pairCount_mono hA hB _)
end Projection

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [DecidableEq K]

lemma sharedSet_fst_subset (h : ℕ) (u : ℕ → F) (v : ℕ → K) :
    (sharedSet h u v).image Prod.fst ⊆ parabolaSet ((Finset.range h).image u) := by
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
  rw [parabolaSet_eq_biUnion]
  exact Finset.mem_biUnion.mpr ⟨u i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,(Finset.mem_product.mp hzi).1⟩

lemma sharedSet_snd_subset (h : ℕ) (u : ℕ → F) (v : ℕ → K) :
    (sharedSet h u v).image Prod.snd ⊆ parabolaSet ((Finset.range h).image v) := by
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
  rw [parabolaSet_eq_biUnion]
  exact Finset.mem_biUnion.mpr ⟨v i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,(Finset.mem_product.mp hzi).2⟩

lemma small_union_curve_bound {L : Type*} [Field L] [Fintype L] [DecidableEq L]
    (hL : ringChar L ≠ 2) (U V : Finset L)
    (hU : ∀ u∈U, u ≠ 0) (hV : ∀ v∈V, v ≠ 0)
    (a b : ℕ) (ha : U.card ≤ a) (hb : V.card ≤ b)
    (z : L × L) (hz : z ≠ 0) :
    pairCount (parabolaSet U) (parabolaSet V) z ≤ 2*a*b := by
  exact (parabolaSet_pairCount_le hL U V hU hV z hz).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 ha) hb)

lemma repair_cross_bound (h : ℕ) (u : ℕ → F) (v : ℕ → K)
    (hF : ringChar F ≠ 2) (hK : ringChar K ≠ 2)
    (hu : ∀ i<h, u i ≠ 0) (hv : ∀ i<h, v i ≠ 0)
    (wF : F) (wK : K) (hwF : wF ≠ 0) (hwK : wK ≠ 0)
    (D : Finset ((F × F) × (K × K)))
    (hD₁ : Set.InjOn Prod.fst (D : Set ((F × F) × (K × K)))) (hD₂ : Set.InjOn Prod.snd (D : Set ((F × F) × (K × K))))
    (hs₁ : D.image Prod.fst ⊆ parabolaSet {wF,-wF})
    (hs₂ : D.image Prod.snd ⊆ parabolaSet {wK,-wK})
    (z : (F × F) × (K × K)) (hz : z ≠ 0) :
    pairCount D (sharedSet h u v) z ≤ 4*h := by
  have hUF : ∀ a∈(Finset.range h).image u, a ≠ 0 := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact hu i (Finset.mem_range.mp hi)
  have hUK : ∀ a∈(Finset.range h).image v, a ≠ 0 := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact hv i (Finset.mem_range.mp hi)
  have hWF : ∀ a∈({wF,-wF} : Finset F), a ≠ 0 := by simpa using And.intro hwF (neg_ne_zero.mpr hwF)
  have hWK : ∀ a∈({wK,-wK} : Finset K), a ≠ 0 := by simpa using And.intro hwK (neg_ne_zero.mpr hwK)
  by_cases hz₁ : z.1 ≠ 0
  · have he := pairCount_le_of_projection (AddMonoidHom.fst (F × F) (K × K)) D (sharedSet h u v)
      hD₁ (parabolaSet {wF,-wF}) (parabolaSet ((Finset.range h).image u)) hs₁
      (sharedSet_fst_subset h u v) z
    exact he.trans (by simpa using (small_union_curve_bound hF _ _ hWF hUF 2 h Finset.card_le_two
      (Finset.card_image_le.trans_eq (Finset.card_range _)) z.1 hz₁))
  · have hz₂ : z.2 ≠ 0 := fun h ↦ hz (Prod.ext (not_ne_iff.mp hz₁) h)
    have he := pairCount_le_of_projection (AddMonoidHom.snd (F × F) (K × K)) D (sharedSet h u v)
      hD₂ (parabolaSet {wK,-wK}) (parabolaSet ((Finset.range h).image v)) hs₂
      (sharedSet_snd_subset h u v) z
    exact he.trans (by simpa using (small_union_curve_bound hK _ _ hWK hUK 2 h Finset.card_le_two
      (Finset.card_image_le.trans_eq (Finset.card_range _)) z.2 hz₂))

lemma repair_self_bound (hF : ringChar F ≠ 2) (hK : ringChar K ≠ 2)
    (wF : F) (wK : K) (hwF : wF ≠ 0) (hwK : wK ≠ 0)
    (D : Finset ((F × F) × (K × K)))
    (hD₁ : Set.InjOn Prod.fst (D : Set ((F × F) × (K × K)))) (hD₂ : Set.InjOn Prod.snd (D : Set ((F × F) × (K × K))))
    (hs₁ : D.image Prod.fst ⊆ parabolaSet {wF,-wF})
    (hs₂ : D.image Prod.snd ⊆ parabolaSet {wK,-wK})
    (z : (F × F) × (K × K)) (hz : z ≠ 0) : pairCount D D z ≤ 8 := by
  have hWF : ∀ a∈({wF,-wF} : Finset F), a ≠ 0 := by simpa using And.intro hwF (neg_ne_zero.mpr hwF)
  have hWK : ∀ a∈({wK,-wK} : Finset K), a ≠ 0 := by simpa using And.intro hwK (neg_ne_zero.mpr hwK)
  by_cases hz₁ : z.1 ≠ 0
  · have he := pairCount_le_of_projection (AddMonoidHom.fst (F × F) (K × K)) D D hD₁
      (parabolaSet {wF,-wF}) (parabolaSet {wF,-wF}) hs₁ hs₁ z
    exact he.trans (by simpa using (small_union_curve_bound hF _ _ hWF hWF 2 2
      Finset.card_le_two Finset.card_le_two z.1 hz₁))
  · have hz₂ : z.2 ≠ 0 := fun h ↦ hz (Prod.ext (not_ne_iff.mp hz₁) h)
    have he := pairCount_le_of_projection (AddMonoidHom.snd (F × F) (K × K)) D D hD₂
      (parabolaSet {wK,-wK}) (parabolaSet {wK,-wK}) hs₂ hs₂ z
    exact he.trans (by simpa using (small_union_curve_bound hK _ _ hWK hWK 2 2
      Finset.card_le_two Finset.card_le_two z.2 hz₂))

/-- Any symmetric disjoint repair with these projection properties has the
required origin mass and O(h) collateral cost. -/
theorem product_origin_repair (h : ℕ) (hh : 0<h) (u : ℕ → F) (v : ℕ → K)
    (hF : ringChar F ≠ 2) (hK : ringChar K ≠ 2)
    (hu : ∀ i<h, u i ≠ 0) (hv : ∀ i<h, v i ≠ 0)
    (huu : ∀ i<h, ∀ j<h, u i+u j ≠ 0) (hvv : ∀ i<h, ∀ j<h, v i+v j ≠ 0)
    (hiu : Set.InjOn u (Finset.range h)) (hiv : Set.InjOn v (Finset.range h))
    (wF : F) (wK : K) (hwF : wF ≠ 0) (hwK : wK ≠ 0)
    (D : Finset ((F × F) × (K × K)))
    (hdis : Disjoint (sharedSet h u v) D) (hsym : ∀ x∈D, -x∈D)
    (hD₁ : Set.InjOn Prod.fst (D : Set ((F × F) × (K × K)))) (hD₂ : Set.InjOn Prod.snd (D : Set ((F × F) × (K × K))))
    (hs₁ : D.image Prod.fst ⊆ parabolaSet {wF,-wF})
    (hs₂ : D.image Prod.snd ⊆ parabolaSet {wK,-wK}) :
    pairCount (sharedSet h u v ∪ D) (sharedSet h u v ∪ D) 0 = 1+D.card ∧
    ∀ z, z ≠ 0 →
      pairCount (sharedSet h u v) (sharedSet h u v) z ≤
        pairCount (sharedSet h u v ∪ D) (sharedSet h u v ∪ D) z ∧
      pairCount (sharedSet h u v ∪ D) (sharedSet h u v ∪ D) z ≤
        pairCount (sharedSet h u v) (sharedSet h u v) z+8*h+8 := by
  constructor
  · rw [pairCount_union_self _ _ _ hdis,
      sharedSet_origin h hh u v hF hK hu hv huu hvv hiu hiv,
      disjoint_symmetric_origin _ _ hdis hsym,symmetric_origin D hsym]
  · intro z hz
    rw [pairCount_union_self _ _ _ hdis]
    have hc := repair_cross_bound h u v hF hK hu hv wF wK hwF hwK D hD₁ hD₂ hs₁ hs₂ z hz
    have hd := repair_self_bound hF hK wF wK hwF hwK D hD₁ hD₂ hs₁ hs₂ z hz
    constructor <;> omega

end Erdos66ProductProjectionRepair
