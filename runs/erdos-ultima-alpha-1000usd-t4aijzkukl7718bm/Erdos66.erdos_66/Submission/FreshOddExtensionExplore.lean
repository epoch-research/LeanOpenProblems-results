import Submission.FreshCurvePrefixExplore
import Submission.OddExtensionCharacterFiberExplore

/-! Exact representation-count inheritance for an arbitrary old set, in an
odd-degree finite-field-plane extension. No ordinary-integer encoding is
asserted. -/
namespace Erdos66FreshOddExtension
open Erdos66FreshCurvePrefix Erdos66ParabolaRepair Erdos66OriginRepair
  Erdos66FiniteField Erdos66Coset Erdos66OddExtensionCharacterFiber
open scoped Classical
set_option maxHeartbeats 1800000

section Algebra
variable {E : Type*} [Field E]

/-- If the old subfield is square-closed, two old-parameter curves with
nonopposite parameters have no new endpoint above an old target. -/
lemma old_target_forces_old_endpoint (k : Subfield E)
    (hclosed : ∀ x : E, x^2∈k → x∈k)
    (u v : E) (hu : u∈k) (hv : v∈k) (hu0 : u≠0) (hv0 : v≠0)
    (huv : u+v≠0) (z a : E×E) (hz : z.1∈k ∧ z.2∈k)
    (ha : a.2=a.1^2/u) (hb : z.2-a.2=(z.1-a.1)^2/v) :
    a.1∈k ∧ a.2∈k := by
  have he : a.1^2/u+(z.1-a.1)^2/v=z.2 := by linear_combination -ha-hb
  have hs := (parabola_equation_iff u v z.1 z.2 a.1 hu0 hv0 huv).mp he
  have hdisc := k.mul_mem (k.mul_mem hu hv)
    (k.sub_mem (k.mul_mem (k.add_mem hu hv) hz.2) (k.pow_mem hz.1 2))
  have hroot : (u+v)*a.1-u*z.1∈k := hclosed _ (hs.symm ▸ hdisc)
  have hx : a.1∈k := by
    have hh := k.div_mem (k.add_mem hroot (k.mul_mem hu hz.1)) (k.add_mem hu hv)
    convert hh using 1
    field_simp
    <;> ring
  exact ⟨hx,ha ▸ k.div_mem (k.pow_mem hx 2) hu⟩
end Algebra

section Finite
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

lemma oldPlane_add (k : Subfield E) {a b : E×E}
    (ha : a∈oldPlane k) (hb : b∈oldPlane k) : a+b∈oldPlane k := by
  obtain ⟨ha1,ha2⟩ := (mem_oldPlane k a).mp ha
  obtain ⟨hb1,hb2⟩ := (mem_oldPlane k b).mp hb
  exact (mem_oldPlane k (a+b)).mpr ⟨k.add_mem ha1 hb1,k.add_mem ha2 hb2⟩

lemma oldPlane_sub (k : Subfield E) {a b : E×E}
    (ha : a∈oldPlane k) (hb : b∈oldPlane k) : a-b∈oldPlane k := by
  obtain ⟨ha1,ha2⟩ := (mem_oldPlane k a).mp ha
  obtain ⟨hb1,hb2⟩ := (mem_oldPlane k b).mp hb
  exact (mem_oldPlane k (a-b)).mpr ⟨k.sub_mem ha1 hb1,k.sub_mem ha2 hb2⟩

lemma old_pairCount_outside (k : Subfield E) (A D : Finset (E×E))
    (hA : A⊆oldPlane k) (hD : D⊆oldPlane k) (z : E×E) (hz : z∉oldPlane k) :
    pairCount A D z=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨ha,hza⟩ := Finset.mem_filter.mp ha
  apply hz
  simpa only [add_sub_cancel] using oldPlane_add k (hA ha) (hD hza)

lemma old_fresh_pairCount_inside (k : Subfield E) (A B : Finset (E×E))
    (hA : A⊆oldPlane k) (hB : Disjoint B (oldPlane k))
    (z : E×E) (hz : z∈oldPlane k) : pairCount A B z=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨ha,hza⟩ := Finset.mem_filter.mp ha
  exact Finset.disjoint_left.mp hB hza (oldPlane_sub k hz (hA ha))

noncomputable def freshParabolas (k : Subfield E) (U : Finset E) : Finset (E×E) :=
  parabolaSet U \ oldPlane k

lemma freshParabolas_eq_biUnion (k : Subfield E) (U : Finset E) :
    freshParabolas k U=U.biUnion (freshCurve k) := by
  ext z
  simp only [freshParabolas,Finset.mem_sdiff,parabolaSet_eq_biUnion,
    Finset.mem_biUnion,freshCurve,Finset.mem_sdiff]
  aesop

lemma freshParabolas_disjoint (k : Subfield E) (U : Finset E) :
    Disjoint (freshParabolas k U) (oldPlane k) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzold
  exact (Finset.mem_sdiff.mp hz).2 hzold

/-- The fresh set introduces no old-target self-representations, including
at zero. The no-opposite-parameters condition is essential. -/
theorem fresh_pairCount_inside (k : Subfield E)
    (hclosed : ∀ x : E, x^2∈k → x∈k)
    (U : Finset E) (hU : ∀ u∈U, u∈k ∧ u≠0)
    (hUU : ∀ u∈U, ∀ v∈U, u+v≠0) (z : E×E) (hz : z∈oldPlane k) :
    pairCount (freshParabolas k U) (freshParabolas k U) z=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨ha,hb⟩ := Finset.mem_filter.mp ha
  obtain ⟨haC,hanot⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hbC,hbnot⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨u,hu,hua⟩ := (Finset.mem_filter.mp haC).2
  obtain ⟨v,hv,hvb⟩ := (Finset.mem_filter.mp hbC).2
  exact hanot ((mem_oldPlane k a).mpr (old_target_forces_old_endpoint k hclosed u v
    (hU u hu).1 (hU v hv).1 (hU u hu).2 (hU v hv).2 (hUU u hu v hv)
    z a ((mem_oldPlane k z).mp hz) hua hvb))

/-- Exact old representation-count preservation for an arbitrary prescribed
old set, not just for the old slice of the new template. -/
theorem prescribed_old_counts (k : Subfield E)
    (hclosed : ∀ x : E, x^2∈k → x∈k)
    (A : Finset (E×E)) (hA : A⊆oldPlane k)
    (U : Finset E) (hU : ∀ u∈U, u∈k ∧ u≠0)
    (hUU : ∀ u∈U, ∀ v∈U, u+v≠0) (z : E×E) (hz : z∈oldPlane k) :
    pairCount (A∪freshParabolas k U) (A∪freshParabolas k U) z=pairCount A A z := by
  have hdis := freshParabolas_disjoint k U
  have hd : Disjoint A (freshParabolas k U) := hdis.symm.mono_left hA
  rw [pairCount_union_self _ _ _ hd, pairCount_comm (freshParabolas k U) A,
    old_fresh_pairCount_inside k A _ hA hdis z hz,
    fresh_pairCount_inside k hclosed U hU hUU z hz]
  omega


/-- Replacing the old slice of a union of parabolas by an arbitrary old set
costs at most 4|U| at every new-plane target. There is no dependence on the
size or self-counts of the prescribed old set. -/
theorem replacement_off_plane (k : Subfield E) (hE : ringChar E≠2)
    (A : Finset (E×E)) (hA : A⊆oldPlane k)
    (U : Finset E) (hU : ∀ u∈U, u≠0) (z : E×E) (hz : z∉oldPlane k) :
    |(pairCount (A∪freshParabolas k U) (A∪freshParabolas k U) z:ℤ)-
      pairCount (parabolaSet U) (parabolaSet U) z|≤4*(U.card:ℤ) := by
  let B := freshParabolas k U
  let D := parabolaSet U ∩ oldPlane k
  have hD : D⊆oldPlane k := Finset.inter_subset_right
  have hB : B⊆U.biUnion (freshCurve k) := by rw [←freshParabolas_eq_biUnion]
  have hdA := fresh_union_disjoint k A B hA U hB
  have hdD := fresh_union_disjoint k D B hD U hB
  have hAB := arbitrary_old_fresh_union_cap k hE A B hA U hU hB z
  have hDB := arbitrary_old_fresh_union_cap k hE D B hD U hU hB z
  rw [pairCount_comm A B] at hAB
  rw [pairCount_comm D B] at hDB
  have he : D∪B=parabolaSet U := by
    rw [Finset.union_comm]
    exact Finset.sdiff_union_inter _ _
  have hC := pairCount_union_self D B z hdD
  rw [he,old_pairCount_outside k D D hD hD z hz] at hC
  have hA' := pairCount_union_self A B z hdA
  rw [old_pairCount_outside k A A hA hA z hz] at hA'
  change |(pairCount (A∪B) (A∪B) z:ℤ)-pairCount (parabolaSet U) (parabolaSet U) z|≤_
  rw [hA',hC]
  push_cast
  have hAB' : (pairCount B A z:ℤ)≤2*(U.card:ℤ) := by exact_mod_cast hAB
  have hDB' : (pairCount B D z:ℤ)≤2*(U.card:ℤ) := by exact_mod_cast hDB
  rw [abs_le]
  constructor <;> omega

/-- New-target flatness is independent of the prescribed old set. At old
targets, use `prescribed_old_counts` instead: their old values remain exact. -/
theorem replacement_flat_new_targets (k : Subfield E) (hE : ringChar E≠2)
    (A : Finset (E×E)) (hA : A⊆oldPlane k)
    (U : Finset E) (hU : ∀ u∈U, u≠0)
    (hUU : ∀ u∈U, ∀ v∈U, u+v≠0) (hne : U.Nonempty)
    (z : E×E) (hz : z∉oldPlane k) :
    |(pairCount (A∪freshParabolas k U) (A∪freshParabolas k U) z:ℤ)-(U.card:ℤ)^2|≤
      (∑ w : E, |charFiber U w|)+6*(U.card:ℤ) := by
  have hz0 : z≠0 := by
    intro he
    apply hz
    rw [he,mem_oldPlane]
    exact ⟨k.zero_mem,k.zero_mem⟩
  have hb := graph_set_error_bound hE U hU hUU hne z.1 z.2
    (by simpa only [Prod.mk.eta] using hz0)
  rw [←parabolaSet_pairCount_eq U z] at hb
  have hr := replacement_off_plane k hE A hA U hU z hz
  rw [abs_le] at hb hr ⊢
  constructor <;> omega

end Finite
end Erdos66FreshOddExtension
