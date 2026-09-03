import Submission.PaleyBilinearExplore
import Submission.DisjointPaletteAssemblyExplore
import Submission.PrefixFaithfulParabolaLiftExplore

/-! A collision-free finite lift preserving an arbitrary row-zero set.
Its complete mixed counts are useful in the high-density parameter regime.
No claim about ordinary counts above the preserved natural prefix is made. -/
namespace Erdos66QuadraticTranslateAnchor
open Erdos66PaleyBilinear Erdos66OriginRepair Erdos66FiniteField
  Erdos66DisjointPaletteAssembly Erdos66PrefixFaithfulParabolaLift
  Erdos66InheritedOriginLift AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1200000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def curve (u : F) : Finset (F × F) :=
  Finset.univ.image (fun k ↦ (u+k^2,k))

noncomputable def lift (U : Finset F) : Finset (F × F) := U.biUnion curve

omit [Fintype F] [DecidableEq F] in
lemma point_injective (u : F) : Function.Injective (fun k : F ↦ (u+k^2,k)) := by
  intro k l h
  exact congrArg Prod.snd h

lemma mem_curve (u : F) (z : F × F) : z∈curve u ↔ z.1=u+z.2^2 := by
  constructor
  · intro hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    rfl
  · intro hz
    exact Finset.mem_image.mpr ⟨z.2,Finset.mem_univ _,Prod.ext hz.symm rfl⟩

lemma curves_disjoint (U : Finset F) : (U : Set F).PairwiseDisjoint curve := by
  intro u hu v hv huv
  apply Finset.disjoint_left.mpr
  intro z hzu hzv
  have h1 := (mem_curve u z).mp hzu
  have h2 := (mem_curve v z).mp hzv
  exact huv (add_right_cancel (h1.symm.trans h2))

lemma mem_lift (U : Finset F) (z : F × F) :
    z∈lift U ↔ z.1-z.2^2∈U := by
  simp only [lift,Finset.mem_biUnion,mem_curve]
  constructor
  · rintro ⟨u,hu,he⟩
    simpa only [he,add_sub_cancel_right] using hu
  · intro h
    exact ⟨z.1-z.2^2,h,by ring⟩

lemma lift_row_zero (U : Finset F) (x : F) : (x,0)∈lift U ↔ x∈U := by
  simp only [mem_lift,zero_pow (by decide : 2≠0),sub_zero]

lemma curve_card (u : F) : (curve u).card=Fintype.card F := by
  rw [curve,Finset.card_image_of_injective _ (point_injective u),Finset.card_univ]

lemma lift_card (U : Finset F) : (lift U).card=U.card*Fintype.card F := by
  rw [lift,Finset.card_biUnion (curves_disjoint U)]
  simp only [curve_card,Finset.sum_const,nsmul_eq_mul,Nat.cast_id]

lemma curve_pairCount (u v q t : F) :
    pairCount (curve u) (curve v) (q,t)=
      Fintype.card {k : F // k^2+(t-k)^2=q-u-v} := by
  rw [pairCount]
  change ((Finset.univ.image (fun k : F ↦ (u+k^2,k))).filter
    (fun a ↦ (q,t)-a∈curve v)).card = _
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (point_injective u),Fintype.card_subtype]
  congr 1
  ext k
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_curve]
  change q-(u+k^2)=v+(t-k)^2 ↔ k^2+(t-k)^2=q-u-v
  constructor <;> intro hh <;> linear_combination -hh

lemma curve_pairCount_char (hF : ringChar F≠2) (u v q t : F) :
    (pairCount (curve u) (curve v) (q,t) : ℤ)=
      1+quadraticChar F (2*(q-u-v)-t^2) := by
  rw [curve_pairCount]
  have hh := parabola_sum_count hF (1 : F) 1 t (q-u-v)
    one_ne_zero one_ne_zero (by simpa only [one_add_one_eq_two] using Ring.two_ne_zero hF)
  simpa only [div_one,map_one,mul_one,one_mul,one_add_one_eq_two] using hh

lemma lift_pairCount_identity (hF : ringChar F≠2) (U V : Finset F) (q t : F) :
    (pairCount (lift U) (lift V) (q,t) : ℤ)=
      (U.card : ℤ)*V.card+quadraticChar F 2*bilinear U V (q-t^2/2) := by
  have he (u v : F) : 2*(q-u-v)-t^2=2*(q-t^2/2-u-v) := by
    field_simp [Ring.two_ne_zero hF]
    ring
  rw [lift,pairCount_biUnion_left _ _ (curves_disjoint U)]
  simp_rw [lift,pairCount_biUnion_right _ _ (curves_disjoint V)]
  push_cast
  simp_rw [curve_pairCount_char hF,he,map_mul]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
    ←Finset.mul_sum,bilinear]
  ring

/-- One explicit map works jointly for all parameter sets and all targets.
There are no translation-selection, nonzero-label, or collision hypotheses. -/
theorem lift_mixed_sq_error (hF : ringChar F≠2) (U V : Finset F) (q t : F) :
    ((pairCount (lift U) (lift V) (q,t) : ℤ)-(U.card : ℤ)*V.card)^2 ≤
      (Fintype.card F : ℤ)*U.card*V.card := by
  rw [lift_pairCount_identity hF]
  have hχ := quadraticChar_sq_one (F := F) (Ring.two_ne_zero hF)
  have he : ((U.card : ℤ)*V.card+quadraticChar F 2*bilinear U V (q-t^2/2)-
      (U.card : ℤ)*V.card)^2=(bilinear U V (q-t^2/2))^2 := by
    convert congrArg (fun x : ℤ ↦ x*(bilinear U V (q-t^2/2))^2) hχ using 1 <;> ring
  rw [he]
  exact bilinear_sq_le_card hF U V _

lemma lift_mixed_abs_error (hF : ringChar F≠2) (U V : Finset F) (z : F × F) :
    |(pairCount (lift U) (lift V) z : ℝ)-(U.card : ℝ)*V.card| ≤
      Real.sqrt ((Fintype.card F : ℝ)*U.card*V.card) := by
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  rw [sq_abs]
  exact_mod_cast lift_mixed_sq_error hF U V z.1 z.2

lemma lift_self_abs_error (hF : ringChar F≠2) (U : Finset F) (z : F × F) :
    |(pairCount (lift U) (lift U) z : ℝ)-(U.card : ℝ)^2| ≤
      Real.sqrt (Fintype.card F)*U.card := by
  have hh := lift_mixed_abs_error hF U U z
  have hs : Real.sqrt ((Fintype.card F : ℝ)*U.card*U.card)=
      Real.sqrt (Fintype.card F)*U.card := by
    rw [mul_assoc,←pow_two,Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  simpa only [hs,←pow_two] using hh

lemma encoded_lift_prefix (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (n : ℕ) (hn : n<p) :
    n∈encodePlane p (lift U) ↔ (n : ZMod p)∈U := by
  rw [encodePlane_prefix p _ n hn,lift_row_zero]

lemma encoded_lift_counts_below (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (n : ℕ) (hn : n<p) :
    sumRep (encodePlane p (lift U) : Set ℕ) n=
      sumRep {k : ℕ | k<p ∧ (k : ZMod p)∈U} n := by
  apply Erdos66Compactness.sumRep_congr_below
  intro k hk
  have hkp : k<p := lt_of_le_of_lt hk hn
  simpa only [Finset.mem_coe,Set.mem_setOf_eq,hkp,true_and] using encoded_lift_prefix p U k hkp

end Erdos66QuadraticTranslateAnchor
