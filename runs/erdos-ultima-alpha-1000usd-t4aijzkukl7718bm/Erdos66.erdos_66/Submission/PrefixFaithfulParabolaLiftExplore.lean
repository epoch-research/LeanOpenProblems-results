import Submission.InheritedOriginLiftExplore
import Submission.ShearedParabolaPrefixExplore
import Submission.CompactnessExplore

/-! A finite parabola lift preserving a prescribed natural prefix exactly.
Its representation mean is amplified, not logarithmically retuned. -/
namespace Erdos66PrefixFaithfulParabolaLift
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph
  Erdos66InheritedOriginLift Erdos66ShearedParabolaPrefix AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1900000

section Groups
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def shiftSet (A : Finset G) (a : G) : Finset G := A.image (fun x ↦ a+x)

lemma mem_shiftSet (A : Finset G) (a x : G) : x∈shiftSet A a ↔ x-a∈A := by
  constructor
  · rintro h
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    have hy' : y=x-a := by
      have hh := congrArg (fun z ↦ z-a) he
      simpa only [add_sub_cancel_left] using hh
    simpa only [hy'] using hy
  · intro h
    exact Finset.mem_image.mpr ⟨x-a,h,by abel⟩

lemma pairCount_shiftSet (A B : Finset G) (a b z : G) :
    pairCount (shiftSet A a) (shiftSet B b) z=pairCount A B (z-a-b) := by
  unfold pairCount
  dsimp only [shiftSet]
  rw [Finset.filter_image,Finset.card_image_of_injective _ (add_right_injective a)]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  have he : z-(a+x)∈shiftSet B b ↔ z-a-b-x∈B := by
    rw [mem_shiftSet]
    rw [show z-(a+x)-b=z-a-b-x by abel]
  exact and_congr_right (fun _ ↦ he)

lemma pairCount_insert_left_bound (A B : Finset G) (a z : G) :
    pairCount (insert a A) B z ≤ pairCount A B z+1 := by
  unfold pairCount
  rw [Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

lemma pairCount_erase_bounds (A : Finset G) (a z : G) :
    pairCount (A.erase a) (A.erase a) z ≤ pairCount A A z ∧
      pairCount A A z ≤ pairCount (A.erase a) (A.erase a) z+2 := by
  constructor
  · apply Finset.card_le_card
    intro x hx
    obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hx,Finset.mem_of_mem_erase hzx⟩
  · by_cases ha : a∈A
    · have h₁ := pairCount_insert_left_bound (A.erase a) A a z
      rw [Finset.insert_erase ha] at h₁
      have h₂ := pairCount_insert_left_bound (A.erase a) (A.erase a) a z
      rw [Finset.insert_erase ha,pairCount_comm A (A.erase a)] at h₂
      omega
    · have he : A.erase a=A := Finset.erase_eq_of_notMem ha
      rw [he]
      omega

lemma pairCount_erase_error (A : Finset G) (a z : G) :
    |(pairCount (A.erase a) (A.erase a) z:ℝ)-(pairCount A A z:ℝ)| ≤ 2 := by
  obtain ⟨h₁,h₂⟩ := pairCount_erase_bounds A a z
  have h₁' : (pairCount (A.erase a) (A.erase a) z:ℝ) ≤ pairCount A A z := by exact_mod_cast h₁
  have h₂' : (pairCount A A z:ℝ) ≤ pairCount (A.erase a) (A.erase a) z+2 := by exact_mod_cast h₂
  rw [abs_le]
  constructor <;> linarith

end Groups

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def faithfulLift (U : Finset F) (a : F) : Finset (F × F) :=
  (shiftSet (sheared (translated U a)) (-a,0)).erase (-a,0)

lemma faithfulLift_row (U : Finset F) (hne : U.Nonempty) (a : F)
    (hU : ∀ u∈translated U a, u≠0) (x : F) :
    (x,0)∈faithfulLift U a ↔ x∈U := by
  have hm : x+a∈translated U a ↔ x∈U := by
    have he : translated U a=shiftSet U a := rfl
    rw [he,mem_shiftSet,add_sub_cancel_right]
  have hne' : (translated U a).Nonempty := hne.image _
  unfold faithfulLift
  rw [Finset.mem_erase,mem_shiftSet]
  have he : (x,(0:F))-(-a,0)=(x+a,0) := by ext <;> simp
  rw [he,first_row _ hU hne',hm]
  constructor
  · rintro ⟨hx,h⟩
    rcases h with h0 | h
    · exact False.elim (hx (Prod.ext (by linear_combination h0) rfl))
    · exact h
  · intro hx
    refine ⟨?_,Or.inr hx⟩
    intro he
    have hx' := congrArg Prod.fst he
    have hu := hU (x+a) (hm.mpr hx)
    exact hu (by dsimp only [Prod.fst] at hx'; rw [hx']; simp)

lemma faithfulLift_count_comparison (U : Finset F) (a : F) (z : F × F) :
    |(pairCount (faithfulLift U a) (faithfulLift U a) z:ℝ)-
      (pairCount (parabolaSet (translated U a)) (parabolaSet (translated U a))
        (shear.symm (z-(-a,0)-(-a,0))):ℝ)| ≤ 2 := by
  have hh := pairCount_erase_error (shiftSet (sheared (translated U a)) (-a,0)) (-a,0) z
  rw [pairCount_shiftSet] at hh
  have he := sheared_pairCount (translated U a) (translated U a)
    (shear.symm (z-(-a,0)-(-a,0)))
  rw [AddEquiv.apply_symm_apply] at he
  rw [he] at hh
  exact hh

noncomputable def encodePlane (p : ℕ) (B : Finset (ZMod p × ZMod p)) : Finset ℕ :=
  B.image (fun z ↦ z.1.val+p*z.2.val)

lemma encodePlane_prefix (p : ℕ) [NeZero p] (B : Finset (ZMod p × ZMod p))
    (n : ℕ) (hn : n<p) : n∈encodePlane p B ↔ ((n:ZMod p),0)∈B := by
  have hp : 0<p := NeZero.pos p
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
    have hx := z.1.val_lt
    have hy := z.2.val_lt
    have hy0 : z.2.val=0 := by nlinarith
    have hz2 : z.2=0 := ZMod.val_injective p (by simpa only [ZMod.val_zero] using hy0)
    have hzn : z.1.val=n := by simpa only [hy0,mul_zero,add_zero] using he
    have hz1 : z.1=(n:ZMod p) := by rw [←hzn,ZMod.natCast_zmod_val]
    have hze : z=((n:ZMod p),0) := Prod.ext hz1 hz2
    simpa only [hze] using hz
  · intro h
    exact Finset.mem_image.mpr ⟨((n:ZMod p),0),h,by simp [ZMod.val_natCast_of_lt hn]⟩

lemma faithful_encoded_prefix (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (hne : U.Nonempty) (a : ZMod p) (hU : ∀ u∈translated U a, u≠0)
    (n : ℕ) (hn : n<p) :
    n∈encodePlane p (faithfulLift U a) ↔ (n:ZMod p)∈U := by
  rw [encodePlane_prefix p _ n hn,faithfulLift_row U hne a hU]

lemma faithful_encoded_counts (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (hne : U.Nonempty) (a : ZMod p) (hU : ∀ u∈translated U a, u≠0)
    (n : ℕ) (hn : n<p) :
    sumRep (encodePlane p (faithfulLift U a):Set ℕ) n=
      sumRep {k : ℕ | k<p ∧ (k:ZMod p)∈U} n := by
  apply Erdos66Compactness.sumRep_congr_below
  intro k hk
  have hkp : k<p := lt_of_le_of_lt hk hn
  simpa only [Finset.mem_coe,Set.mem_setOf_eq,hkp,true_and] using
    faithful_encoded_prefix p U hne a hU k hkp

/-- The selected translate does not change the retained first row after
undoing its shift and deleting the common origin. All other counts lose at
most two, but the lifted nominal mean remains |U|^2, not |U|^2/|F|. -/
theorem exists_prefix_faithful_lift (hF : ringChar F≠2) (U : Finset F)
    (hne : U.Nonempty) (hU : 2*U.card<Fintype.card F) (μ E : ℝ)
    (hflat : ∀ t : F, |(pairCount U U t:ℝ)-μ| ≤ E) :
    ∃ a : F, (∀ u∈translated U a, u≠0) ∧
      (∀ x : F, (x,0)∈faithfulLift U a ↔ x∈U) ∧
      ∀ z : F × F,
        let w := shear.symm (z-(-a,0)-(-a,0))
        (w=0 → |(pairCount (faithfulLift U a) (faithfulLift U a) z:ℝ)-
          (1+((Fintype.card F:ℝ)-1)*μ)| ≤ ((Fintype.card F:ℝ)-1)*E+2) ∧
        (w≠0 → |(pairCount (faithfulLift U a) (faithfulLift U a) z:ℝ)-(U.card:ℝ)^2| ≤
          Real.sqrt (8*(Fintype.card F:ℝ)*(U.card:ℝ)^2)+3*U.card+2) := by
  obtain ⟨a,ha,hzero,hother⟩ := exists_inherited_origin_lift hF U hne hU μ E hflat
  refine ⟨a,ha,faithfulLift_row U hne a ha,fun z ↦ ?_⟩
  dsimp only
  have hc := faithfulLift_count_comparison U a z
  constructor
  · intro hz
    rw [hz] at hc
    have ht := abs_sub_le (pairCount (faithfulLift U a) (faithfulLift U a) z:ℝ)
      (pairCount (parabolaSet (translated U a)) (parabolaSet (translated U a)) 0:ℝ)
      (1+((Fintype.card F:ℝ)-1)*μ)
    linarith
  · intro hz
    have hh := hother _ hz
    have ht := abs_sub_le (pairCount (faithfulLift U a) (faithfulLift U a) z:ℝ)
      (pairCount (parabolaSet (translated U a)) (parabolaSet (translated U a))
        (shear.symm (z-(-a,0)-(-a,0))):ℝ) ((U.card:ℝ)^2)
    linarith

end Erdos66PrefixFaithfulParabolaLift
