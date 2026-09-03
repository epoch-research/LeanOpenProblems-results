import Submission.CompleteFamilyCompression
import Submission.TernaryTwoSliceDomination

/-! Actual complete-family slices on the first two coordinates. Each
ternary exponent group has its exact multiplicity of labels. -/
namespace Erdos7TernaryTwoFamilySlices
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7KilledSieve
open Erdos7TernaryTwoCoherentMixture Erdos7TernaryTwoSliceDomination
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {κ : Type} [DecidableEq κ] {E : Fin 14 → ℕ} {e : κ → Fin 14 → ℕ}

def rootPattern (u v : ℕ) (i : Fin 14) : ℕ := if i.val=0 then u else if i.val=1 then v else 0

lemma rootPattern_prefix (u v : ℕ) (hu : u≤E 0) (hv : v≤E 1) :
    PrefixPattern E 2 (rootPattern u v) := by
  constructor
  · intro i
    by_cases h0 : i.val=0
    · have hi : i=0 := Fin.ext h0
      subst i
      simpa [rootPattern] using hu
    · by_cases h1 : i.val=1
      · have hi : i=1 := Fin.ext h1
        subst i
        simpa [rootPattern] using hv
      · simp [rootPattern,h0,h1]
  · intro i hi
    simp [rootPattern,show i.val≠0 by omega,show i.val≠1 by omega]

lemma project_eq_rootPattern (f : Fin 14 → ℕ) (u v : ℕ) :
    project 2 f=rootPattern u v ↔ f 0=u ∧ f 1=v := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simpa [project,rootPattern] using And.intro h0 h1
  · rintro ⟨h0,h1⟩
    funext i
    by_cases hi0 : i.val=0
    · have hi : i=0 := Fin.ext hi0
      subst i
      simpa [project,rootPattern] using h0
    · by_cases hi1 : i.val=1
      · have hi : i=1 := Fin.ext hi1
        subst i
        simpa [project,rootPattern] using h1
      · simp [project,rootPattern,hi0,hi1,show ¬i.val<2 by omega]

noncomputable def sectionLabels (b : Family E e 2) (u v : ℕ) : Finset κ :=
  b.labels.filter (fun k => e k 0=u ∧ e k 1=v)

lemma section_card (b : Family E e 2) (u v : ℕ) (hu : u≤E 0) (hv : v≤E 1) :
    (sectionLabels b u v).card=b.multiplicity := by
  have hh := b.complete (rootPattern u v) (rootPattern_prefix u v hu hv)
  simpa only [sectionLabels,project_eq_rootPattern] using hh

variable (A : Fin 14 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (X : κ → ∀ i,Finset (A i)) (ξ : Fin 5 → ∀ i,A i)

noncomputable def slice (b : Family E e 2) (v : ℕ) (x : Fin 5) : ℝ :=
  (∑ k∈b.labels.filter (fun k => e k 1=v),indicator A 1 (e k) (X k) (ξ x))/(b.multiplicity:ℝ)

lemma first_indicator_zero (k : κ) (hk : e k 0=0) (x : Fin 5) :
    indicator A 1 (e k) (X k) (ξ x)=1 := by
  have hh := indicator_step A 0 (show 0<14 by omega) (e k) (X k) (ξ x) (ξ x 0)
  change indicator A 1 (e k) (X k) (Function.update (ξ x) 0 (ξ x 0)) =
    (if e k 0=0 ∨ ξ x 0∈X k 0 then indicator A 0 (e k) (X k) (ξ x) else 0) at hh
  simpa only [Function.update_eq_self,indicator_zero,hk,true_or,if_true] using hh

lemma slice_nonneg (b : Family E e 2) (v : ℕ) (x : Fin 5) : 0≤slice A X ξ b v x := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun k _ => indicator_nonneg A 1 (e k) (X k) (ξ x))
  · exact Nat.cast_nonneg _

lemma slice_split (b : Family E e 2) (he : ∀ k i,e k i≤E i) (hE : E 0=2)
    (v : ℕ) (hv : v≤E 1) (x : Fin 5) :
    slice A X ξ b v x = 1+
      (∑ k∈sectionLabels b 1 v,indicator A 1 (e k) (X k) (ξ x)/(b.multiplicity:ℝ))+
      (∑ k∈sectionLabels b 2 v,indicator A 1 (e k) (X k) (ξ x)/(b.multiplicity:ℝ)) := by
  let W (k : κ) : ℝ := indicator A 1 (e k) (X k) (ξ x)
  let L := b.labels.filter (fun k => e k 1=v)
  have hfilter : L.filter (fun k => e k 0≤2)=L := by
    apply Finset.filter_true_of_mem
    intro k hk
    simpa only [hE] using he k 0
  have hsect (u : ℕ) : L.filter (fun k => e k 0=u)=sectionLabels b u v := by
    ext k
    simp only [L,sectionLabels,Finset.mem_filter]
    tauto
  have hp := sum_filter_level_le L (fun k => e k 0) 2 W
  rw [hfilter] at hp
  simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,zero_add,Nat.reduceAdd,hsect] at hp
  have hz : (∑ k∈sectionLabels b 0 v,W k)=(b.multiplicity:ℝ) := by
    have heq : (∑ k∈sectionLabels b 0 v,W k)=∑ _k∈sectionLabels b 0 v,(1:ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact first_indicator_zero A X ξ k (Finset.mem_filter.mp hk).2.1 x
    rw [heq]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,section_card b 0 v (by omega) hv]
  have hm : (b.multiplicity:ℝ)≠0 := by exact_mod_cast b.positive.ne'
  change (∑ k∈L,W k)/(b.multiplicity:ℝ)=_
  rw [hp,hz]
  simp only [add_div,div_self hm,Finset.sum_div,W]
  ring

lemma subtype_mean (S : Finset κ) (f : κ → ℝ) (M : ℝ) :
    (∑ k : S,(1/M)*f k.val)=∑ k∈S,f k/M := by
  rw [Finset.sum_coe_sort S (fun k => (1/M)*f k)]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every actual complete-family slice has a full-profile majorant. Labels
whose restricted section is empty are padded only in the majorant. -/
theorem slice_profile (b : Family E e 2) (he : ∀ k i,e k i≤E i) (hE : E 0=2)
    (hbranch : ∀ k,e k 0=1 → ∃ q : Fin 2,∀ x,
      indicator A 1 (e k) (X k) (ξ x)≤(if branch x=q then (1:ℝ) else 0))
    (hpoint : ∀ k,e k 0=2 → ∃ y : Fin 5,∀ x,
      indicator A 1 (e k) (X k) (ξ x)≤(if x=y then (1:ℝ) else 0))
    (v : ℕ) (hv : v≤E 1) :
    ∃ f : Fin 5 → ℝ,f∈convexHull ℝ (Set.range corner) ∧ ∀ x,slice A X ξ b v x≤f x := by
  classical
  let I := ↥(sectionLabels b 1 v)
  let J := ↥(sectionLabels b 2 v)
  have hm : (0:ℝ)<b.multiplicity := by exact_mod_cast b.positive
  have hwI : (∑ _i : I,(1:ℝ)/b.multiplicity)=1 := by
    simp only [I,J,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,
      section_card b 1 v (by omega) hv]
    field_simp
  have hwJ : (∑ _i : J,(1:ℝ)/b.multiplicity)=1 := by
    simp only [I,J,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,
      section_card b 2 v (by omega) hv]
    field_simp
  have hB (k : I) : ∃ q : Fin 2,∀ x,
      indicator A 1 (e k.val) (X k.val) (ξ x)≤(if branch x=q then (1:ℝ) else 0) :=
    hbranch k.val (Finset.mem_filter.mp k.property).2.1
  have hP (k : J) : ∃ y : Fin 5,∀ x,
      indicator A 1 (e k.val) (X k.val) (ξ x)≤(if x=y then (1:ℝ) else 0) :=
    hpoint k.val (Finset.mem_filter.mp k.property).2.1
  choose B hB using hB
  choose P hP using hP
  obtain ⟨f,hf,hbound⟩ := dominating_profile
    (fun _ : I => (1:ℝ)/b.multiplicity) (fun _ : J => (1:ℝ)/b.multiplicity)
    (fun _ => by positivity) (fun _ => by positivity) hwI hwJ B P
    (fun k x => indicator A 1 (e k.val) (X k.val) (ξ x))
    (fun k x => indicator A 1 (e k.val) (X k.val) (ξ x)) hB hP
  refine ⟨f,hf,fun x => ?_⟩
  rw [slice_split A X ξ b he hE v hv x]
  have hh := hbound x
  rw [subtype_mean (sectionLabels b 1 v) (fun k => indicator A 1 (e k) (X k) (ξ x)),
    subtype_mean (sectionLabels b 2 v) (fun k => indicator A 1 (e k) (X k) (ξ x))] at hh
  exact hh

/-- A multiplicity-one slice has a single integer corner majorant. This is
used for the current slices, not for arbitrary normalized future families. -/
theorem slice_single_corner (b : Family E e 2) (he : ∀ k i,e k i≤E i) (hE : E 0=2)
    (hM : b.multiplicity=1)
    (hbranch : ∀ k,e k 0=1 → ∃ q : Fin 2,∀ x,
      indicator A 1 (e k) (X k) (ξ x)≤(if branch x=q then (1:ℝ) else 0))
    (hpoint : ∀ k,e k 0=2 → ∃ y : Fin 5,∀ x,
      indicator A 1 (e k) (X k) (ξ x)≤(if x=y then (1:ℝ) else 0))
    (v : ℕ) (hv : v≤E 1) :
    ∃ c : Fin 10,∀ x,slice A X ξ b v x≤corner c x := by
  obtain ⟨k1,h1⟩ := Finset.card_eq_one.mp ((section_card b 1 v (by omega) hv).trans hM)
  obtain ⟨k2,h2⟩ := Finset.card_eq_one.mp ((section_card b 2 v (by omega) hv).trans hM)
  have hk1 : k1∈sectionLabels b 1 v := by rw [h1]; simp
  have hk2 : k2∈sectionLabels b 2 v := by rw [h2]; simp
  obtain ⟨q,hq⟩ := hbranch k1 (Finset.mem_filter.mp hk1).2.1
  obtain ⟨y,hy⟩ := hpoint k2 (Finset.mem_filter.mp hk2).2.1
  refine ⟨choiceCode q y,fun x => ?_⟩
  rw [slice_split A X ξ b he hE v hv x,h1,h2]
  simp only [Finset.sum_singleton,hM,Nat.cast_one,div_one,corner,count_formula,
    Nat.cast_add,Nat.cast_one,Nat.cast_ite,Nat.cast_zero]
  exact add_le_add (add_le_add le_rfl (hq x)) (hy x)

#print axioms slice_single_corner

#print axioms slice_profile

#print axioms section_card
#print axioms slice_split
end Erdos7TernaryTwoFamilySlices
