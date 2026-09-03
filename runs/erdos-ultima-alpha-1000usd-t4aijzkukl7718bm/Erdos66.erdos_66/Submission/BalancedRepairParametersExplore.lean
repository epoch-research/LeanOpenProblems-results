import Submission.CharacterEnergyExplore
import Submission.AffineRootAggregateExplore

/-! Two fixed types of repair pairs suffice. Their parameters have common
sum one and opposite product characters; their two root-count errors cancel
identically at every plane target. -/
namespace Erdos66BalancedRepairParameters
open Erdos66FiniteField Erdos66CharacterEnergy Erdos66AffineRootAggregate Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1800000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def goodParameters (δ : ℤ) : Finset F :=
  Finset.univ.filter (fun u ↦ quadraticChar F (u*(1-u))=δ)

lemma parameter_character_sum (hF : ringChar F ≠ 2) :
    (∑ u : F, quadraticChar F (u*(1-u))) = -quadraticChar F (-1) := by
  have hh := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  rw [(quadraticChar_isQuadratic F).inv] at hh
  simpa only [jacobiSum,map_mul] using hh

lemma goodParameters_card (hF : ringChar F ≠ 2) (δ : ℤ) (hδ : δ=1 ∨ δ = -1) :
    Fintype.card F ≤ 2*(goodParameters (F := F) δ).card+3 := by
  have hpoint (u : F) : (1 : ℤ) =
      2*(if quadraticChar F (u*(1-u))=δ then 1 else 0)-δ*quadraticChar F (u*(1-u))+
        (if u=0 then 1 else 0)+(if u=1 then 1 else 0) := by
    by_cases hu0 : u=0
    · subst u
      rcases hδ with rfl | rfl <;> simp
    by_cases hu1 : u=1
    · subst u
      rcases hδ with rfl | rfl <;> simp
    have hne : u*(1-u)≠0 := mul_ne_zero hu0 (sub_ne_zero.mpr (Ne.symm hu1))
    rcases quadraticChar_dichotomy hne with he | he
    all_goals rcases hδ with rfl | rfl <;> simp [he,hu0,hu1]
  have he : (Fintype.card F : ℤ) = 2*(goodParameters (F := F) δ).card-
      δ*(∑ u : F, quadraticChar F (u*(1-u)))+2 := by
    calc
      _ = ∑ _u : F, (1 : ℤ) := by simp
      _ = ∑ u : F, (2*(if quadraticChar F (u*(1-u))=δ then 1 else 0)-δ*quadraticChar F (u*(1-u))+
          (if u=0 then 1 else 0)+(if u=1 then 1 else 0)) := Finset.sum_congr rfl (fun u _ ↦ hpoint u)
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
        simp [goodParameters]
        ring
  rw [parameter_character_sum hF] at he
  have hc := quadraticChar_abs_le_one (F := F) (-1)
  have hb : (Fintype.card F : ℤ) ≤ 2*(goodParameters (F := F) δ).card+3 := by
    rcases hδ with rfl | rfl <;> nlinarith [(abs_le.mp hc).1,(abs_le.mp hc).2]
  exact_mod_cast hb

/-- A prescribed character sign remains available after forbidding a
finite set for each of the two parameters. -/
theorem exists_pair_avoiding (hF : ringChar F ≠ 2) (B : Finset F)
    (hsize : 4*B.card+3 < Fintype.card F) (δ : ℤ) (hδ : δ=1 ∨ δ = -1) :
    ∃ u v : F, u≠0 ∧ v≠0 ∧ u+v=1 ∧ quadraticChar F (u*v)=δ ∧ u∉B ∧ v∉B := by
  let C := B ∪ B.image (fun v ↦ 1-v)
  have hc : C.card ≤ 2*B.card := by
    have hh := Finset.card_union_le B (B.image (fun v ↦ 1-v))
    have hi := Finset.card_image_le (s := B) (f := fun v : F ↦ 1-v)
    dsimp [C]
    omega
  have hg := goodParameters_card (F := F) hF δ hδ
  have hnot : ¬goodParameters (F := F) δ ⊆ C := by
    intro hs
    have hh := Finset.card_le_card hs
    omega
  obtain ⟨u,hu,huC⟩ := Finset.not_subset.mp hnot
  have hchar : quadraticChar F (u*(1-u))=δ := (Finset.mem_filter.mp hu).2
  have hδ0 : δ≠0 := by rcases hδ with rfl | rfl <;> norm_num
  have hu0 : u≠0 := by intro he; simp only [he,zero_mul,quadraticChar_zero] at hchar; exact hδ0 hchar.symm
  have hv0 : 1-u≠0 := by intro he; simp only [he,mul_zero,quadraticChar_zero] at hchar; exact hδ0 hchar.symm
  refine ⟨u,1-u,hu0,hv0,by ring,hchar,?_,?_⟩
  · exact fun hh ↦ huC (Finset.mem_union_left _ hh)
  · intro hh
    exact huC (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨1-u,hh,by ring⟩))

/-- The fixed four-parameter palette avoids all opposites in the old
palette and within itself. It can be reused at every coarse repair center. -/
theorem exists_balanced_palette (hF : ringChar F ≠ 2) (U : Finset F)
    (hsize : 4*(U.card+2)+3 < Fintype.card F) :
    ∃ u v x y : F, u≠0 ∧ v≠0 ∧ x≠0 ∧ y≠0 ∧
      u+v=1 ∧ x+y=1 ∧ quadraticChar F (u*v)=1 ∧ quadraticChar F (x*y)= -1 ∧
      (∀ r∈({u,v,x,y} : Finset F), ∀ s∈U, r+s≠0) ∧
      (∀ r∈({u,v,x,y} : Finset F), ∀ s∈({u,v,x,y} : Finset F), r+s≠0) := by
  let B := U.image Neg.neg
  have hB : B.card ≤ U.card := Finset.card_image_le
  obtain ⟨u,v,hu,hv,huv,hcuv,huB,hvB⟩ := exists_pair_avoiding hF B (by omega) 1 (Or.inl rfl)
  let C := B ∪ {-u,-v}
  have hC : C.card ≤ U.card+2 := by
    have hh := Finset.card_union_le B ({-u,-v} : Finset F)
    have hi : ({-u,-v} : Finset F).card ≤ 2 := by
      exact Finset.card_le_two
    dsimp [C]
    omega
  obtain ⟨x,y,hx,hy,hxy,hcxy,hxC,hyC⟩ := exists_pair_avoiding hF C (by omega) (-1) (Or.inr rfl)
  have hself (z : F) (hz : z≠0) : z+z≠0 := by
    rw [←two_mul]
    exact mul_ne_zero (Ring.two_ne_zero hF) hz
  have hav (z : F) (hz : z∉B) (s : F) (hs : s∈U) : z+s≠0 := by
    intro he
    have he' : z= -s := eq_neg_of_add_eq_zero_left he
    exact hz (Finset.mem_image.mpr ⟨s,hs,he'.symm⟩)
  have hcross (z : F) (hz : z∉C) : z+u≠0 ∧ z+v≠0 := by
    constructor
    · intro he
      have he' : z= -u := eq_neg_of_add_eq_zero_left he
      exact hz (Finset.mem_union_right _ (by simp [he']))
    · intro he
      have he' : z= -v := eq_neg_of_add_eq_zero_left he
      exact hz (Finset.mem_union_right _ (by simp [he']))
  have hxB : x∉B := fun hh ↦ hxC (Finset.mem_union_left _ hh)
  have hyB : y∉B := fun hh ↦ hyC (Finset.mem_union_left _ hh)
  have hxu := (hcross x hxC).1
  have hxv := (hcross x hxC).2
  have hyu := (hcross y hyC).1
  have hyv := (hcross y hyC).2
  have huv0 : u+v≠0 := by rw [huv]; exact one_ne_zero
  have hxy0 : x+y≠0 := by rw [hxy]; exact one_ne_zero
  refine ⟨u,v,x,y,hu,hv,hx,hy,huv,hxy,hcuv,hcxy,?_,?_⟩
  · intro r hr s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with he | he | he | he <;> subst r
    · exact hav u huB s hs
    · exact hav v hvB s hs
    · exact hav x hxB s hs
    · exact hav y hyB s hs
  · intro r hr s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr hs
    rcases hr with he | he | he | he <;> subst r
    all_goals rcases hs with he | he | he | he <;> subst s
    all_goals
      first
      | exact hself _ hu
      | exact hself _ hv
      | exact hself _ hx
      | exact hself _ hy
      | assumption
      | simpa only [add_comm] using huv0
      | simpa only [add_comm] using hxy0
      | simpa only [add_comm] using hxu
      | simpa only [add_comm] using hxv
      | simpa only [add_comm] using hyu
      | simpa only [add_comm] using hyv

lemma balanced_pair_count (hF : ringChar F ≠ 2) (u v x y : F)
    (hu : u≠0) (hv : v≠0) (hx : x≠0) (hy : y≠0)
    (huv : u+v=1) (hxy : x+y=1)
    (hplus : quadraticChar F (u*v)=1) (hminus : quadraticChar F (x*y)= -1)
    (t s : F) :
    pairCount (parabolaSet {u}) (parabolaSet {v}) (t,s)+
      pairCount (parabolaSet {x}) (parabolaSet {y}) (t,s)=2 := by
  have h₁ := parabola_sum_count hF u v t s hu hv (by rw [huv]; exact one_ne_zero)
  have h₂ := parabola_sum_count hF x y t s hx hy (by rw [hxy]; exact one_ne_zero)
  rw [huv,←map_mul,hplus] at h₁
  rw [hxy,←map_mul,hminus] at h₂
  have he₁ := singleton_parabola_pair_count u v t s
  have he₂ := singleton_parabola_pair_count x y t s
  have hh : (pairCount (parabolaSet {u}) (parabolaSet {v}) (t,s) : ℤ)+
      pairCount (parabolaSet {x}) (parabolaSet {y}) (t,s)=2 := by linarith
  exact_mod_cast hh

end Erdos66BalancedRepairParameters
