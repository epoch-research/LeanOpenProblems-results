import Submission.InterceptConcurrencyPolynomialExplore
import Submission.InheritedOriginLiftExplore

/-! Quantitative exclusion of triple-collision translations, simultaneous
with nonzero/nonopposite labels and a small character energy. -/
namespace Erdos66InterceptGoodTranslation
open Polynomial Erdos66InterceptEdgePolynomial Erdos66InterceptConcurrencyPolynomial
  Erdos66CharacterTranslateSelection Erdos66InheritedOriginLift
  Erdos66TranslatedCharacterEnergy Erdos66TranslatedMixedFiber Erdos66MixedEnergy
open scoped Classical
set_option maxHeartbeats 2400000
variable {F : Type*} [Field F] [DecidableEq F]

def edges (U : Finset F) : Finset (F × F) := U ×ˢ U

noncomputable def collisionForbidden (U : Finset F) : Finset F :=
  U.biUnion (fun w ↦ (edges U).biUnion (fun e ↦ (edges U).biUnion (fun f ↦
    (edges U).biUnion (fun g ↦ (concurrencyPolynomial w e f g).roots.toFinset))))

noncomputable def oppositeForbidden (U : Finset F) : Finset F :=
  (edges U).image (fun e ↦ -(e.1+e.2)/2)

noncomputable def allForbidden (U : Finset F) : Finset F :=
  collisionForbidden U ∪ oppositeForbidden U

lemma biUnion_card_bound {α β : Type*} [DecidableEq β] (S : Finset α)
    (T : α → Finset β) (n : ℕ) (h : ∀i∈S,(T i).card≤ n) :
    (S.biUnion T).card≤ S.card*n := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤  ∑_i∈S,n := Finset.sum_le_sum h
    _ = _ := by simp

lemma polynomial_root_card (w : F) (e f g : F × F) :
    (concurrencyPolynomial w e f g).roots.toFinset.card≤ 8 :=
  (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (concurrencyPolynomial_degree w e f g))

lemma collisionForbidden_card (U : Finset F) :
    (collisionForbidden U).card≤ 8*U.card^7 := by
  have hh : (collisionForbidden U).card≤ U.card*((edges U).card*((edges U).card*((edges U).card*8))) := by
    apply biUnion_card_bound
    intro w hw
    apply biUnion_card_bound
    intro e he
    apply biUnion_card_bound
    intro f hf
    apply biUnion_card_bound
    intro g hg
    exact polynomial_root_card w e f g
  have he : (edges U).card=U.card*U.card := Finset.card_product _ _
  rw [he] at hh
  convert hh using 1
  ring

lemma oppositeForbidden_card (U : Finset F) : (oppositeForbidden U).card≤ U.card^2 := by
  have hh := @Finset.card_image_le _ _ (edges U) (fun e : F × F ↦ -(e.1+e.2)/2) _
  simpa only [edges,Finset.card_product,pow_two] using hh

lemma allForbidden_card (U : Finset F) : (allForbidden U).card≤ 8*U.card^7+U.card^2 :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add (collisionForbidden_card U) (oppositeForbidden_card U))

lemma outside_opposite (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉oppositeForbidden U) :
    (∀u∈U,a+u≠0) ∧ ∀u∈U,∀v∈U,(a+u)+(a+v)≠0 := by
  have hopp (u : F) (hu : u∈U) (v : F) (hv : v∈U) : (a+u)+(a+v)≠0 := by
    intro hh
    apply ha
    apply Finset.mem_image.mpr
    refine ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,?_⟩
    apply (div_eq_iff h2).mpr
    linear_combination -hh
  refine ⟨?_,hopp⟩
  intro u hu hz
  exact hopp u hu u hu (by rw [hz]; simp)

lemma outside_admissible (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉allForbidden U) :
    (∀u∈translated U a,u≠0) ∧ ∀u∈translated U a,∀v∈translated U a,u+v≠0 := by
  have hnot : a∉oppositeForbidden U := fun h ↦ ha (Finset.mem_union_right _ h)
  obtain ⟨hz,ho⟩ := outside_opposite h2 U a hnot
  constructor
  · intro u hu
    change u∈U.image (fun x ↦ a+x) at hu
    obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp hu
    exact hz u0 hu0
  · intro u hu v hv
    change u∈U.image (fun x ↦ a+x) at hu
    change v∈U.image (fun x ↦ a+x) at hv
    obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v0,hv0,rfl⟩ := Finset.mem_image.mp hv
    exact ho u0 hu0 v0 hv0

lemma outside_no_three_hits (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉collisionForbidden U) (w : F) (hw : w∈U)
    (e f g : F × F) (heU : e∈edges U) (hfU : f∈edges U) (hgU : g∈edges U)
    (he : e.1≠e.2) (hef : ¬SameEdge e f) (hfg : ¬SameEdge f g) (hge : ¬SameEdge g e)
    (q t k l m : F) (hw0 : a+w≠0)
    (heh : EdgeHit a w q t e k) (hfh : EdgeHit a w q t f l) (hgh : EdgeHit a w q t g m) : False := by
  have hp := concurrencyPolynomial_ne_zero h2 w e f g he hef hfg hge
  have hr : a∈(concurrencyPolynomial w e f g).roots :=
    (Polynomial.mem_roots hp).mpr (three_hits_root a w q t e f g k l m hw0 heh hfh hgh)
  apply ha
  apply Finset.mem_biUnion.mpr
  refine ⟨w,hw,Finset.mem_biUnion.mpr ⟨e,heU,Finset.mem_biUnion.mpr ⟨f,hfU,?_⟩⟩⟩
  exact Finset.mem_biUnion.mpr ⟨g,hgU,Multiset.mem_toFinset.mpr hr⟩

variable [Fintype F]

/-- The field-size cost is explicit. The same translation avoids all bad
incidences and has the character-energy bound needed for complete counts. -/
theorem exists_good_low_energy_translate (hF : ringChar F≠2) (U : Finset F)
    (hsize : 2*(8*U.card^7+U.card^2)<Fintype.card F) :
    ∃a : F, a∉allForbidden U ∧
      (∀u∈translated U a,u≠0) ∧
      (∀u∈translated U a,∀v∈translated U a,u+v≠0) ∧
      energy (signedFunction (translated U a)) (signedFunction (translated U a))≤ 8*(U.card : ℝ)^2 := by
  obtain ⟨a,ha,hE⟩ := exists_simultaneous_small_translates hF ({0} : Finset ℕ)
    (fun _ ↦ U) (allForbidden U) (by have hh := allForbidden_card U; omega)
  obtain ⟨hz,ho⟩ := outside_admissible (Ring.two_ne_zero hF) U a ha
  refine ⟨a,ha,hz,ho,?_⟩
  rw [translated,energy_signed_translate]
  simpa only [Finset.card_singleton,Nat.cast_one,mul_one] using hE 0 (Finset.mem_singleton_self 0)

end Erdos66InterceptGoodTranslation
