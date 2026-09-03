import Submission.PrefixFaithfulParabolaLiftExplore

/-! Exact size of the prefix-preserving parabola lift, including the removed
common origin. The full lift amplifies the old mass by p-1. -/
namespace Erdos66FaithfulParabolaCardinality
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph
  Erdos66InheritedOriginLift Erdos66ShearedParabolaPrefix Erdos66PrefixFaithfulParabolaLift
open scoped Classical
set_option maxHeartbeats 1600000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma punctured_parabola_card (U : Finset F) (hU : ∀ u∈U, u≠0) :
    ((parabolaSet U).erase 0).card=U.card*(Fintype.card F-1) := by
  have he : (U ×ˢ (Finset.univ.erase (0:F))).card=((parabolaSet U).erase 0).card := by
    apply Finset.card_bij (fun ux _ ↦ (ux.2,ux.2^2/ux.1))
    · intro ux hux
      obtain ⟨hu,hx⟩ := Finset.mem_product.mp hux
      have hx0 := (Finset.mem_erase.mp hx).1
      apply Finset.mem_erase.mpr
      refine ⟨fun hh ↦ hx0 (congrArg Prod.fst hh),?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ux.1,hu,rfl⟩
    · intro ux hux vy hvy he
      obtain ⟨hu,hx⟩ := Finset.mem_product.mp hux
      obtain ⟨hv,hy⟩ := Finset.mem_product.mp hvy
      have hx0 := (Finset.mem_erase.mp hx).1
      have hxy := congrArg Prod.fst he
      have hdiv := congrArg Prod.snd he
      dsimp only [Prod.fst,Prod.snd] at hxy hdiv
      rw [←hxy] at hdiv
      have hm := (div_eq_div_iff (hU ux.1 hu) (hU vy.1 hv)).mp hdiv
      have huv : ux.1=vy.1 := (mul_left_cancel₀ (pow_ne_zero 2 hx0) hm).symm
      exact Prod.ext huv hxy
    · intro z hz
      obtain ⟨hz0,hz⟩ := Finset.mem_erase.mp hz
      obtain ⟨u,hu,he⟩ := (Finset.mem_filter.mp hz).2
      have hx0 : z.1≠0 := by
        intro hx
        have hy : z.2=0 := by simpa only [hx,zero_pow (by norm_num : (2:ℕ)≠0),zero_div] using he
        exact hz0 (Prod.ext hx hy)
      refine ⟨(u,z.1),Finset.mem_product.mpr ⟨hu,Finset.mem_erase.mpr ⟨hx0,Finset.mem_univ _⟩⟩,?_⟩
      exact Prod.ext rfl he.symm
  rw [Finset.card_product,Finset.card_erase_of_mem (Finset.mem_univ (0:F)),Finset.card_univ] at he
  exact he.symm

lemma faithfulLift_card (U : Finset F) (a : F)
    (hU : ∀ u∈translated U a, u≠0) :
    (faithfulLift U a).card=U.card*(Fintype.card F-1) := by
  have hs : Function.Injective (fun z : F × F ↦ (-a,0)+z) := add_right_injective _
  have he := Finset.image_erase hs (sheared (translated U a)) 0
  simp only [add_zero] at he
  unfold faithfulLift shiftSet
  rw [←he, Finset.card_image_of_injective _ hs]
  have he' := Finset.image_erase shear.injective (parabolaSet (translated U a)) 0
  simp only [map_zero] at he'
  rw [sheared, ←he', Finset.card_image_of_injective _ shear.injective]
  rw [punctured_parabola_card _ hU,translated_card]

lemma encodePlane_injective (p : ℕ) [NeZero p] :
    Function.Injective (fun z : ZMod p × ZMod p ↦ z.1.val+p*z.2.val) := by
  intro z w he
  have hx := z.1.val_lt
  have hy := w.1.val_lt
  have hp : 0<p := NeZero.pos p
  have hm := congrArg (fun n : ℕ ↦ n%p) he
  have hd := congrArg (fun n : ℕ ↦ n/p) he
  have h₁ : z.1.val=w.1.val := by simpa [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hm
  have h₂ : z.2.val=w.2.val := by
    dsimp only at he
    rw [h₁] at he
    exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel he)
  exact Prod.ext (ZMod.val_injective p h₁) (ZMod.val_injective p h₂)

lemma encodePlane_card (p : ℕ) [NeZero p] (B : Finset (ZMod p × ZMod p)) :
    (encodePlane p B).card=B.card := Finset.card_image_of_injective _ (encodePlane_injective p)

lemma encodePlane_lt (p : ℕ) [NeZero p] (B : Finset (ZMod p × ZMod p)) {n : ℕ}
    (hn : n∈encodePlane p B) : n<p^2 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
  have hx := z.1.val_lt
  have hy := z.2.val_lt
  nlinarith

lemma faithful_encoded_card (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p)) (a : ZMod p)
    (hU : ∀ u∈translated U a, u≠0) :
    (encodePlane p (faithfulLift U a)).card=U.card*(p-1) := by
  rw [encodePlane_card,faithfulLift_card U a hU,ZMod.card]

end Erdos66FaithfulParabolaCardinality
