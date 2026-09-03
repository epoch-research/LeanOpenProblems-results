import Submission.SymmetricSidonExplore

/-! Reusing template vertices across many designated sum targets. Opposite
translations preserve the entire mixed profile. These identities do not
construct a template for the exceptional sets in Erdos 66. -/
namespace Erdos66ReusableSidonTemplate
open Erdos66OriginRepair Erdos66SymmetricSidon
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def shift (t : ℤ) (A : Finset ℤ) : Finset ℤ := A.image (fun a ↦ t+a)

lemma mem_shift (t a : ℤ) (A : Finset ℤ) : a ∈ shift t A ↔ a-t ∈ A := by
  simp only [shift, Finset.mem_image]
  constructor
  · rintro ⟨b,hb,rfl⟩
    simpa using hb
  · intro h
    exact ⟨a-t,h,by omega⟩

lemma shift_zero (A : Finset ℤ) : shift 0 A = A := by
  ext a
  simp only [mem_shift, sub_zero]

lemma shift_card (t : ℤ) (A : Finset ℤ) : (shift t A).card = A.card := by
  exact Finset.card_image_of_injective _ (fun a b h ↦ by omega)

lemma pairCount_shift (s t z : ℤ) (A B : Finset ℤ) :
    pairCount (shift s A) (shift t B) z = pairCount A B (z-s-t) := by
  change ((A.image (fun a ↦ s+a)).filter (fun a ↦ z-a ∈ shift t B)).card = _
  rw [Finset.filter_image]
  have he : A.filter (fun a ↦ z-(s+a) ∈ shift t B) = A.filter (fun a ↦ z-s-t-a ∈ B) := by
    ext a
    simp only [Finset.mem_filter, mem_shift]
    rw [show z-(s+a)-t = z-s-t-a by omega]
  rw [he, Finset.card_image_of_injective _ (fun a b h ↦ by omega)]
  rfl

lemma pairCount_shift_right (t z : ℤ) (A B : Finset ℤ) :
    pairCount A (shift t B) z = pairCount A B (z-t) := by
  simpa only [shift_zero, sub_zero] using pairCount_shift 0 t z A B

lemma pairCount_shift_left (s z : ℤ) (A B : Finset ℤ) :
    pairCount (shift s A) B z = pairCount A B (z-s) := by
  simpa only [shift_zero, sub_zero] using pairCount_shift s 0 z A B

lemma sidon_shift (t : ℤ) {A : Finset ℤ} (hA : IsSidon A) : IsSidon (shift t A) := by
  intro a ha b hb c hc d hd he
  have hh := hA (a-t) ((mem_shift t a A).mp ha) (b-t) ((mem_shift t b A).mp hb)
    (c-t) ((mem_shift t c A).mp hc) (d-t) ((mem_shift t d A).mp hd) (by omega)
  rcases hh with ⟨h,h'⟩ | ⟨h,h'⟩ <;> omega

noncomputable def reusable (U V : Finset ℤ) (t : ℤ) : Finset ℤ := shift t U ∪ shift (-t) V

lemma reusable_card (U V : Finset ℤ) (t : ℤ) (hdis : Disjoint (shift t U) (shift (-t) V)) :
    (reusable U V t).card = U.card+V.card := by
  rw [reusable, Finset.card_union_of_disjoint hdis, shift_card, shift_card]

/-- Every cross edge survives the opposite translations. Thus |U|+|V|
vertices can contribute |U||V| designated unordered edges. -/
lemma reusable_exact (U V : Finset ℤ) (t z : ℤ)
    (hdis : Disjoint (shift t U) (shift (-t) V)) :
    pairCount (reusable U V t) (reusable U V t) z =
      pairCount U U (z-2*t) + 2*pairCount U V z + pairCount V V (z+2*t) := by
  rw [reusable, pairCount_union_self _ _ _ hdis, pairCount_shift,
    pairCount_shift, pairCount_shift, pairCount_comm V U]
  rw [show z-t-t=z-2*t by omega, show z- -t- -t=z+2*t by omega,
    show z- -t-t=z by omega]

lemma reusable_profile_bounds (U V : Finset ℤ) (hU : IsSidon U) (hV : IsSidon V)
    (t : ℤ) (hdis : Disjoint (shift t U) (shift (-t) V)) (z : ℤ) :
    2*pairCount U V z ≤ pairCount (reusable U V t) (reusable U V t) z ∧
      pairCount (reusable U V t) (reusable U V t) z ≤ 2*pairCount U V z+4 := by
  rw [reusable_exact U V t z hdis]
  have h1 := sidon_self_le_two hU (z-2*t)
  have h2 := sidon_self_le_two hV (z+2*t)
  omega

lemma reusable_old_mixed (A U V : Finset ℤ) (t z : ℤ)
    (hdis : Disjoint (shift t U) (shift (-t) V)) :
    pairCount (reusable U V t) A z = pairCount U A (z-t)+pairCount V A (z+t) := by
  rw [reusable, pairCount_union_left _ _ _ _ hdis, pairCount_shift_left, pairCount_shift_left]
  congr 1
  congr 1
  omega

/-- Translating a fixed template moves its old-set mixed peaks; it cannot
lower their uniform bound over all integer targets. -/
lemma uniform_mixed_shift_iff (A U : Finset ℤ) (t : ℤ) (R : ℕ) :
    (∀ z, pairCount (shift t U) A z ≤ R) ↔ (∀ z, pairCount U A z ≤ R) := by
  simp only [pairCount_shift_left]
  constructor
  · intro h z
    simpa only [add_sub_cancel_right] using h (z+t)
  · intro h z
    exact h (z-t)

lemma reusable_preserves_mixed_peak (A U V : Finset ℤ) (t z : ℤ)
    (hdis : Disjoint (shift t U) (shift (-t) V)) :
    pairCount U A z ≤ pairCount (reusable U V t) A (z+t) := by
  rw [reusable_old_mixed _ _ _ _ _ hdis, add_sub_cancel_right]
  omega

/-- If a reusable template is independently known to be mixed-flat with
A, the full prescribed cross profile can be adjoined with bounded error. -/
theorem reusable_union_profile (A U V : Finset ℤ) (hU : IsSidon U) (hV : IsSidon V)
    (t : ℤ) (hdis : Disjoint (shift t U) (shift (-t) V))
    (hA : Disjoint A (reusable U V t)) (R : ℕ)
    (hUA : ∀ z, pairCount U A z ≤ R) (hVA : ∀ z, pairCount V A z ≤ R) (z : ℤ) :
    pairCount A A z + 2*pairCount U V z ≤
        pairCount (A∪reusable U V t) (A∪reusable U V t) z ∧
      pairCount (A∪reusable U V t) (A∪reusable U V t) z ≤
        pairCount A A z + 2*pairCount U V z + 4*R+4 := by
  rw [pairCount_union_self _ _ _ hA]
  have hp := reusable_profile_bounds U V hU hV t hdis z
  have hm := reusable_old_mixed A U V t z hdis
  have h1 := hUA (z-t)
  have h2 := hVA (z+t)
  omega

end Erdos66ReusableSidonTemplate
