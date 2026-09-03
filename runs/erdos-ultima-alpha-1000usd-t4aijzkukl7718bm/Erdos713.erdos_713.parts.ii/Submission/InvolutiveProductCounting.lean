import FormalConjecturesUtil

/-! Finite counting for a function on paired parameters. No graph-theoretic
or asymptotic hypothesis is hidden in this purely group-theoretic bound. -/
namespace Erdos713InvolutiveProductCounting
open Finset
variable {I W : Type*} [Fintype I] [Fintype W] [Group W]
set_option maxHeartbeats 2000000

lemma twice_card_le_of_missing_product (A : Finset W) (p : W)
    (h : ∀ a ∈ A, ∀ b ∈ A, a*b ≠ p) : 2*A.card ≤ Fintype.card W := by
  classical
  let C := A.image (fun b => p*b⁻¹)
  have hC : C.card = A.card := Finset.card_image_of_injective _ (by
    intro x y he
    exact inv_injective (mul_left_cancel he))
  have hd : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro a ha hc
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
    exact h (p*b⁻¹) ha b hb (by simp [mul_assoc])
  have hh := (A ∪ C).card_le_univ
  rw [Finset.card_union_of_disjoint hd,hC] at hh
  omega

open scoped Classical in
/-- If each fiber has size at most three, nondegenerate product exclusion
forces the parameter set to be small compared with the ambient group.
The error term counts equal values at paired parameters. -/
theorem card_bound (τ : I → I) (hτ : Function.Involutive τ)
    (B : I → W) (e : ℕ)
    (hfib : ∀ w, (Finset.univ.filter (fun i => B i = w)).card ≤ 3)
    (he : (Finset.univ.filter (fun i => B i = B (τ i))).card ≤ e)
    (havoid : ∀ c r d, c ≠ r → c ≠ τ r → c ≠ d → c ≠ τ d →
      B c*B (τ c) ≠ B r*B d) :
    4*Fintype.card I ≤ 3*Fintype.card W+12+2*e := by
  classical
  let S := Finset.univ.filter (fun i : I => ∀ j, B j = B i → j=i)
  let E := Finset.univ.filter (fun i : I => B i = B (τ i))
  let R := Finset.univ.image B
  have hcover : (Finset.univ : Finset I) ⊆ S ∪ S.image τ ∪ E := by
    intro c _
    by_cases hc : c ∈ S
    · exact mem_union_left _ (mem_union_left _ hc)
    by_cases hec : c ∈ E
    · exact mem_union_right _ hec
    have hbc : B c ≠ B (τ c) := by simpa [E] using hec
    have hn : ¬ ∀ j, B j = B c → j=c := by simpa [S] using hc
    push_neg at hn
    obtain ⟨r,hr,hrc⟩ := hn
    have hrτ : r ≠ τ c := by
      intro hh
      exact hbc (by simpa [hh] using hr.symm)
    have hcτ : τ c ∈ S := by
      simp only [S,mem_filter,mem_univ,true_and]
      intro d hd
      by_contra hdτ
      have hdc : d ≠ c := by
        intro hh
        exact hbc (by simpa [hh] using hd)
      refine havoid c r d (Ne.symm hrc) ?_ (Ne.symm hdc) ?_ ?_
      · intro hh
        exact hrτ (by simpa only [hτ r] using (congrArg τ hh).symm)
      · intro hh
        exact hdτ (by simpa only [hτ d] using (congrArg τ hh).symm)
      · rw [hr,hd]
    exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨τ c,hcτ,hτ c⟩))
  have hqS : Fintype.card I ≤ 2*S.card+e := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (S ∪ S.image τ) E
    have h3 := Finset.card_union_le S (S.image τ)
    have h4 := Finset.card_image_le (s := S) (f := τ)
    change E.card ≤ e at he
    simp only [card_univ] at h1
    omega
  have hSinj : Set.InjOn B S := by
    intro a ha b _ hab
    exact ((mem_filter.mp ha).2 b hab.symm).symm
  have hST : (S.image B).card = S.card := Finset.card_image_of_injOn hSinj
  have hRS : S.image B ⊆ R := Finset.image_subset_image (filter_subset _ _)
  have hremaining : ((Finset.univ \ S).image B) ⊆ R \ S.image B := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw
    refine mem_sdiff.mpr ⟨mem_image_of_mem B (mem_univ i),?_⟩
    intro hh
    obtain ⟨j,hj,hji⟩ := mem_image.mp hh
    have hij := (mem_filter.mp hj).2 i hji.symm
    exact (mem_sdiff.mp hi).2 (hij ▸ hj)
  have hremfib : ∀ w ∈ (Finset.univ \ S).image B,
      ((Finset.univ \ S).filter (fun i => B i = w)).card ≤ 3 := by
    intro w _
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (sdiff_subset))).trans (hfib w)
  have hqR : Fintype.card I+2*S.card ≤ 3*R.card := by
    have h1 := Finset.card_le_mul_card_image (Finset.univ \ S) 3 hremfib
    have h2 := Finset.card_le_card hremaining
    have h3 := Finset.card_le_card hRS
    have h4 : S.card ≤ Fintype.card I := S.card_le_univ
    rw [card_sdiff_of_subset (subset_univ S),card_univ] at h1
    rw [card_sdiff_of_subset hRS,hST] at h2
    rw [hST] at h3
    omega
  have hR : 2*R.card ≤ Fintype.card W+4 := by
    rcases isEmpty_or_nonempty I with hI | hI
    · have hq : Fintype.card I = 0 := Fintype.card_eq_zero
      have hh : R.card ≤ Fintype.card I := by
        simpa only [card_univ] using (Finset.card_image_le (s := Finset.univ) (f := B))
      omega
    · obtain ⟨c⟩ := hI
      let T : Finset I := Finset.univ \ {c,τ c}
      let A := T.image B
      have hA : 2*A.card ≤ Fintype.card W := by
        apply twice_card_le_of_missing_product A (B c*B (τ c))
        intro a ha b hb hab
        obtain ⟨r,hr,rfl⟩ := mem_image.mp ha
        obtain ⟨d,hd,rfl⟩ := mem_image.mp hb
        have hr' : r ≠ c ∧ r ≠ τ c := by simpa [T] using hr
        have hd' : d ≠ c ∧ d ≠ τ c := by simpa [T] using hd
        apply havoid c r d hr'.1.symm ?_ hd'.1.symm ?_ hab.symm
        · intro hh
          exact hr'.2 (by simpa only [hτ r] using (congrArg τ hh).symm)
        · intro hh
          exact hd'.2 (by simpa only [hτ d] using (congrArg τ hh).symm)
      have hRA : R ⊆ A ∪ {B c,B (τ c)} := by
        intro w hw
        obtain ⟨i,_,rfl⟩ := mem_image.mp hw
        by_cases hi : i=c ∨ i=τ c
        · exact mem_union_right _ (by simpa only [mem_insert,mem_singleton] using (hi.imp (congrArg B) (congrArg B)))
        · exact mem_union_left _ (mem_image.mpr ⟨i,by simpa [T] using hi,rfl⟩)
      have h1 := Finset.card_le_card hRA
      have h2 := Finset.card_union_le A {B c,B (τ c)}
      have h3 := Finset.card_le_two (a := B c) (b := B (τ c))
      omega
  omega

#print axioms twice_card_le_of_missing_product
#print axioms card_bound
end Erdos713InvolutiveProductCounting
