import Submission.SelectedAdditiveCoding

/-!
A sharper parallelogram count for additive evaluation codes, including codes
which are nonlinear globally but additive on a large message slice.
This is a construction obstruction, not a resolution of Erdős 714.
-/

noncomputable section
open Finset SimpleGraph Classical

namespace Erdos714AdditiveSlices

variable {V I A : Type*} [AddCommGroup V] [AddCommGroup A]
  [Fintype V] [Fintype I] [Fintype A]

omit [Fintype V] in
/-- There are at most four degenerate ordered pairs per element of a set.
The bound is local to the set, rather than to the whole message group. -/
lemma degenerate_on_set (S : Finset V) :
    ((S ×ˢ S).filter (fun p => p.1 = 0 ∨ p.2 = 0 ∨ p.1 = p.2 ∨ p.1+p.2 = 0)).card
      ≤ 4*S.card := by
  have h₀ : ((S ×ˢ S).filter (fun p => p.1 = 0)).card ≤ S.card := by
    apply card_le_card_of_injOn Prod.snd
    · intro p hp
      exact (mem_product.mp (mem_filter.mp hp).1).2
    · intro p hp q hq he
      exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) he
  have h₁ : ((S ×ˢ S).filter (fun p => p.2 = 0)).card ≤ S.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (mem_product.mp (mem_filter.mp hp).1).1
    · intro p hp q hq he
      exact Prod.ext he ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
  have h₂ : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card ≤ S.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (mem_product.mp (mem_filter.mp hp).1).1
    · intro p hp q hq he
      exact Prod.ext he ((mem_filter.mp hp).2.symm.trans
        (he.trans (mem_filter.mp hq).2))
  have h₃ : ((S ×ˢ S).filter (fun p => p.1+p.2 = 0)).card ≤ S.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (mem_product.mp (mem_filter.mp hp).1).1
    · intro p hp q hq he
      apply Prod.ext he
      apply add_left_cancel (a := p.1)
      rw [he, (mem_filter.mp hq).2]
      simpa only [← he] using (mem_filter.mp hp).2
  simp only [filter_or]
  have h := card_union_le ((S ×ˢ S).filter (fun p => p.1 = 0))
    (((S ×ˢ S).filter (fun p => p.2 = 0)) ∪
      (((S ×ˢ S).filter (fun p => p.1 = p.2)) ∪
        ((S ×ˢ S).filter (fun p => p.1+p.2 = 0))))
  have h' := card_union_le ((S ×ˢ S).filter (fun p => p.2 = 0))
    (((S ×ˢ S).filter (fun p => p.1 = p.2)) ∪
      ((S ×ˢ S).filter (fun p => p.1+p.2 = 0)))
  have h'' := card_union_le ((S ×ˢ S).filter (fun p => p.1 = p.2))
    ((S ×ˢ S).filter (fun p => p.1+p.2 = 0))
  omega

/-- Ordered nondegenerate parallelogram directions. -/
def goodPairs : Finset (V × V) :=
  univ.filter (fun p => ¬(p.1 = 0 ∨ p.2 = 0 ∨ p.1 = p.2 ∨ p.1+p.2 = 0))

/-- Nondegenerate ordered pairs in one coordinate kernel. -/
def goodKernel (l : V →+ A) : Finset (V × V) :=
  goodPairs.filter (fun p => l p.1 = 0 ∧ l p.2 = 0)

omit [Fintype A] in
lemma kernel_square_bound (l : V →+ A) :
    (univ.filter (fun v => l v = 0)).card ^ 2 ≤
      (goodKernel l).card + 4*(univ.filter (fun v => l v = 0)).card := by
  let K := univ.filter (fun v => l v = 0)
  have he : (K ×ˢ K).filter
      (fun p => ¬(p.1 = 0 ∨ p.2 = 0 ∨ p.1 = p.2 ∨ p.1+p.2 = 0)) = goodKernel l := by
    ext p
    simp only [K, goodKernel, goodPairs, mem_filter, mem_product, mem_univ, true_and]
    tauto
  have hs := card_filter_add_card_filter_not (s := K ×ˢ K)
    (p := fun p => p.1 = 0 ∨ p.2 = 0 ∨ p.1 = p.2 ∨ p.1+p.2 = 0)
  rw [he, card_product] at hs
  have hb := degenerate_on_set K
  change K.card^2 ≤ (goodKernel l).card + 4*K.card
  nlinarith

/-- Every nondegenerate pair can vanish in at most three coordinates. -/
lemma good_kernel_sum (f : V →+ (I → A))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v i => f v i))) :
    ∑ i : I, (goodKernel ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f)).card
      ≤ 3*(Fintype.card V)^2 := by
  have he : (∑ i : I, (goodKernel
      ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f)).card) =
      ∑ p ∈ (goodPairs : Finset (V × V)),
        (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card := by
    simp only [goodKernel, card_filter]
    rw [sum_comm]
    rfl
  have hb (p : V × V) (hp : p ∈ goodPairs) :
      (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card ≤ 3 := by
    have hgood : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2 ∧ p.1+p.2 ≠ 0 := by
      simpa only [goodPairs, mem_filter, mem_univ, true_and, not_or] using hp
    exact Erdos714AdditiveCoding.common_zeros_le_three f hfree
      hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2
  rw [he]
  calc
    _ ≤ ∑ _p ∈ (goodPairs : Finset (V × V)), 3 := sum_le_sum hb
    _ = 3*(goodPairs : Finset (V × V)).card := by simp [mul_comm]
    _ ≤ 3*(Fintype.card V)^2 := by
      apply Nat.mul_le_mul_left
      simpa [pow_two] using (card_le_univ (goodPairs : Finset (V × V)))

/-- The message threshold is linear, not quadratic, in the alphabet size. -/
theorem length_bound (f : V →+ (I → A))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v i => f v i)))
    (hsize : 8*Fintype.card A ≤ Fintype.card V) :
    Fintype.card I ≤ 6*(Fintype.card A)^2 := by
  have hi (i : I) : (Fintype.card V)^2 ≤ 2*(Fintype.card A)^2 *
      (goodKernel ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f)).card := by
    let l := (Pi.evalAddMonoidHom (fun _ : I => A) i).comp f
    let k := (univ.filter (fun v => l v = 0)).card
    have hk : Fintype.card V ≤ Fintype.card A*k :=
      Erdos714AdditiveCoding.card_le_alphabet_mul_kernel l
    have hk8 : 8 ≤ k := by
      have h := hsize.trans hk
      exact Nat.le_of_mul_le_mul_left (by simpa only [mul_comm] using h)
        (Fintype.card_pos (α := A))
    have hb : k^2 ≤ (goodKernel l).card + 4*k := kernel_square_bound l
    have hhalf : k^2 ≤ 2*(goodKernel l).card := by nlinarith
    have hs := Nat.pow_le_pow_left hk 2
    have ht := Nat.mul_le_mul_left ((Fintype.card A)^2) hhalf
    change (Fintype.card V)^2 ≤ 2*(Fintype.card A)^2*(goodKernel l).card
    nlinarith
  have hs := sum_le_sum (s := (univ : Finset I)) (fun i _ => hi i)
  simp only [sum_const, card_univ, smul_eq_mul, ← mul_sum] at hs
  have ht := Nat.mul_le_mul_left (2*(Fintype.card A)^2) (good_kernel_sum f hfree)
  have hp := pow_pos (Fintype.card_pos (α := V)) 2
  apply Nat.le_of_mul_le_mul_right (c := (Fintype.card V)^2) _ hp
  nlinarith [hs.trans ht]

/-- Nondegenerate directions that actually occur in a selected message set. -/
def selectedGoodKernel (l : V →+ A) (S : Finset V) : Finset (V × V) :=
  (goodKernel l).filter (fun p => p ∈ Erdos714SelectedAdditive.directions S)

omit [Fintype A] in
lemma selected_kernel_square (l : V →+ A) (S : Finset V) (D : ℕ)
    (hS : Fintype.card V ≤ D*S.card) :
    (univ.filter (fun v => l v = 0)).card ^ 2 ≤
      D^3*((selectedGoodKernel l S).card +
        4*(univ.filter (fun v => l v = 0)).card) := by
  let K := univ.filter (fun v => l v = 0)
  let T := Erdos714SelectedAdditive.kernelDirections l S
  let bad (p : V × V) := p.1 = 0 ∨ p.2 = 0 ∨ p.1 = p.2 ∨ p.1+p.2 = 0
  have hbad : (T.filter bad).card ≤ 4*K.card := by
    apply le_trans (card_le_card (t := (K ×ˢ K).filter bad) ?_) (degenerate_on_set K)
    intro p hp
    obtain ⟨ht,hb⟩ := mem_filter.mp hp
    obtain ⟨hd,hk⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_product.mpr ⟨by simpa [K] using hk.1,
      by simpa [K] using hk.2⟩, hb⟩
  have he : T.filter (fun p => ¬bad p) = selectedGoodKernel l S := by
    ext p
    simp only [T, Erdos714SelectedAdditive.kernelDirections,
      Erdos714SelectedAdditive.directions, selectedGoodKernel, goodKernel,
      goodPairs, bad, mem_filter, mem_univ, true_and]
    tauto
  have hs := card_filter_add_card_filter_not (s := T) (p := bad)
  rw [he] at hs
  have ht : T.card ≤ (selectedGoodKernel l S).card + 4*K.card := by omega
  exact (Erdos714SelectedAdditive.kernel_square_le_directions l S D hS).trans
    (Nat.mul_le_mul_left (D^3) ht)

lemma selected_good_kernel_sum (f : V →+ (I → A)) (S : Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => f v.1))) :
    ∑ i : I, (selectedGoodKernel ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) S).card
      ≤ 3*(Fintype.card V)^2 := by
  let P := (goodPairs : Finset (V × V)).filter
    (fun p => p ∈ Erdos714SelectedAdditive.directions S)
  have hset (i : I) : selectedGoodKernel
      ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) S =
      P.filter (fun p => f p.1 i = 0 ∧ f p.2 i = 0) := by
    ext p
    simp only [selectedGoodKernel, goodKernel, P, mem_filter,
      AddMonoidHom.coe_comp, Function.comp_apply]
    tauto
  have he : (∑ i : I, (selectedGoodKernel
      ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) S).card) =
      ∑ p ∈ P, (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card := by
    simp only [hset, card_filter]
    rw [sum_comm]
  have hb (p : V × V) (hp : p ∈ P) :
      (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card ≤ 3 := by
    obtain ⟨hg, hd⟩ := mem_filter.mp hp
    have hgood : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2 ∧ p.1+p.2 ≠ 0 := by
      simpa only [goodPairs, mem_filter, mem_univ, true_and, not_or] using hg
    exact Erdos714SelectedAdditive.selected_common_zeros f S hfree hd
      hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2
  rw [he]
  calc
    _ ≤ ∑ _p ∈ P, 3 := sum_le_sum hb
    _ = 3*P.card := by simp [mul_comm]
    _ ≤ 3*(Fintype.card V)^2 := by
      apply Nat.mul_le_mul_left
      simpa [pow_two] using card_le_univ P

/-- The sharper threshold also survives arbitrary positive-density message selection. -/
theorem selected_length_bound (f : V →+ (I → A)) (S : Finset V) (D : ℕ)
    (hS : Fintype.card V ≤ D*S.card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => f v.1)))
    (hsize : 8*D^3*Fintype.card A ≤ Fintype.card V) :
    Fintype.card I ≤ 6*D^3*(Fintype.card A)^2 := by
  have hi (i : I) : (Fintype.card V)^2 ≤ 2*D^3*(Fintype.card A)^2 *
      (selectedGoodKernel ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) S).card := by
    let l := (Pi.evalAddMonoidHom (fun _ : I => A) i).comp f
    let k := (univ.filter (fun v => l v = 0)).card
    have hk : Fintype.card V ≤ Fintype.card A*k :=
      Erdos714AdditiveCoding.card_le_alphabet_mul_kernel l
    have hk8 : 8*D^3 ≤ k := by
      have h := hsize.trans hk
      exact Nat.le_of_mul_le_mul_left (by simpa only [mul_comm] using h)
        (Fintype.card_pos (α := A))
    have hb : k^2 ≤ D^3*((selectedGoodKernel l S).card + 4*k) :=
      selected_kernel_square l S D hS
    have hhalf : k^2 ≤ 2*D^3*(selectedGoodKernel l S).card := by nlinarith
    have hs := Nat.pow_le_pow_left hk 2
    have ht := Nat.mul_le_mul_left ((Fintype.card A)^2) hhalf
    change (Fintype.card V)^2 ≤ 2*D^3*(Fintype.card A)^2*(selectedGoodKernel l S).card
    nlinarith
  have hs := sum_le_sum (s := (univ : Finset I)) (fun i _ => hi i)
  simp only [sum_const, card_univ, smul_eq_mul, ← mul_sum] at hs
  have ht := Nat.mul_le_mul_left (2*D^3*(Fintype.card A)^2)
    (selected_good_kernel_sum f S hfree)
  have hp := pow_pos (Fintype.card_pos (α := V)) 2
  apply Nat.le_of_mul_le_mul_right (c := (Fintype.card V)^2) _ hp
  nlinarith [hs.trans ht]

variable {R : Type*}

omit [Fintype V] in
/-- An affine-additive message slice inherits freeness from the full code. -/
theorem free_on_affine_slice (f : R → I → A) (e : V ↪ R)
    (L : V →+ (I → A)) (b : I → A)
    (hfactor : ∀ v i, f (e v) i = b i + L v i)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v i => L v i)) := by
  rw [Erdos714Coding.free_iff_agreement _ (by decide : 0 < 4)] at hfree ⊢
  intro g
  have h := hfree (g.trans e)
  have he : Erdos714Coding.agreement f (by decide : 0 < 4) (g.trans e) =
      Erdos714Coding.agreement (fun v i => L v i) (by decide : 0 < 4) g := by
    ext i
    simp [Erdos714Coding.agreement, hfactor]
  rwa [he] at h

/-- Global nonlinearity does not suffice if a large affine-additive slice remains. -/
theorem affine_slice_length_bound (f : R → I → A) (e : V ↪ R)
    (L : V →+ (I → A)) (b : I → A)
    (hfactor : ∀ v i, f (e v) i = b i + L v i)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f))
    (hsize : 8*Fintype.card A ≤ Fintype.card V) :
    Fintype.card I ≤ 6*(Fintype.card A)^2 :=
  length_bound L (free_on_affine_slice f e L b hfactor hfree) hsize

/-- A quadratic-size affine-additive slice already excludes the cubic code length. -/
theorem quadratic_slice_not_free (f : R → I → A) (e : V ↪ R)
    (L : V →+ (I → A)) (b : I → A)
    (hfactor : ∀ v i, f (e v) i = b i + L v i)
    (hq : 8 ≤ Fintype.card A)
    (hV : Fintype.card V = (Fintype.card A)^2)
    (hI : Fintype.card I = (Fintype.card A)^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f) := by
  intro hfree
  have hsize : 8*Fintype.card A ≤ Fintype.card V := by rw [hV]; nlinarith
  have hb := affine_slice_length_bound f e L b hfactor hfree hsize
  rw [hI] at hb
  have hp := pow_pos (Fintype.card_pos (α := A)) 2
  have hq6 : Fintype.card A ≤ 6 := by
    apply Nat.le_of_mul_le_mul_right (c := (Fintype.card A)^2) _ hp
    nlinarith
  omega

/-- A dense subset of a nonlinear code's affine-additive slice is also covered. -/
theorem selected_affine_slice_length_bound (f : R → I → A)
    (S : Finset V) (e : S ↪ R) (L : V →+ (I → A)) (b : I → A) (D : ℕ)
    (hfactor : ∀ v : S, ∀ i, f (e v) i = b i + L v.1 i)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f))
    (hS : Fintype.card V ≤ D*S.card)
    (hsize : 8*D^3*Fintype.card A ≤ Fintype.card V) :
    Fintype.card I ≤ 6*D^3*(Fintype.card A)^2 := by
  have hsfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => L v.1)) := by
    rw [Erdos714Coding.free_iff_agreement _ (by decide : 0 < 4)] at hfree ⊢
    intro g
    have h := hfree (g.trans e)
    have he : Erdos714Coding.agreement f (by decide : 0 < 4) (g.trans e) =
        Erdos714Coding.agreement (fun v : S => L v.1) (by decide : 0 < 4) g := by
      ext i
      simp [Erdos714Coding.agreement, hfactor]
    rwa [he] at h
  exact selected_length_bound L S D hS hsfree hsize

#print axioms degenerate_on_set
#print axioms kernel_square_bound
#print axioms good_kernel_sum
#print axioms length_bound
#print axioms selected_kernel_square
#print axioms selected_good_kernel_sum
#print axioms selected_length_bound
#print axioms free_on_affine_slice
#print axioms affine_slice_length_bound
#print axioms quadratic_slice_not_free
#print axioms selected_affine_slice_length_bound

end Erdos714AdditiveSlices
