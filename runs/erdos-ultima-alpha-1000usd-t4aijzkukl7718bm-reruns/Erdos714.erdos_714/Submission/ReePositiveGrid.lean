import Submission.ReeAxisFourRoots
import Submission.ReeNegativeGrid
import Submission.ConsecutiveSquares

/-!
An axis construction for the positive-square labelled Ree-style norm graph.
All incidences use the displayed relative-coordinate kernel. This concerns a
particular graph family, not the conjecture of Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace Erdos714ReePositive
variable {F : Type*} [Field F] [Fintype F] [CharP F 3]

abbrev Sq := Subgroup.square Fˣ

omit [Fintype F] in
lemma oddChar : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; decide

omit [Fintype F] [CharP F 3] in
lemma unit_square_iff (u : Fˣ) : IsSquare u ↔ IsSquare (u : F) := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v,congrArg Units.val hv⟩
  · rintro ⟨v,hv⟩
    have hn : v ≠ 0 := by intro h; rw [h,mul_zero] at hv; exact u.ne_zero hv
    exact ⟨Units.mk0 v hn,Units.ext hv⟩

lemma square_card : Fintype.card (Sq (F := F)) = (Fintype.card F-1)/2 := by
  have he : Subgroup.square Fˣ = (powMonoidHom 2 : Fˣ →* Fˣ).range := by
    ext x
    simp only [Subgroup.mem_square,MonoidHom.mem_range,powMonoidHom_apply,pow_two,IsSquare]
    constructor <;> rintro ⟨r,hr⟩ <;> exact ⟨r,hr.symm⟩
  change Fintype.card (Subgroup.square Fˣ) = _
  rw [← Nat.card_eq_fintype_card,he,IsCyclic.card_powMonoidHom_range]
  simp only [Nat.card_eq_fintype_card,Fintype.card_units]
  have ho := FiniteField.odd_card_of_char_ne_two (oddChar (F := F))
  have hdiv : 2 ∣ Fintype.card F-1 := by omega
  rw [Nat.gcd_eq_right hdiv]

lemma ratio_square (σ : F →+* F) {x : F} (hx : x ≠ 0) : IsSquare (σ x/x) := by
  apply (FiniteField.isSquare_iff (oddChar (F := F))
    (div_ne_zero ((_root_.map_ne_zero σ).mpr hx) hx)).mpr
  rw [div_pow,← map_pow]
  rcases FiniteField.pow_dichotomy (oddChar (F := F)) hx with h | h <;> simp [h]

/-- The automorphism ratio lands in the nonzero squares. -/
def ratioHom (σ : F →+* F) : Fˣ →* Sq (F := F) :=
  { toFun := fun u => ⟨Units.mk0 (σ (u : F)/(u : F))
      (div_ne_zero ((_root_.map_ne_zero σ).mpr u.ne_zero) u.ne_zero),
      (unit_square_iff _).mpr (ratio_square σ u.ne_zero)⟩
    map_one' := by apply Subtype.ext; apply Units.ext; simp
    map_mul' := by
      intro u v
      apply Subtype.ext
      apply Units.ext
      change σ ((u*v : Fˣ) : F)/((u*v : Fˣ) : F) =
        (σ (u : F)/(u : F))*(σ (v : F)/(v : F))
      simp only [Units.val_mul,map_mul]
      ring }

/-- The kernel consists only of the two nonzero prime-field fixed points. -/
lemma ratio_ker_card (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) :
    Nat.card (ratioHom σ).ker ≤ 2 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  apply le_trans (card_le_card (t := ({1,-1} : Finset Fˣ)) ?_) card_le_two
  intro u hu
  have h := congrArg (fun a : Sq (F := F) => (a.val : F)) ((mem_filter.mp hu).2 : ratioHom σ u=1)
  change σ (u : F)/(u : F)=1 at h
  have hf : σ (u : F)=(u : F) := (div_eq_one_iff_eq u.ne_zero).mp h
  rcases Erdos714ReeAxis.fixed_trichotomy σ hσ hf with h0 | h1 | hm
  · exact False.elim (u.ne_zero h0)
  · have : u=1 := Units.ext h1
    simp [this]
  · have : u = -1 := Units.ext hm
    simp [this]

/-- Every nonzero square is an automorphism ratio. No generator choice is needed. -/
lemma ratio_surjective (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) :
    Function.Surjective (ratioHom σ) := by
  apply (ratioHom σ).surjective_of_card_ker_le_div
  apply (ratio_ker_card σ hσ).trans
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,square_card,Fintype.card_units]
  have hq : 3 ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    have := FiniteField.odd_card_of_char_ne_two (oddChar (F := F))
    omega
  apply (Nat.le_div_iff_mul_le (by omega : 0 < (Fintype.card F-1)/2)).mpr
  omega

lemma ratio_preimage (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (k : F) (hk : k ≠ 0) (hs : IsSquare k) :
    ∃ w : F, w ≠ 0 ∧ σ w = k*w := by
  let u : Fˣ := Units.mk0 k hk
  obtain ⟨w,hw⟩ := ratio_surjective σ hσ ⟨u,(unit_square_iff u).mpr hs⟩
  have h := congrArg (fun a : Sq (F := F) => (a.val : F)) hw
  change σ (w : F)/(w : F)=k at h
  exact ⟨w,w.ne_zero,(div_eq_iff w.ne_zero).mp h⟩

omit [Fintype F] [CharP F 3] in
lemma neg_nonsquare (hns : ¬ IsSquare (-1 : F)) {a : F}
    (ha : a ≠ 0) (hs : IsSquare a) : ¬ IsSquare (-a) := by
  intro hn
  have h := hn.div hs
  rw [neg_div,div_self ha] at h
  exact hns h

/-- A nontrivial square k for which -(1+k) is also a nonzero square. -/
lemma paley_parameter (hns : ¬ IsSquare (-1 : F)) (hq : 3 < Fintype.card F) :
    ∃ k : F, k ≠ 0 ∧ k ≠ 1 ∧ IsSquare k ∧ -(1+k) ≠ 0 ∧ IsSquare (-(1+k)) := by
  obtain ⟨x,hx,hm,hp,hs,hsm,hsp⟩ := Erdos714ConsecutiveSquares.exists_three_squares hns hq
  refine ⟨(x-1)/(x+1),div_ne_zero hm hp,?_,hsm.div hsp,?_,?_⟩
  · intro he
    have he' := (div_eq_one_iff_eq hp).mp he
    have h3 := CharP.cast_eq_zero F 3
    have : (1 : F)=0 := by linear_combination h3+he'
    exact one_ne_zero this
  · have he : -(1+(x-1)/(x+1))=x/(x+1) := by
      apply (eq_div_iff hp).mpr
      field_simp
      linear_combination (norm := (ring_nf; reduce_mod_char!)) (CharP.cast_eq_zero F 3)*x
    rw [he]
    exact div_ne_zero hx hp
  · have he : -(1+(x-1)/(x+1))=x/(x+1) := by
      apply (eq_div_iff hp).mpr
      field_simp
      linear_combination (norm := (ring_nf; reduce_mod_char!)) (CharP.cast_eq_zero F 3)*x
    rw [he]
    exact hs.div hsp

/-- The one-coordinate profile of the norm at (1,t-1,0). -/
def axis (σ : F →+* F) (t : F) : F := t*σ t-t^2

omit [Fintype F] [CharP F 3] in
lemma axis_neg (σ : F →+* F) (t : F) : axis σ (-t)=axis σ t := by
  simp [axis]

/-- Two non-antipodal pairs in one axis fiber, uniformly over the field. -/
theorem four_axis_values (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 3 < Fintype.card F) :
    ∃ d : F, ∃ f : Fin 4 ↪ F, ∀ i, axis σ (f i)=d := by
  obtain ⟨k,hk,hk1,hks,hkn,hks'⟩ := paley_parameter hns hq
  obtain ⟨h,hh,hρ⟩ := ratio_preimage σ hσ k⁻¹ (inv_ne_zero hk) hks.inv
  have hρ' : σ h*k=h := by rw [hρ]; field_simp
  obtain ⟨w,hw,hω⟩ := ratio_preimage σ hσ (-(1+k)) hkn hks'
  have hw1 : w ≠ 1 := by
    intro he; subst w
    simp only [map_one,mul_one] at hω
    apply hk1
    linear_combination (norm := (ring_nf; reduce_mod_char!)) hω
  have hwm : w ≠ -1 := by
    intro he; subst w
    simp only [map_neg,map_one,mul_neg,neg_neg,mul_one] at hω
    apply hk1
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -hω
  let a := h*(w+1)
  let b := h*(w-1)
  have ha : a ≠ 0 := mul_ne_zero hh (by intro he; exact hwm (eq_neg_of_add_eq_zero_left he))
  have hb : b ≠ 0 := mul_ne_zero hh (sub_ne_zero.mpr hw1)
  have hab : a ≠ b := by
    intro he
    apply hh
    dsimp [a,b] at he
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -he
  have habn : a ≠ -b := by
    intro he
    apply mul_ne_zero hh hw
    dsimp [a,b] at he
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -he
  have hneg (z : F) (hz : z ≠ 0) : z ≠ -z := by
    intro he
    apply hz
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -he
  have hna : -a ≠ b := by
    intro he
    apply habn
    simpa only [neg_neg] using congrArg Neg.neg he
  have hnb : -a ≠ -b := fun he => hab (neg_injective he)
  let f : Fin 4 ↪ F := ⟨![a,-a,b,-b],by
    intro i j he
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals first
      | exact False.elim ((hneg a ha) he)
      | exact False.elim ((hneg a ha).symm he)
      | exact False.elim ((hneg b hb) he)
      | exact False.elim ((hneg b hb).symm he)
      | exact False.elim (hab he)
      | exact False.elim (hab.symm he)
      | exact False.elim (habn he)
      | exact False.elim (habn.symm he)
      | exact False.elim (hna he)
      | exact False.elim (hna.symm he)
      | exact False.elim (hnb he)
      | exact False.elim (hnb.symm he)⟩
  have he : axis σ a=axis σ b := by
    simp only [axis,a,b,map_mul,map_add,map_sub,map_one,hω]
    linear_combination (norm := (ring_nf; reduce_mod_char!)) (h*w)*hρ'
  refine ⟨axis σ a,f,?_⟩
  intro i
  fin_cases i
  · rfl
  · exact axis_neg σ a
  · exact he.symm
  · exact (axis_neg σ b).trans he.symm


omit [CharP F 3] in
lemma square_fiber_bound (a : F) : (univ.filter (fun z : F => z^2=a)).card ≤ 2 := by
  let P : Polynomial F := Polynomial.X^2-Polynomial.C a
  have hP : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide : 0 < 2) a
  have hsub : (univ.filter (fun z : F => z^2=a)).val ⊆ P.roots := by
    intro z hz
    apply (Polynomial.mem_roots hP).mpr
    simpa only [P,Polynomial.IsRoot.def,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C,sub_eq_zero] using (mem_filter.mp hz).2
  simpa only [P,Polynomial.natDegree_X_pow_sub_C] using Polynomial.card_le_degree_of_subset_roots hsub

/-- Positive-square coefficients make this semilinear map invertible. -/
lemma linear_surjective (σ : F →+* F) (hns : ¬ IsSquare (-1 : F))
    (a : F) (ha : a ≠ 0) (hs : IsSquare a) :
    Function.Surjective (fun v : F => σ v+a*v) := by
  apply Finite.injective_iff_surjective.mp
  intro v w he
  by_contra hn
  have hd : v-w ≠ 0 := sub_ne_zero.mpr hn
  have hratio : σ (v-w)/(v-w) = -a := by
    apply (div_eq_iff hd).mpr
    rw [map_sub]
    linear_combination he
  have hh := ratio_square σ hd
  rw [hratio] at hh
  exact neg_nonsquare hns ha hs hh

def squareValue (σ : F →+* F) (c x : F) : F := x^2-σ x+c

def positiveValues (σ : F →+* F) (c : F) : Finset F :=
  univ.filter (fun x => squareValue σ c x ≠ 0 ∧ IsSquare (squareValue σ c x))

/-- A uniform lower bound on the nonzero square values, with no character-sum estimate. -/
theorem positive_card_bound (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (c : F) :
    (Fintype.card F-1)/2 ≤ 2*(positiveValues σ c).card+4 := by
  have hsol (u : Sq (F := F)) : ∃ v : F,
      σ v+(u.val : F)*v = -(σ (u.val : F)+c) :=
    linear_surjective σ hns (u.val : F) u.val.ne_zero ((unit_square_iff u.val).mp u.property) _
  choose v hv using hsol
  let x (u : Sq (F := F)) : F := -((u.val : F)+v u)
  let z (u : Sq (F := F)) : F := (u.val : F)-v u
  have he (u : Sq (F := F)) : (z u)^2=squareValue σ c (x u) := by
    simp only [z,x,squareValue,map_neg,map_add]
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -(hv u)
  have hr (u : Sq (F := F)) : (u.val : F)=x u-z u := by
    dsimp [x,z]
    ring_nf
    reduce_mod_char!
    ring_nf
    reduce_mod_char!
  have hfiber (r : F) : (univ.filter (fun u : Sq (F := F) => x u=r)).card ≤ 2 := by
    apply le_trans (card_le_card_of_injOn z (t := univ.filter (fun w : F => w^2=squareValue σ c r)) ?_ ?_)
      (square_fiber_bound _)
    · intro u hu
      apply mem_filter.mpr
      exact ⟨mem_univ _,(he u).trans (congrArg (squareValue σ c) (mem_filter.mp hu).2)⟩
    · intro u hu u' hu' hz
      apply Subtype.ext
      apply Units.ext
      rw [hr u,hr u',(mem_filter.mp hu).2,(mem_filter.mp hu').2,hz]
  let bad := univ.filter (fun u : Sq (F := F) => squareValue σ c (x u)=0)
  let good := univ.filter (fun u : Sq (F := F) => squareValue σ c (x u)≠0)
  have hbad : bad.card ≤ 4 := by
    let S := univ.filter (fun r : F => squareValue σ c r=0)
    have hb : bad.card ≤ S.card := by
      apply card_le_card_of_injOn x
      · intro u hu
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
      · intro u hu u' hu' hx
        have hz : z u=0 := sq_eq_zero_iff.mp ((he u).trans (mem_filter.mp hu).2)
        have hz' : z u'=0 := sq_eq_zero_iff.mp ((he u').trans (mem_filter.mp hu').2)
        apply Subtype.ext
        apply Units.ext
        rw [hr u,hr u',hx,hz,hz']
    apply hb.trans
    apply Erdos714ReeAxis.root_bound_four σ hσ 0 c 1 (-1) one_ne_zero S
    intro r hr
    simpa only [squareValue,one_mul,neg_one_mul,zero_mul,add_zero,sub_eq_add_neg] using (mem_filter.mp hr).2
  have hgood : good.card ≤ 2*(positiveValues σ c).card := by
    apply card_le_mul_card_image_of_maps_to (f := x) (s := good) (t := positiveValues σ c) ?_ 2 ?_
    · intro u hu
      apply mem_filter.mpr
      refine ⟨mem_univ _,(mem_filter.mp hu).2,?_⟩
      exact (isSquare_iff_exists_sq _).mpr ⟨z u,(he u).symm⟩
    · intro r hr
      apply le_trans (card_le_card ?_) (hfiber r)
      intro u hu
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
  have htotal : good.card+bad.card=Fintype.card (Sq (F := F)) := by
    simpa only [good,bad,not_not,card_univ] using
      (card_filter_add_card_filter_not (s := (univ : Finset (Sq (F := F))))
        (fun u => squareValue σ c (x u)≠0))
  rw [square_card] at htotal
  omega

/-- Four distinct allowed axis row coordinates exist at all relevant field orders. -/
theorem four_positive_values (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 23 ≤ Fintype.card F) (c : F) :
    ∃ f : Fin 4 ↪ F, ∀ i, squareValue σ c (f i)≠0 ∧ IsSquare (squareValue σ c (f i)) := by
  have h := positive_card_bound σ hσ hns c
  have hc : 4 ≤ (positiveValues σ c).card := by omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 4) ≤ Fintype.card (positiveValues σ c) by simpa only [Fintype.card_fin,Fintype.card_coe] using hc)
  refine ⟨g.trans (Function.Embedding.subtype _),?_⟩
  intro i
  exact (mem_filter.mp (g i).property).2


omit [Fintype F] [CharP F 3] in
/-- The original relative norm, evaluated on the two displayed axes. -/
lemma axis_incidence (σ : F →+* F) (x t : F) :
    Erdos714ReeNegative.norm σ (Erdos714ReeNegative.relative σ (0,0,-x) (1,t-1,0)) =
      axis σ t+x^2-σ x-1 := by
  simp only [Erdos714ReeNegative.norm,Erdos714ReeNegative.relative,map_zero,map_one,
    map_sub,zero_sub,sub_zero,zero_mul,add_zero,neg_neg,one_mul,one_pow,axis]
  ring

abbrev Label := {u : Fˣ // IsSquare (u : F)}

/-- An actual K44 in the ORDINARY positive-square weight law N=a*b.
This is different from the previously excluded negative-square law. -/
def positiveSquareCopy (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 23 ≤ Fintype.card F) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (Erdos714ReeNegative.graph σ (fun a b : Label (F := F) => (a.val : F)*(b.val : F))) := by
  apply Classical.choice
  obtain ⟨d,f,hf⟩ := four_axis_values σ hσ hns (by omega)
  obtain ⟨g,hg⟩ := four_positive_values σ hσ hns hq (d-1)
  let one : Label (F := F) := ⟨1,by simp⟩
  let L : Fin 4 ↪ Erdos714ReeNegative.Point F × Label (F := F) :=
    ⟨fun i => ((0,0,-g i),⟨Units.mk0 (squareValue σ (d-1) (g i)) (hg i).1,(hg i).2⟩),by
      intro i j he
      exact g.injective (neg_injective (congrArg (fun p => p.1.2.2) he))⟩
  let R : Fin 4 ↪ Erdos714ReeNegative.Point F × Label (F := F) :=
    ⟨fun j => ((1,f j-1,0),one),by
      intro i j he
      exact f.injective (sub_left_injective (congrArg (fun p => p.1.2.1) he))⟩
  have hadj (i j : Fin 4) :
      Erdos714ReeNegative.norm σ (Erdos714ReeNegative.relative σ (L i).1 (R j).1) =
        ((L i).2.val : F)*((R j).2.val : F) := by
    change Erdos714ReeNegative.norm σ
      (Erdos714ReeNegative.relative σ (0,0,-g i) (1,f j-1,0)) = squareValue σ (d-1) (g i)*1
    rw [axis_incidence,hf j,mul_one]
    dsimp [squareValue]
    ring
  refine ⟨⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩⟩
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => simp at huv
    | inr j => exact hadj i j
  | inr j =>
    cases v with
    | inr i => simp at huv
    | inl i => exact hadj i j

theorem positive_square_not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 23 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714ReeNegative.graph σ (fun a b : Label (F := F) => (a.val : F)*(b.val : F))) := by
  intro h
  exact h ⟨positiveSquareCopy σ hσ hns hq⟩

/-- Every genuine Ree field of order at least 27 is covered, not only orders
containing the old q=27 example as a subfield. -/
theorem finite_positive_square_not_free (m : ℕ) (hm : 0 < m)
    (hcard : Fintype.card F=3^(2*m+1)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714ReeNegative.graph (Erdos714ReeNegative.reeTwist m)
        (fun a b : Label (F := F) => (a.val : F)*(b.val : F))) := by
  apply positive_square_not_free _ (Erdos714ReeNegative.reeTwist_square m hcard)
  · intro hs
    have h := FiniteField.isSquare_neg_one_iff.mp hs
    have he : 3^(2*m+1)%4=3 := by
      rw [pow_add,pow_mul]
      simp [Nat.mul_mod,Nat.pow_mod]
    rw [hcard,he] at h
    exact h rfl
  · have h : 3^3 ≤ 3^(2*m+1) := Nat.pow_le_pow_right (by decide : 1 ≤ 3) (by omega)
    rw [hcard]
    norm_num at h ⊢
    omega


#print axioms square_card
#print axioms ratio_square
#print axioms ratio_surjective
#print axioms ratio_preimage
#print axioms paley_parameter
#print axioms four_axis_values
#print axioms linear_surjective
#print axioms positive_card_bound
#print axioms four_positive_values
#print axioms axis_incidence
#print axioms positiveSquareCopy
#print axioms positive_square_not_free
#print axioms finite_positive_square_not_free
end Erdos714ReePositive
