import Submission.ReePositiveGrid
import Submission.UnbalancedBounds

/-!
Removing the mixed terms of the Ree-style norm does not yield a free family.
The argument uses four-point fibers for EVERY nonzero semilinear coefficient,
then positive square levels for an even one-coordinate norm.
This is a construction obstruction, not a disproof of Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714ReeThreeTerm
open Erdos714ReePositive
variable {F : Type*} [Field F] [Fintype F] [CharP F 3]

/-- First produce a centered four-point fiber, with a nonzero semilinear coefficient. -/
lemma centered_fiber (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) (hq : 3 < Fintype.card F) :
    ∃ a b : F, a ≠ 0 ∧ ∃ f : Fin 4 ↪ F, ∀ i, (f i)^2-a*σ (f i)=b := by
  obtain ⟨t,ht⟩ := Erdos714ReeAxis.exists_nonfixed σ hσ hq
  let c := σ t-t
  let u := (t^2-σ t)/c
  let a := t*(t-1)/c
  have hc : c ≠ 0 := sub_ne_zero.mpr ht
  have ha : a ≠ 0 := div_ne_zero (mul_ne_zero
    (Erdos714ReeAxis.nonfixed_ne_zero σ ht)
    (sub_ne_zero.mpr (Erdos714ReeAxis.nonfixed_ne_one σ ht))) hc
  let f := Erdos714ReeAxis.rootEmbedding σ hσ t ht
  have hr (i : Fin 4) : (f i)^2+u*f i-a*σ (f i)=0 := by
    have h := Erdos714ReeAxis.embedding_roots σ hσ t ht i
    dsimp [Erdos714ReeAxis.equation] at h
    dsimp [u,a]
    apply (mul_left_cancel₀ hc)
    change c*((f i)^2+(t^2-σ t)/c*f i-(t*(t-1)/c)*σ (f i))=c*0
    field_simp
    linear_combination h
  let g : Fin 4 ↪ F := f.trans (Equiv.subRight u).toEmbedding
  refine ⟨a,u^2+a*σ u,ha,g,?_⟩
  intro i
  change (f i-u)^2-a*σ (f i-u)=u^2+a*σ u
  rw [map_sub]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) hr i

omit [Fintype F] [CharP F 3] in
/-- The map z -> z²/sigma(z) has the explicit inverse z -> z²*sigma(z). -/
lemma scale_identity (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) (z : F) :
    (z^2*σ z)^2=z*σ (z^2*σ z) := by
  rw [map_mul,map_pow,hσ]
  ring

/-- The four-point fiber exists for EVERY nonzero coefficient, not just a selected one. -/
theorem every_coefficient_fiber (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hq : 3 < Fintype.card F) (A : F) (hA : A ≠ 0) :
    ∃ b : F, ∃ f : Fin 4 ↪ F, ∀ i, (f i)^2-A*σ (f i)=b := by
  obtain ⟨a,b,ha,f,hf⟩ := centered_fiber σ hσ hq
  let z := A/a
  let s := z^2*σ z
  have hz : z ≠ 0 := div_ne_zero hA ha
  have hs : s ≠ 0 := mul_ne_zero (pow_ne_zero 2 hz) ((_root_.map_ne_zero σ).mpr hz)
  have he : A*σ s=a*s^2 := by
    rw [show s^2=z*σ s from scale_identity σ hσ z]
    dsimp [z]
    field_simp
  let g : Fin 4 ↪ F := f.trans ⟨fun x => s*x,fun _ _ h => mul_left_cancel₀ hs h⟩
  refine ⟨s^2*b,g,?_⟩
  intro i
  change (s*f i)^2-A*σ (s*f i)=s^2*b
  rw [map_mul,mul_pow]
  linear_combination s^2*(hf i) - σ (f i)*he

/-- In fact this fiber has exactly four elements, by the checked quartic eliminant. -/
theorem exact_four_fiber (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hq : 3 < Fintype.card F) (A : F) (hA : A ≠ 0) :
    ∃ b : F, (univ.filter (fun x : F => x^2-A*σ x=b)).card=4 := by
  obtain ⟨b,f,hf⟩ := every_coefficient_fiber σ hσ hq A hA
  refine ⟨b,le_antisymm ?_ ?_⟩
  · apply Erdos714ReeAxis.root_bound_four σ hσ 0 (-b) 1 (-A) one_ne_zero
    intro x hx
    have h := (mem_filter.mp hx).2
    linear_combination h
  · have hc := card_le_card_of_injOn f (s := (univ : Finset (Fin 4)))
      (t := univ.filter (fun x : F => x^2-A*σ x=b))
      (fun i _ => mem_filter.mpr ⟨mem_univ _,hf i⟩) f.injective.injOn
    simpa only [card_univ,Fintype.card_fin] using hc

/-- The even one-coordinate norm. -/
def evenNorm (σ : F →+* F) (x : F) : F := x*σ x

omit [Fintype F] [CharP F 3] in
lemma evenNorm_neg (σ : F →+* F) (x : F) : evenNorm σ (-x)=evenNorm σ x := by
  simp [evenNorm]

lemma evenNorm_square (σ : F →+* F) {x : F} (hx : x ≠ 0) : IsSquare (evenNorm σ x) := by
  have h := (IsSquare.sq x).mul (ratio_square σ hx)
  convert h using 1
  dsimp [evenNorm]
  field_simp

def normHom (σ : F →+* F) : Fˣ →* Sq (F := F) :=
  { toFun := fun u => ⟨Units.mk0 (evenNorm σ (u : F))
      (mul_ne_zero u.ne_zero ((_root_.map_ne_zero σ).mpr u.ne_zero)),
      (unit_square_iff _).mpr (evenNorm_square σ u.ne_zero)⟩
    map_one' := by apply Subtype.ext; apply Units.ext; simp [evenNorm]
    map_mul' := by
      intro u v
      apply Subtype.ext
      apply Units.ext
      change evenNorm σ ((u*v : Fˣ) : F)=evenNorm σ (u : F)*evenNorm σ (v : F)
      simp only [evenNorm,Units.val_mul,map_mul]
      ring }

lemma norm_ker_card (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) : Nat.card (normHom σ).ker ≤ 2 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  apply le_trans (card_le_card (t := ({1,-1} : Finset Fˣ)) ?_) card_le_two
  intro u hu
  have h := congrArg (fun a : Sq (F := F) => (a.val : F)) ((mem_filter.mp hu).2 : normHom σ u=1)
  change (u : F)*σ (u : F)=1 at h
  have hs := congrArg σ h
  rw [map_mul,hσ,map_one] at hs
  have he : (u : F)^2=(1 : F)^2 := by linear_combination -(u : F)^2*h+hs
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h1 | hm
  · have : u=1 := Units.ext h1
    simp [this]
  · have : u = -1 := Units.ext hm
    simp [this]

/-- Every nonzero square has a nonzero preimage under x*sigma(x). -/
lemma norm_preimage (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (r : F) (hr : r ≠ 0) (hs : IsSquare r) : ∃ b : F, b ≠ 0 ∧ evenNorm σ b=r := by
  have hsur : Function.Surjective (normHom σ) := by
    apply (normHom σ).surjective_of_card_ker_le_div
    apply (norm_ker_card σ hσ).trans
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,square_card,Fintype.card_units]
    have hq : 3 ≤ Fintype.card F := by
      have := Fintype.one_lt_card (α := F)
      have := FiniteField.odd_card_of_char_ne_two (oddChar (F := F))
      omega
    apply (Nat.le_div_iff_mul_le (by omega : 0 < (Fintype.card F-1)/2)).mpr
    omega
  let u : Fˣ := Units.mk0 r hr
  obtain ⟨b,hb⟩ := hsur ⟨u,(unit_square_iff u).mpr hs⟩
  exact ⟨b,b.ne_zero,congrArg (fun a : Sq (F := F) => (a.val : F)) hb⟩

/-- Two distinct positive square levels remain positive after any prescribed translation. -/
lemma two_positive_levels (hns : ¬ IsSquare (-1 : F)) (hq : 3 < Fintype.card F) (b : F) :
    ∃ r s : F, r ≠ s ∧ r ≠ 0 ∧ s ≠ 0 ∧ IsSquare r ∧ IsSquare s ∧
      b+r ≠ 0 ∧ IsSquare (b+r) ∧ b+s ≠ 0 ∧ IsSquare (b+s) := by
  obtain ⟨x,hx,hm,hp,hs,hsm,hsp⟩ := Erdos714ConsecutiveSquares.exists_three_squares hns hq
  by_cases hb : b=0
  · subst b
    refine ⟨1,x,?_,one_ne_zero,hx,IsSquare.one,hs,?_,?_,?_,?_⟩
    · intro h
      exact hm (by rw [← h,sub_self])
    all_goals simp_all
  by_cases hbs : IsSquare b
  · refine ⟨b*(x-1),b*x,?_,mul_ne_zero hb hm,mul_ne_zero hb hx,hbs.mul hsm,hbs.mul hs,?_,?_,?_,?_⟩
    · intro he
      have h := mul_left_cancel₀ hb he
      have : (1 : F)=0 := by linear_combination -h
      exact one_ne_zero this
    · rw [show b+b*(x-1)=b*x by ring]
      exact mul_ne_zero hb hx
    · rw [show b+b*(x-1)=b*x by ring]
      exact hbs.mul hs
    · rw [show b+b*x=b*(x+1) by ring]
      exact mul_ne_zero hb hp
    · rw [show b+b*x=b*(x+1) by ring]
      exact hbs.mul hsp
  · have hbn : -b ≠ 0 := neg_ne_zero.mpr hb
    have hbs' : IsSquare (-b) := by
      apply (quadraticChar_one_iff_isSquare hbn).mp
      rw [show -b=(-1)*b by ring,map_mul,
        quadraticChar_neg_one_iff_not_isSquare.mpr hns,
        quadraticChar_neg_one_iff_not_isSquare.mpr hbs]
      norm_num
    refine ⟨(-b)*x,(-b)*(x+1),?_,mul_ne_zero hbn hx,mul_ne_zero hbn hp,hbs'.mul hs,hbs'.mul hsp,?_,?_,?_,?_⟩
    · intro he
      have h := mul_left_cancel₀ hbn he
      have : (1 : F)=0 := by linear_combination -h
      exact one_ne_zero this
    · rw [show b+(-b)*x=(-b)*(x-1) by ring]
      exact mul_ne_zero hbn hm
    · rw [show b+(-b)*x=(-b)*(x-1) by ring]
      exact hbs'.mul hsm
    · rw [show b+(-b)*(x+1)=(-b)*x by ring]
      exact mul_ne_zero hbn hx
    · rw [show b+(-b)*(x+1)=(-b)*x by ring]
      exact hbs'.mul hs


lemma four_positive_norm_values (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 3 < Fintype.card F) (b : F) :
    ∃ f : Fin 4 ↪ F, ∀ i, b+evenNorm σ (f i)≠0 ∧ IsSquare (b+evenNorm σ (f i)) := by
  obtain ⟨r,s,hrs,hr,hs,hrq,hsq,hbr,hbrq,hbs,hbsq⟩ := two_positive_levels hns hq b
  obtain ⟨u,hu,hur⟩ := norm_preimage σ hσ r hr hrq
  obtain ⟨v,hv,hvs⟩ := norm_preimage σ hσ s hs hsq
  have huv : u ≠ v := by
    intro he
    exact hrs (hur.symm.trans ((congrArg (evenNorm σ) he).trans hvs))
  have huvn : u ≠ -v := by
    intro he
    apply hrs
    rw [← hur,he,evenNorm_neg,hvs]
  have hneg (z : F) (hz : z ≠ 0) : z ≠ -z := by
    intro he
    apply hz
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -he
  have hnu : -u ≠ v := by
    intro he
    apply huvn
    simpa only [neg_neg] using congrArg Neg.neg he
  have hnv : -u ≠ -v := fun he => huv (neg_injective he)
  let f : Fin 4 ↪ F := ⟨![u,-u,v,-v],by
    intro i j he
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals first
      | exact False.elim ((hneg u hu) he)
      | exact False.elim ((hneg u hu).symm he)
      | exact False.elim ((hneg v hv) he)
      | exact False.elim ((hneg v hv).symm he)
      | exact False.elim (huv he)
      | exact False.elim (huv.symm he)
      | exact False.elim (huvn he)
      | exact False.elim (huvn.symm he)
      | exact False.elim (hnu he)
      | exact False.elim (hnu.symm he)
      | exact False.elim (hnv he)
      | exact False.elim (hnv.symm he)⟩
  refine ⟨f,?_⟩
  intro i
  fin_cases i
  · change b+evenNorm σ u≠0 ∧ IsSquare (b+evenNorm σ u)
    rw [hur]
    exact ⟨hbr,hbrq⟩
  · change b+evenNorm σ (-u)≠0 ∧ IsSquare (b+evenNorm σ (-u))
    rw [evenNorm_neg,hur]
    exact ⟨hbr,hbrq⟩
  · change b+evenNorm σ v≠0 ∧ IsSquare (b+evenNorm σ v)
    rw [hvs]
    exact ⟨hbs,hbsq⟩
  · change b+evenNorm σ (-v)≠0 ∧ IsSquare (b+evenNorm σ (-v))
    rw [evenNorm_neg,hvs]
    exact ⟨hbs,hbsq⟩

/-- The simplified semilinear norm under investigation, not the original Ree norm. -/
def norm (σ : F →+* F) (u : Erdos714ReeNegative.Point F) : F :=
  u.2.1*σ u.2.1+u.2.2^2-u.1*σ u.2.2

omit [Fintype F] [CharP F 3] in
lemma axis_identity (σ : F →+* F) (A x y : F) :
    norm σ (Erdos714ReeNegative.relative σ (0,0,-x) (A,y,0)) =
      evenNorm σ y+x^2-A*σ x := by
  simp [norm,Erdos714ReeNegative.relative,evenNorm]

/-- Positive scalar labels on both sides, with any additional first-coordinate guard. -/
def graph (σ : F →+* F) (P : F → Prop) :
    SimpleGraph ((Erdos714ReeNegative.Point F × Label (F := F)) ⊕
      (Erdos714ReeNegative.Point F × Label (F := F))) where
  Adj u v := match u,v with
    | .inl x,.inr y => P (Erdos714ReeNegative.relative σ x.1 y.1).1 ∧
        norm σ (Erdos714ReeNegative.relative σ x.1 y.1)=(x.2.val : F)*(y.2.val : F)
    | .inr y,.inl x => P (Erdos714ReeNegative.relative σ x.1 y.1).1 ∧
        norm σ (Erdos714ReeNegative.relative σ x.1 y.1)=(x.2.val : F)*(y.2.val : F)
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> exact id
  loopless := by intro u; cases u <;> exact not_false

/-- A genuine copy at ANY prescribed nonzero first-coordinate value. -/
def copy (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 3 < Fintype.card F)
    (P : F → Prop) (A : F) (hA : A ≠ 0) (hPA : P A) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph σ P) := by
  apply Classical.choice
  obtain ⟨b,f,hf⟩ := every_coefficient_fiber σ hσ hq A hA
  obtain ⟨g,hg⟩ := four_positive_norm_values σ hσ hns hq b
  let one : Label (F := F) := ⟨1,by simp⟩
  let L : Fin 4 ↪ Erdos714ReeNegative.Point F × Label (F := F) :=
    ⟨fun i => ((0,0,-f i),one),by
      intro i j he
      exact f.injective (neg_injective (congrArg (fun p => p.1.2.2) he))⟩
  let R : Fin 4 ↪ Erdos714ReeNegative.Point F × Label (F := F) :=
    ⟨fun j => ((A,g j,0),⟨Units.mk0 (b+evenNorm σ (g j)) (hg j).1,(hg j).2⟩),by
      intro i j he
      exact g.injective (congrArg (fun p => p.1.2.1) he)⟩
  have hadj (i j : Fin 4) : (graph σ P).Adj (.inl (L i)) (.inr (R j)) := by
    refine ⟨?_,?_⟩
    · change P (A-0)
      simpa only [sub_zero] using hPA
    · change norm σ (Erdos714ReeNegative.relative σ (0,0,-f i) (A,g j,0)) =
        1*(b+evenNorm σ (g j))
      rw [axis_identity,one_mul]
      linear_combination hf i
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

theorem not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 3 < Fintype.card F)
    (P : F → Prop) (A : F) (hA : A ≠ 0) (hPA : P A) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph σ P) := by
  intro hf
  exact hf ⟨copy σ hσ hns hq P A hA hPA⟩

/-- Actual twists at every Ree order >=27; arbitrary nonempty nonzero first-coordinate filters remain covered. -/
theorem finite_not_free (m : ℕ) (hm : 0 < m) (hcard : Fintype.card F=3^(2*m+1))
    (P : F → Prop) (A : F) (hA : A ≠ 0) (hPA : P A) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (Erdos714ReeNegative.reeTwist m) P) := by
  apply not_free _ (Erdos714ReeNegative.reeTwist_square m hcard) ?_ ?_ P A hA hPA
  · intro hs
    have h := FiniteField.isSquare_neg_one_iff.mp hs
    have he : 3^(2*m+1)%4=3 := by
      rw [pow_add,pow_mul]
      simp [Nat.mul_mod,Nat.pow_mod]
    rw [hcard,he] at h
    exact h rfl
  · rw [hcard]
    exact (show 3^1=3 by norm_num) ▸
      Nat.pow_lt_pow_right (by decide : 1 < 3) (by omega : 1 < 2*m+1)


omit [CharP F 3] in
/-- If the first-coordinate guard retains only zero, scalar recovery bounds
all row degrees by q², rather than q³. -/
theorem zero_guard_edges (σ : F →+* F) (P : F → Prop) (hP : ∀ a, P a → a=0) :
    (graph σ P).edgeFinset.card ≤ Fintype.card F^6 := by
  let V := Erdos714ReeNegative.Point F × Label (F := F)
  let N := Erdos714Unbalanced.neighborhoods (graph σ P)
  have hbi : graph σ P ≤ completeBipartiteGraph V V := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [graph]
  have hinc : Erdos714Packing.incidence N=graph σ P :=
    Erdos714Unbalanced.incidence_neighborhoods _ hbi
  have hd (x : V) : (N x).card ≤ Fintype.card F^2 := by
    have h := card_le_card_of_injOn (fun y : V => (y.1.2.1,y.1.2.2))
      (s := N x) (t := (univ : Finset (F × F))) (fun _ _ => mem_univ _) (by
        intro y hy z hz he
        have hy' := (mem_filter.mp hy).2
        have hz' := (mem_filter.mp hz).2
        change P (Erdos714ReeNegative.relative σ x.1 y.1).1 ∧
          norm σ (Erdos714ReeNegative.relative σ x.1 y.1)=(x.2.val : F)*(y.2.val : F) at hy'
        change P (Erdos714ReeNegative.relative σ x.1 z.1).1 ∧
          norm σ (Erdos714ReeNegative.relative σ x.1 z.1)=(x.2.val : F)*(z.2.val : F) at hz'
        have hy0 : y.1.1=x.1.1 := sub_eq_zero.mp (hP _ hy'.1)
        have hz0 : z.1.1=x.1.1 := sub_eq_zero.mp (hP _ hz'.1)
        have hp : y.1=z.1 := Prod.ext (hy0.trans hz0.symm) he
        have hw : (y.2.val : F)=(z.2.val : F) := by
          apply mul_left_cancel₀ x.2.val.ne_zero
          rw [← hy'.2,← hz'.2,hp]
        exact Prod.ext hp (Subtype.ext (Units.ext hw)))
    simpa only [card_univ,Fintype.card_prod,pow_two] using h
  have hl : Fintype.card (Label (F := F)) ≤ Fintype.card F := by
    exact (Fintype.card_subtype_le _).trans (by rw [Fintype.card_units]; omega)
  have hv : Fintype.card V ≤ Fintype.card F^4 := by
    change Fintype.card (Erdos714ReeNegative.Point F × Label (F := F)) ≤ _
    simp only [Erdos714ReeNegative.Point,Fintype.card_prod]
    calc
      _ ≤ Fintype.card F*(Fintype.card F*Fintype.card F)*Fintype.card F := by gcongr
      _ = _ := by ring
  rw [← hinc,Erdos714Packing.incidence_edges]
  calc
    _ ≤ ∑ _x : V, Fintype.card F^2 := sum_le_sum (fun x _ => hd x)
    _ = Fintype.card V*Fintype.card F^2 := by simp
    _ ≤ Fintype.card F^4*Fintype.card F^2 := Nat.mul_le_mul_right _ hv
    _ = _ := by ring

/-- Every K44-free FULL member of the displayed filtered family has only O(q^6) edges.
This does not assert the same bound for arbitrary edge thinnings. -/
theorem free_host_edges (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬ IsSquare (-1 : F)) (hq : 3 < Fintype.card F)
    (P : F → Prop) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph σ P)) :
    (graph σ P).edgeFinset.card ≤ Fintype.card F^6 := by
  apply zero_guard_edges σ P
  intro A hPA
  by_contra hA
  exact not_free σ hσ hns hq P A hA hPA hf


#print axioms centered_fiber
#print axioms every_coefficient_fiber
#print axioms exact_four_fiber
#print axioms norm_preimage
#print axioms two_positive_levels
#print axioms four_positive_norm_values
#print axioms axis_identity
#print axioms copy
#print axioms not_free
#print axioms finite_not_free
#print axioms zero_guard_edges
#print axioms free_host_edges
end Erdos714ReeThreeTerm
