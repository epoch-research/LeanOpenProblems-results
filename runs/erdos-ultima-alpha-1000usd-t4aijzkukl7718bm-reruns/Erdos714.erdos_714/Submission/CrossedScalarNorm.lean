import Submission.VoltageFusion

/-!
Crossed affine scalar tags still have a complete-block edge partition. This
excludes a specific construction, not arbitrary relabelled local factors and
not the original extremal conjecture. The functions f, g and ν are arbitrary.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714CrossedScalar
open Erdos714Packing
variable {F X Y : Type*} [Field F] [Fintype F] [Fintype X] [Fintype Y]
abbrev Row := X × F × F
abbrev Col := Y × F × F
abbrev Index := X × F × F × Fˣ

def neighbors (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (p : Row (F := F) (X := X)) : Finset (Col (F := F) (Y := Y)) :=
  univ.filter (fun c => ν p.1 c.1 ≠ 0 ∧
    ν p.1 c.1 = (p.2.1+c.2.2*f p.1)*(c.2.1+p.2.2*(g c.1 : F)))

def graph (ν : X → Y → F) (f : X → F) (g : Y → Fˣ) := incidence (neighbors ν f g)

def fiber (ν : X → Y → F) (g : Y → Fˣ) (x : X) (D : Fˣ) : Finset Y :=
  univ.filter (fun y => ν x y = (D : F)*(g y : F))

def rows (f : X → F) (i : Index (F := F) (X := X)) :
    Fˣ ↪ Row (F := F) (X := X) :=
  ⟨fun u => (i.1, (i.2.2.2 : F)/(u : F)-i.2.1*f i.1, (u : F)-i.2.2.1), by
    intro u v h
    apply Units.ext
    exact sub_left_injective (congrArg (fun p => p.2.2) h)⟩

def columns (ν : X → Y → F) (g : Y → Fˣ) (i : Index (F := F) (X := X)) :
    fiber ν g i.1 i.2.2.2 ↪ Col (F := F) (Y := Y) :=
  ⟨fun y => (y.val, i.2.2.1*(g y.val : F), i.2.1),
    fun _ _ h => Subtype.ext (congrArg Prod.fst h)⟩

omit [Fintype X] in
lemma block_incidence (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (i : Index (F := F) (X := X)) (u : Fˣ) (y : fiber ν g i.1 i.2.2.2) :
    columns ν g i y ∈ neighbors ν f g (rows f i u) := by
  have hy := (mem_filter.mp y.property).2
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_, ?_⟩
  · exact hy.trans_ne (mul_ne_zero i.2.2.2.ne_zero (g y.val).ne_zero)
  · change ν i.1 y.val =
      ((i.2.2.2 : F)/(u : F)-i.2.1*f i.1+i.2.1*f i.1)*
      (i.2.2.1*(g y.val : F)+((u : F)-i.2.2.1)*(g y.val : F))
    rw [hy]
    field_simp
    ring

def block (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (R : Row (F := F) (X := X) → Finset (Col (F := F) (Y := Y)))
    (i : Index (F := F) (X := X)) (u : Fˣ) : Finset (fiber ν g i.1 i.2.2.2) :=
  univ.filter (fun y => columns ν g i y ∈ R (rows f i u))

omit [Fintype F] [Fintype X] in
lemma block_free (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (R : Row (F := F) (X := X) → Finset (Col (F := F) (Y := Y)))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R))
    (i : Index (F := F) (X := X)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (block ν f g R i)) := by
  rw [free_iff_no_rectangle _ (by decide)] at hf ⊢
  intro a b h
  exact hf (a.trans (rows f i)) (b.trans (columns ν g i))
    (fun j k => (mem_filter.mp (h j k)).2)

/-- An edge determines x, s, B=b/g(y), and D=ν(x,y)/g(y) uniquely. -/
lemma edge_partition (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (R : Row (F := F) (X := X) → Finset (Col (F := F) (Y := Y)))
    (hR : ∀ p, R p ⊆ neighbors ν f g p) :
    (incidence R).edgeFinset.card =
      ∑ i : Index (F := F) (X := X), ∑ u : Fˣ, (block ν f g R i u).card := by
  let e : (Σ i : Index (F := F) (X := X), Σ u : Fˣ, block ν f g R i u) →
      (Σ p : Row (F := F) (X := X), R p) := fun z =>
    ⟨rows f z.1 z.2.1, columns ν g z.1 z.2.2.val, (mem_filter.mp z.2.2.property).2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨⟨x,s,B,D⟩,u,⟨y,hy⟩⟩ ⟨⟨x',s',B',D'⟩,u',⟨y',hy'⟩⟩ h
      have hx : x=x' := congrArg (fun z => z.1.1) h
      have hs : s=s' := congrArg (fun z => z.2.val.2.2) h
      have hyy : y.val=y'.val := congrArg (fun z => z.2.val.1) h
      have hB : B=B' := by
        have hh : B*(g y.val : F)=B'*(g y'.val : F) := congrArg (fun z => z.2.val.2.1) h
        rw [← hyy] at hh
        exact mul_right_cancel₀ (g y.val).ne_zero hh
      have hu : u=u' := by
        apply Units.ext
        have hh : (u : F)-B=(u' : F)-B' := congrArg (fun z => z.1.2.2) h
        rw [← hB] at hh
        exact sub_left_injective hh
      subst x'; subst s'; subst B'; subst u'
      have hD : D=D' := by
        apply Units.ext
        have h1 := (mem_filter.mp y.property).2
        have h2 := (mem_filter.mp y'.property).2
        rw [← hyy] at h2
        exact mul_right_cancel₀ (g y.val).ne_zero (h1.symm.trans h2)
      subst D'
      have hy' : y=y' := Subtype.ext hyy
      subst y'
      rfl
    · rintro ⟨⟨x,a,t⟩,⟨⟨y,b,s⟩,hh⟩⟩
      have hn := (mem_filter.mp (hR (x,a,t) hh)).2
      change ν x y ≠ 0 ∧ ν x y=(a+s*f x)*(b+t*(g y : F)) at hn
      let B : F := b/(g y : F)
      have hB : B*(g y : F)=b := div_mul_cancel₀ _ (g y).ne_zero
      have hu0 : B+t ≠ 0 := by
        intro hz
        apply hn.1
        rw [hn.2]
        have he : b+t*(g y : F)=0 := by linear_combination (g y : F)*hz-hB
        rw [he,mul_zero]
      let u : Fˣ := Units.mk0 (B+t) hu0
      let D : Fˣ := Units.mk0 (ν x y/(g y : F)) (div_ne_zero hn.1 (g y).ne_zero)
      have hD : ν x y=(D : F)*(g y : F) := (div_mul_cancel₀ _ (g y).ne_zero).symm
      have ha : (D : F)/(u : F)-s*f x=a := by
        have hd : (D : F)=(a+s*f x)*(u : F) := by
          apply mul_right_cancel₀ (g y).ne_zero
          rw [← hD,hn.2]
          change (a+s*f x)*(b+t*(g y : F))=(a+s*f x)*(B+t)*(g y : F)
          linear_combination -(a+s*f x)*hB
        rw [hd,mul_div_cancel_right₀ _ u.ne_zero,add_sub_cancel_right]
      have ht : (u : F)-B=t := by dsimp [u]; ring
      refine ⟨⟨(x,s,B,D),u,⟨⟨y,mem_filter.mpr ⟨mem_univ _,hD⟩⟩,?_⟩⟩,?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        simpa only [rows,columns,Function.Embedding.coeFn_mk,ha,ht,hB] using hh
      · apply Sigma.subtype_ext
        · exact Prod.ext rfl (Prod.ext ha ht)
        · exact Prod.ext rfl (Prod.ext hB rfl)
  have hc := Fintype.card_congr (Equiv.ofBijective e he)
  rw [incidence_edges]
  simpa only [Fintype.card_sigma,Fintype.card_coe] using hc.symm

omit [Fintype X] in
/-- The nonzero fibers partition precisely the points where ν is nonzero. -/
lemma fiber_sum (ν : X → Y → F) (g : Y → Fˣ) (x : X) :
    ∑ D : Fˣ, (fiber ν g x D).card =
      (univ.filter (fun y : Y => ν x y ≠ 0)).card := by
  let e : (Σ D : Fˣ, fiber ν g x D) → {y : Y // y ∈ univ.filter (fun y => ν x y ≠ 0)} :=
    fun z => ⟨z.2.val, mem_filter.mpr ⟨mem_univ _,
      ((mem_filter.mp z.2.property).2).trans_ne (mul_ne_zero z.1.ne_zero (g z.2.val).ne_zero)⟩⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨D,y⟩ ⟨D',y'⟩ h
      have hy : y.val=y'.val := congrArg Subtype.val h
      have hD : D=D' := by
        apply Units.ext
        have h1 := (mem_filter.mp y.property).2
        have h2 := (mem_filter.mp y'.property).2
        rw [←hy] at h2
        exact mul_right_cancel₀ (g y.val).ne_zero (h1.symm.trans h2)
      subst D'
      have hy' : y=y' := Subtype.ext hy
      subst y'
      rfl
    · intro y
      let D : Fˣ := Units.mk0 (ν x y.val/(g y.val : F))
        (div_ne_zero (mem_filter.mp y.property).2 (g y.val).ne_zero)
      refine ⟨⟨D,⟨y.val,mem_filter.mpr ⟨mem_univ _,?_⟩⟩⟩,rfl⟩
      exact (div_mul_cancel₀ _ (g y.val).ne_zero).symm
  have h := Fintype.card_congr (Equiv.ofBijective e he)
  simpa only [Fintype.card_sigma,Fintype.card_coe] using h

/-- No upper bound or regularity of the ν/g fibers is required. -/
lemma weight_sum (ν : X → Y → F) (g : Y → Fˣ) :
    (∑ i : Index (F := F) (X := X),
      ((fiber ν g i.1 i.2.2.2).card+Fintype.card F)) ≤
      Fintype.card X*Fintype.card F^2*(Fintype.card Y+Fintype.card F^2) := by
  have hu : Fintype.card Fˣ ≤ Fintype.card F := by
    rw [Fintype.card_units]; exact Nat.sub_le _ _
  have hb (x : X) : (∑ D : Fˣ, ((fiber ν g x D).card+Fintype.card F)) ≤
      Fintype.card Y+Fintype.card F^2 := by
    rw [sum_add_distrib,fiber_sum]
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
    have hc := card_filter_le (univ : Finset Y) (fun y => ν x y ≠ 0)
    simp only [card_univ] at hc
    calc
      _ ≤ Fintype.card Y+Fintype.card F*Fintype.card F := by gcongr
      _ = _ := by ring
  simp only [Index,Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _x : X, ∑ _s : F, ∑ _B : F, (Fintype.card Y+Fintype.card F^2) := by
      gcongr with x _ s _ B _
      exact hb x
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]; ring

/-- Every K44-free selected edge set loses a power at the critical scale. -/
theorem set_system_fourth (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (R : Row (F := F) (X := X) → Finset (Col (F := F) (Y := Y)))
    (hR : ∀ p, R p ⊆ neighbors ν f g p)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R))
    (hX : Fintype.card X ≤ Fintype.card F^2)
    (hY : Fintype.card Y ≤ Fintype.card F^2) :
    (incidence R).edgeFinset.card^4 ≤ 10752*Fintype.card F^27 := by
  let q := Fintype.card F
  let I := Index (F := F) (X := X)
  let w (i : I) := (fiber ν g i.1 i.2.2.2).card+q
  let e (i : I) := ∑ u : Fˣ, (block ν f g R i u).card
  have hq : 0 < q := Fintype.card_pos
  have hu : Fintype.card Fˣ ≤ q := by rw [Fintype.card_units]; exact Nat.sub_le _ _
  have hb (i : I) : 1*(e i)^4 ≤ (672*q^3)*(w i)^4 := by
    have h := Erdos714Unbalanced.fourth_power_bound (block ν f g R i) (block_free ν f g R hf i)
    simp only [Fintype.card_coe] at h
    have hw : q ≤ w i := Nat.le_add_left _ _
    have hn : (fiber ν g i.1 i.2.2.2).card ≤ w i := Nat.le_add_right _ _
    have hp : q^4 ≤ q^3*(w i)^4 := by
      have h1 : 1 ≤ q^3 := Nat.one_le_pow _ _ hq
      calc
        _ ≤ (w i)^4 := Nat.pow_le_pow_left hw 4
        _ = 1*(w i)^4 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ h1
    simp only [one_mul]
    calc
      (e i)^4 ≤ 24*q^3*(fiber ν g i.1 i.2.2.2).card^4+648*q^4 := h.trans (by gcongr)
      _ ≤ 24*q^3*(w i)^4+648*(q^3*(w i)^4) := by gcongr
      _ = _ := by ring
  have hs : (∑ i : I, w i) ≤ 2*q^6 := by
    calc
      _ ≤ Fintype.card X*q^2*(Fintype.card Y+q^2) := weight_sum ν g
      _ ≤ q^2*q^2*(q^2+q^2) := by gcongr
      _ = _ := by ring
  have h := Erdos714FusionBounds.sum_relative_fourth e w 1 (672*q^3) (by decide) hb
  simp only [one_mul] at h
  rw [edge_partition ν f g R hR]
  calc
    (∑ i : I, e i)^4 ≤ (672*q^3)*(∑ i : I, w i)^4 := h
    _ ≤ (672*q^3)*(2*q^6)^4 := by gcongr
    _ = _ := by ring

/-- The bound applies to arbitrary spanning graph edge thinnings. -/
theorem graph_fourth (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (H : SimpleGraph (Row (F := F) (X := X) ⊕ Col (F := F) (Y := Y)))
    (hH : H ≤ graph ν f g) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F^2)
    (hY : Fintype.card Y ≤ Fintype.card F^2) :
    H.edgeFinset.card^4 ≤ 10752*Fintype.card F^27 := by
  let R := Erdos714Unbalanced.neighborhoods H
  have hbi : H ≤ completeBipartiteGraph (Row (F := F) (X := X)) (Col (F := F) (Y := Y)) := by
    intro a b hab
    have h := hH hab
    cases a <;> cases b <;> simp_all [graph]
  have he : incidence R = H := Erdos714Unbalanced.incidence_neighborhoods H hbi
  have hr : ∀ p, R p ⊆ neighbors ν f g p := by
    intro p c hc
    exact hH ((mem_filter.mp hc).2 : H.Adj (.inl p) (.inr c))
  have hb := set_system_fourth ν f g R hr (by rwa [he]) hX hY
  rw [he] at hb
  exact hb

/-- The host has q²(q-1) edges for each nonzero point-pair value. -/
theorem edge_count (ν : X → Y → F) (f : X → F) (g : Y → Fˣ) :
    (graph ν f g).edgeFinset.card =
      Fintype.card F^2*(Fintype.card F-1)*
        ∑ x : X, (univ.filter (fun y : Y => ν x y ≠ 0)).card := by
  have hb (i : Index (F := F) (X := X)) (u : Fˣ) :
      block ν f g (neighbors ν f g) i u = univ := by
    ext y
    simp only [block,mem_filter,mem_univ,true_and,iff_true]
    exact block_incidence ν f g i u y
  rw [graph,edge_partition ν f g (neighbors ν f g) (fun _ => Subset.rfl)]
  simp_rw [hb,card_univ,Fintype.card_coe,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
  simp_rw [Index,Fintype.sum_prod_type,←mul_sum,fiber_sum]
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_units]
  simp_rw [←mul_sum]
  ring

/-- A fixed retained fraction of q⁷ edges forces a bounded field order. -/
theorem size_budget (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (H : SimpleGraph (Row (F := F) (X := X) ⊕ Col (F := F) (Y := Y)))
    (hH : H ≤ graph ν f g) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F^2)
    (hY : Fintype.card Y ≤ Fintype.card F^2)
    (K : ℕ) (he : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 10752*K^4 := by
  have hb := graph_fourth ν f g H hH hf hX hY
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(10752*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(10752*Fintype.card F^27) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

omit [Fintype X] in
/-- The full graph already fails if one point row has enough nonzero values. -/
theorem not_free (ν : X → Y → F) (f : X → F) (g : Y → Fˣ)
    (hq : 5 ≤ Fintype.card F) (x : X)
    (hx : 3*(Fintype.card F-1) < (univ.filter (fun y : Y => ν x y ≠ 0)).card) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ν f g) := by
  have hex : ∃ D : Fˣ, 4 ≤ (fiber ν g x D).card := by
    by_contra hn
    push_neg at hn
    have hs : (∑ D : Fˣ, (fiber ν g x D).card) ≤ ∑ _D : Fˣ, 3 :=
      sum_le_sum (fun D _ => by have := hn D; omega)
    rw [fiber_sum] at hs
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_units] at hs
    omega
  obtain ⟨D,hD⟩ := hex
  obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 4) ≤ Fintype.card Fˣ by simp [Fintype.card_units]; omega)
  obtain ⟨b⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 4) ≤ Fintype.card (fiber ν g x D) by simpa using hD)
  intro hf
  exact (free_iff_no_rectangle (neighbors ν f g) (by decide : 0<4)).mp hf
    (a.trans (rows f (x,0,0,D))) (b.trans (columns ν g (x,0,0,D)))
    (fun i j => block_incidence ν f g (x,0,0,D) (a i) (b j))

section Norm
variable {E : Type*} [Field E] [Fintype E] [Algebra F E] [FiniteDimensional F E]

omit [Fintype F] in
omit [Fintype F] in
lemma norm_nonzero_count (x : E) :
    (univ.filter (fun y : E => Algebra.norm F (x+y) ≠ 0)).card = Fintype.card E-1 := by
  have hh (y : E) : Algebra.norm F (x+y) ≠ 0 ↔ y ≠ -x := by
    rw [Algebra.norm_ne_zero_iff]
    apply not_congr
    constructor
    · intro h; linear_combination h
    · intro h; rw [h]; ring
  simp_rw [hh,filter_ne']
  simp

/-- Both vertex parts have q⁴ elements, and the host has order q⁷ edges. -/
theorem norm_host_size (hE : Fintype.card E=Fintype.card F^2)
    (f : E → F) (g : E → Fˣ) :
    Fintype.card ((E × F × F) ⊕ (E × F × F)) = 2*Fintype.card F^4 ∧
    (graph (fun x y : E => Algebra.norm F (x+y)) f g).edgeFinset.card =
      Fintype.card F^4*(Fintype.card F-1)*(Fintype.card F^2-1) := by
  constructor
  · simp only [Fintype.card_sum,Fintype.card_prod,hE]; ring
  · rw [edge_count]
    simp_rw [norm_nonzero_count]
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,hE]
    ring

omit [FiniteDimensional F E] in
/-- All functions f and nowhere-zero g are covered, without fiber hypotheses. -/
theorem norm_thinning (hE : Fintype.card E=Fintype.card F^2)
    (f : E → F) (g : E → Fˣ)
    (H : SimpleGraph ((E × F × F) ⊕ (E × F × F)))
    (hH : H ≤ graph (fun x y : E => Algebra.norm F (x+y)) f g)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 10752*Fintype.card F^27 :=
  graph_fourth _ f g H hH hf hE.le hE.le

theorem norm_not_free (hE : Fintype.card E=Fintype.card F^2)
    (hq : 5 ≤ Fintype.card F) (f : E → F) (g : E → Fˣ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun x y : E => Algebra.norm F (x+y)) f g) := by
  apply not_free _ f g hq (0 : E)
  rw [norm_nonzero_count,hE]
  have h1 : 3*(Fintype.card F-1) ≤ 3*Fintype.card F := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : 3*Fintype.card F < Fintype.card F^2-1 := by
    have hp : 1 ≤ Fintype.card F^2 := by nlinarith
    have hs := Nat.sub_add_cancel hp
    nlinarith
  exact h1.trans_lt h2
end Norm

#print axioms block_incidence
#print axioms block_free
#print axioms edge_partition
#print axioms fiber_sum
#print axioms weight_sum
#print axioms set_system_fourth
#print axioms graph_fourth
#print axioms edge_count
#print axioms size_budget
#print axioms not_free
#print axioms norm_nonzero_count
#print axioms norm_host_size
#print axioms norm_thinning
#print axioms norm_not_free
end Erdos714CrossedScalar
