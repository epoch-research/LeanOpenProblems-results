import Submission.Packing

/-! Exact counting for affine-line replacements. Local C4-freeness does not
imply global K44-freeness, and no such implication is asserted here. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000

namespace Erdos714AffineLineReplacement
variable {E : Type*} [Field E]

/-- The local coordinate is shifted separately on every nonvertical line. -/
def point (C : E → E → E) (m b t : E) : E × E :=
  (t-C m b,m*(t-C m b)+b)

lemma point_injective (C : E → E → E) (m b : E) : Function.Injective (point C m b) := by
  intro s t h
  exact sub_left_injective (congrArg Prod.fst h)

/-- Two distinct points determine the line and both shifted coordinates. -/
lemma pair_unique (C : E → E → E) {m b s t m' b' s' t' : E} (hst : s ≠ t)
    (hs : point C m b s=point C m' b' s')
    (ht : point C m b t=point C m' b' t') :
    m=m' ∧ b=b' ∧ s=s' ∧ t=t' := by
  have hx := congrArg Prod.fst hs
  have hy := congrArg Prod.fst ht
  have hx' := congrArg Prod.snd hs
  have hy' := congrArg Prod.snd ht
  dsimp [point] at hx hy hx' hy'
  rw [← hx] at hx'
  rw [← hy] at hy'
  have he : (m-m')*(s-t)=0 := by linear_combination hx'-hy'
  have hm : m=m' := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hst))
  subst m'
  have hb : b=b' := by linear_combination hx'
  subst b'
  exact ⟨rfl,rfl,sub_left_injective hx,sub_left_injective hy⟩

def Pattern (R : E → E → Prop) := {p : E × E // p.1 ≠ p.2 ∧ R p.1 p.2}
def Index (R : E → E → Prop) := E × E × Pattern R

def pair (C : E → E → E) (R : E → E → Prop) (j : Index R) : (E × E) × (E × E) :=
  (point C j.1 j.2.1 j.2.2.1.1,point C j.1 j.2.1 j.2.2.1.2)

lemma pair_injective (C : E → E → E) (R : E → E → Prop) :
    Function.Injective (pair C R) := by
  rintro ⟨m,b,⟨⟨s,t⟩,hst,hR⟩⟩ ⟨m',b',⟨⟨s',t'⟩,hst',hR'⟩⟩ h
  obtain ⟨hm,hb,hs,ht⟩ := pair_unique C hst (congrArg Prod.fst h) (congrArg Prod.snd h)
  dsimp only at hm hb hs ht
  subst m'; subst b'; subst s'; subst t'; rfl

variable [Fintype E]
instance (R : E → E → Prop) : Fintype (Pattern R) := by unfold Pattern; infer_instance
instance (R : E → E → Prop) : Fintype (Index R) := inferInstanceAs (Fintype (E × E × Pattern R))

def graph (C : E → E → E) (R : E → E → Prop) : SimpleGraph ((E × E) ⊕ (E × E)) :=
  Erdos714Packing.incidence fun x => univ.filter (fun y => (x,y) ∈ Set.range (pair C R))

/-- The entire edge set is parameterized once by a line and a local edge. -/
theorem edge_count (C : E → E → E) (R : E → E → Prop) :
    (graph C R).edgeFinset.card=Fintype.card E^2*Fintype.card (Pattern R) := by
  let e : Index R ≃ Set.range (pair C R) := Equiv.ofInjective (pair C R) (pair_injective C R)
  have hc := Fintype.card_congr e
  simp only [Index,Fintype.card_prod] at hc
  rw [graph,Erdos714Packing.incidence_edges]
  have he : (∑ x : E × E, (univ.filter (fun y => (x,y) ∈ Set.range (pair C R))).card) =
      Fintype.card (Set.range (pair C R)) := by
    simp only [Fintype.card_subtype,card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
  rw [he,← hc]
  ring

/-- Distinct points on one line have no alternative line label. -/
lemma on_line_iff (C : E → E → E) (R : E → E → Prop) (m b s t : E) :
    (graph C R).Adj (.inl (point C m b s)) (.inr (point C m b t)) ↔ s ≠ t ∧ R s t := by
  change point C m b t ∈ univ.filter (fun y => (point C m b s,y) ∈ Set.range (pair C R)) ↔ _
  simp only [mem_filter,mem_univ,true_and,Set.mem_range]
  constructor
  · rintro ⟨⟨m',b',⟨⟨s',t'⟩,hst,hR⟩⟩,h⟩
    obtain ⟨hm,hb,hs,ht⟩ := pair_unique C hst (congrArg Prod.fst h) (congrArg Prod.snd h)
    dsimp only at hm hb hs ht
    subst m'; subst b'; subst s'; subst t'
    exact ⟨hst,hR⟩
  · intro h
    exact ⟨(m,b,⟨(s,t),h⟩),rfl⟩


section Polarity
variable {F : Type*} [Field F] [Fintype F]

def polarity (e : E ≃ F × F) (s t : E) : Prop :=
  (e s).1+(e t).1=(e s).2*(e t).2

omit [Field E] [Fintype E] [Fintype F] in
lemma polarity_rectangle (e : E ≃ F × F) {s u t v : E} (hsu : s ≠ u)
    (hst : polarity e s t) (hsv : polarity e s v)
    (hut : polarity e u t) (huv : polarity e u v) : t=v := by
  have hsecond : (e s).2 ≠ (e u).2 := by
    intro h
    apply hsu
    apply e.injective
    apply Prod.ext _ h
    dsimp [polarity] at hst hut
    rw [h] at hst
    linear_combination hst-hut
  have hprod : ((e s).2-(e u).2)*((e t).2-(e v).2)=0 := by
    dsimp [polarity] at hst hsv hut huv
    linear_combination -hst+hsv+hut-huv
  have htv : (e t).2=(e v).2 := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hsecond))
  apply e.injective
  apply Prod.ext _ htv
  dsimp [polarity] at hst hsv
  rw [htv] at hst
  linear_combination hst-hsv

omit [Field E] [Fintype F] in
/-- The local graph really is C4-free, including its diagonal deletions. -/
theorem local_free (e : E ≃ F × F) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free
      (Erdos714Packing.incidence fun s => univ.filter (fun t => s ≠ t ∧ polarity e s t)) := by
  apply (Erdos714Packing.free_iff_no_rectangle _ (by decide)).mpr
  intro f g h
  have he (i j : Fin 2) : polarity e (f i) (g j) := (mem_filter.mp (h i j)).2.2
  have ht := polarity_rectangle e (f.injective.ne (by decide : (0 : Fin 2) ≠ 1))
    (he 0 0) (he 0 1) (he 1 0) (he 1 1)
  exact (by decide : (0 : Fin 2) ≠ 1) (g.injective ht)

omit [Field E] in
lemma polarity_all_card (e : E ≃ F × F) :
    (univ.filter (fun p : E × E => polarity e p.1 p.2)).card=Fintype.card F^3 := by
  have hc : Fintype.card (F × F × F)=Fintype.card F^3 := by simp only [Fintype.card_prod]; ring
  rw [← hc,← card_univ (α := F × F × F)]
  apply card_bij (fun p _ => ((e p.1).1,(e p.1).2,(e p.2).2))
  · intro p _; exact mem_univ _
  · intro p hp q hq he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun a : F × F × F => a.2.1) he
    have h3 := congrArg (fun a : F × F × F => a.2.2) he
    dsimp only at h1 h2 h3
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    apply Prod.ext
    · exact e.injective (Prod.ext h1 h2)
    · apply e.injective
      apply Prod.ext _ h3
      dsimp [polarity] at hp' hq'
      rw [h1,h2,h3] at hp'
      linear_combination hp'-hq'
  · rintro ⟨a,b,c⟩ _
    refine ⟨(e.symm (a,b),e.symm (b*c-a,c)),?_,?_⟩
    · simp [polarity]
    · simp

omit [Field E] in
lemma polarity_diagonal_card (e : E ≃ F × F) (h2 : (2:F) ≠ 0) :
    (univ.filter (fun p : E × E => polarity e p.1 p.2 ∧ p.1=p.2)).card=Fintype.card F := by
  rw [← card_univ (α := F)]
  apply card_bij (fun p _ => (e p.1).2)
  · intro p _; exact mem_univ _
  · intro p hp q hq he
    obtain ⟨hp',hp⟩ := (mem_filter.mp hp).2
    obtain ⟨hq',hq⟩ := (mem_filter.mp hq).2
    have hx : p.1=q.1 := by
      apply e.injective
      apply Prod.ext _ he
      dsimp [polarity] at hp' hq'
      rw [← hp] at hp'
      rw [← hq,← he] at hq'
      apply (mul_left_cancel₀ h2)
      linear_combination hp'-hq'
    exact Prod.ext hx (hp.symm.trans (hx.trans hq))
  · intro t _
    let x := e.symm (t*t/2,t)
    refine ⟨(x,x),?_,?_⟩
    · simp only [mem_filter,mem_univ,true_and,polarity,x,e.apply_symm_apply,and_true]
      field_simp
      ring
    · simp [x]

omit [Field E] in
lemma polarity_pattern_card (e : E ≃ F × F) (h2 : (2:F) ≠ 0) :
    Fintype.card (Pattern (polarity e))=Fintype.card F^3-Fintype.card F := by
  have h := card_filter_add_card_filter_not
    (s := univ.filter (fun p : E × E => polarity e p.1 p.2)) (fun p => p.1=p.2)
  simp only [filter_filter] at h
  rw [polarity_all_card e,polarity_diagonal_card e h2] at h
  have he : Fintype.card (Pattern (polarity e))=
      (univ.filter (fun p : E × E => polarity e p.1 p.2 ∧ p.1 ≠ p.2)).card := by
    simp only [Pattern,Fintype.card_subtype,and_comm]
  rw [he]
  exact Nat.eq_sub_of_add_eq' h

omit [Field E] [Field F] in
lemma polarity_vertex_count (e : E ≃ F × F) :
    Fintype.card ((E × E) ⊕ (E × E))=2*Fintype.card F^4 := by
  have hE : Fintype.card E=Fintype.card F^2 := by
    simpa only [Fintype.card_prod,pow_two] using Fintype.card_congr e
  simp only [Fintype.card_sum,Fintype.card_prod,hE]
  ring

/-- Exact critical-scale edge count for every line-dependent shift. -/
theorem polarity_edge_count (C : E → E → E) (e : E ≃ F × F) (h2 : (2:F) ≠ 0) :
    (graph C (polarity e)).edgeFinset.card=Fintype.card F^7-Fintype.card F^5 := by
  have hE : Fintype.card E=Fintype.card F^2 := by
    simpa only [Fintype.card_prod,pow_two] using Fintype.card_congr e
  rw [edge_count,polarity_pattern_card e h2,hE,Nat.mul_sub_left_distrib]
  congr 1 <;> ring

end Polarity

end Erdos714AffineLineReplacement
#print axioms Erdos714AffineLineReplacement.pair_unique
#print axioms Erdos714AffineLineReplacement.edge_count
#print axioms Erdos714AffineLineReplacement.on_line_iff

#print axioms Erdos714AffineLineReplacement.local_free
#print axioms Erdos714AffineLineReplacement.polarity_pattern_card
#print axioms Erdos714AffineLineReplacement.polarity_edge_count

#print axioms Erdos714AffineLineReplacement.polarity_vertex_count
