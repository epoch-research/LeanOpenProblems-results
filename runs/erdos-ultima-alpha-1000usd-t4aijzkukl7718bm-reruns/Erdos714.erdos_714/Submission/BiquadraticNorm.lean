import Submission.NormPolynomialLevels
import Submission.TranslatedNormCounts

/-!
The explicit biquadratic norm-difference host has the critical number of edges
in odd characteristic, but every K44-free edge thinning loses density.
No identification with a semifield or classification theorem is assumed.
-/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714Biquadratic
section Parameters
variable {F : Type*} [Field F]

def den (D u : F) := 1-D*u^2
def t (D u : F) := (1+D*u^2)/den D u
def s (D u : F) := 2*u/den D u

def Good (D u : F) : Prop := u ≠ 0 ∧ 1+D*u^2 ≠ 0

lemma den_ne_zero (D : F) (hD : ¬ IsSquare D) (u : F) : den D u ≠ 0 := by
  intro hd
  have hu : u ≠ 0 := by
    intro hu
    simp [den,hu] at hd
  apply hD
  refine ⟨u⁻¹,?_⟩
  have he : D*u^2=1 := by dsimp [den] at hd; linear_combination -hd
  field_simp
  linear_combination he

lemma conic (D u : F) (hd : den D u ≠ 0) : t D u^2-D*s D u^2=1 := by
  dsimp [t,s]
  field_simp
  dsimp [den]
  ring

lemma t_ne_zero (D u : F) (hd : den D u ≠ 0) (hu : Good D u) : t D u ≠ 0 :=
  div_ne_zero hu.2 hd

lemma s_ne_zero (D u : F) (h₂ : (2 : F) ≠ 0) (hd : den D u ≠ 0)
    (hu : Good D u) : s D u ≠ 0 := div_ne_zero (mul_ne_zero h₂ hu.1) hd

lemma t_add_one (D u : F) (hd : den D u ≠ 0) : t D u+1=2/den D u := by
  dsimp [t]
  field_simp
  dsimp [den]
  ring

lemma recover (D u : F) (h₂ : (2 : F) ≠ 0) (hd : den D u ≠ 0) :
    s D u/(t D u+1)=u := by
  rw [t_add_one D u hd]
  dsimp [s]
  field_simp

lemma parameters_injective (D : F) (hD : ¬ IsSquare D) (h₂ : (2 : F) ≠ 0) :
    Function.Injective (fun u => (t D u,s D u)) := by
  intro u v huv
  have ht := congrArg Prod.fst huv
  have hs := congrArg Prod.snd huv
  dsimp at ht hs
  rw [← recover D u h₂ (den_ne_zero D hD u),ht,hs,
    recover D v h₂ (den_ne_zero D hD v)]

variable [Fintype F]

/-- At most three rational parameters are lost to either coordinate being zero. -/
lemma good_card (D : F) : Fintype.card F-3 ≤ Fintype.card {u : F // Good D u} := by
  let P : F[X] := X+C D*X^3
  have hp : P ≠ 0 := by
    intro h
    have h1 := congrArg (fun p : F[X] => p.coeff 1) h
    simp [P] at h1
  have hdeg : P.natDegree ≤ 3 := by dsimp [P]; compute_degree!
  have hbad : (univ.filter (fun u : F => ¬ Good D u)).card ≤ 3 := by
    have hh := (Erdos714NormLevels.polynomial_roots_bound hp).trans hdeg
    convert hh using 1
    congr 1
    ext u
    simp only [mem_filter,mem_univ,true_and,P,eval_add,eval_X,eval_mul,eval_C,eval_pow]
    have he : u+D*u^3=u*(1+D*u^2) := by ring
    rw [he,mul_eq_zero]
    simp only [Good]
    tauto
  have hc := card_filter_add_card_filter_not (s := (univ : Finset F)) (Good D)
  rw [card_univ] at hc
  have he : Fintype.card {u : F // Good D u}=(univ.filter (Good D)).card := by
    rw [Fintype.card_subtype]
  rw [he]
  omega

lemma exists_good (D : F) (hq : 3 < Fintype.card F) : ∃ u : F, Good D u := by
  have hc : 0 < Fintype.card {u : F // Good D u} := lt_of_lt_of_le (by omega) (good_card D)
  obtain ⟨u⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨u.val,u.property⟩

end Parameters

section Graph
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

abbrev Point (E : Type*) := E × E

def rel (D : F) (x y : Point E) : Prop :=
  Algebra.norm F (x.1+y.1)^2-D*Algebra.norm F (x.2+y.2)^2=1

def neighbors (D : F) (x : Point E) : Finset (Point E) := univ.filter (rel D x)

def graph (D : F) : SimpleGraph (Point E ⊕ Point E) :=
  Erdos714Packing.incidence (neighbors (E := E) D)

/-- This applies even without the nonsquare or odd-characteristic assumptions. -/
theorem thinning (hE : Fintype.card E=Fintype.card F^2) (D : F)
    (H : SimpleGraph (Point E ⊕ Point E)) (hH : H ≤ graph D)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 339738624*Fintype.card F^27 := by
  have hb := Erdos714NormLevels.power_level_bound hE (fun _ => 0)
    (fun z : E => 1+D*Algebra.norm F z^2) 2 (by decide) H (by
      intro u v huv
      have h := hH huv
      cases u <;> cases v <;>
        simp only [graph,Erdos714Packing.incidence,neighbors,mem_filter,mem_univ,true_and,
          Erdos714Tensor.incidence,sub_zero,rel] at h ⊢ <;> first | exact h | linear_combination h)
    hfree
  norm_num at hb ⊢
  exact hb

/-- A four-by-four copy from one nonzero point of the base conic. -/
def gridCopy (hE : Fintype.card E=Fintype.card F^2) (D a b : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a^2-D*b^2=1) (hq : 3 ≤ Fintype.card F) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph (E := E) D) := by
  let A := {x : E // Algebra.norm F x=a}
  let B := {y : E // Algebra.norm F y=b}
  have hA : 4 ≤ Fintype.card A := by
    rw [show Fintype.card A=Fintype.card F+1 from
      Erdos714TranslatedNorm.norm_fiber_card hE ha]
    omega
  have hB : 4 ≤ Fintype.card B := by
    rw [show Fintype.card B=Fintype.card F+1 from
      Erdos714TranslatedNorm.norm_fiber_card hE hb]
    omega
  let i : Fin 4 ↪ A := (Fin.castLEEmb hA).trans (Fintype.equivFin A).symm.toEmbedding
  let j : Fin 4 ↪ B := (Fin.castLEEmb hB).trans (Fintype.equivFin B).symm.toEmbedding
  let l : Fin 4 ↪ Point E := ⟨fun k => ((i k).val,0),by
    intro k m he
    exact i.injective (Subtype.ext (congrArg Prod.fst he))⟩
  let r : Fin 4 ↪ Point E := ⟨fun k => (0,(j k).val),by
    intro k m he
    exact j.injective (Subtype.ext (congrArg Prod.snd he))⟩
  have hr (k m : Fin 4) : rel D (l k) (r m) := by
    change Algebra.norm F ((i k).val+0)^2-D*Algebra.norm F (0+(j m).val)^2=1
    simpa only [add_zero,zero_add,(i k).property,(j m).property] using hab
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro u v huv
  cases u with
  | inl k =>
    cases v with
    | inl m => simp at huv
    | inr m => exact mem_filter.mpr ⟨mem_univ _,hr k m⟩
  | inr m =>
    cases v with
    | inr k => simp at huv
    | inl k => exact mem_filter.mpr ⟨mem_univ _,hr k m⟩

/-- Every nonsquare parameter fails for every odd field order greater than three. -/
theorem not_free (hE : Fintype.card E=Fintype.card F^2) (D : F)
    (hD : ¬ IsSquare D) (h₂ : (2 : F) ≠ 0) (hq : 3 < Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E) D) := by
  obtain ⟨u,hu⟩ := exists_good D hq
  have hd := den_ne_zero D hD u
  exact fun h => h ⟨gridCopy hE D (t D u) (s D u) (t_ne_zero D u hd hu)
    (s_ne_zero D u h₂ hd hu) (conic D u hd) (by omega)⟩

/-- The connection set is the actual biquadratic level set in the extension. -/
abbrev Connection (D : F) := {z : Point E // Algebra.norm F z.1^2-D*Algebra.norm F z.2^2=1}

/-- The critical edge scale is not lost before imposing freeness. -/
theorem connection_lower (hE : Fintype.card E=Fintype.card F^2)
    (D : F) (hD : ¬ IsSquare D) (h₂ : (2 : F) ≠ 0) :
    (Fintype.card F-3)*(Fintype.card F+1)^2 ≤ Fintype.card (Connection (E := E) D) := by
  let I := Σ u : {u : F // Good D u},
    {x : E // Algebra.norm F x=t D u.val} × {y : E // Algebra.norm F y=s D u.val}
  let f : I → Connection (E := E) D := fun z =>
    ⟨(z.2.1.val,z.2.2.val),by
      rw [z.2.1.property,z.2.2.property]
      exact conic D z.1.val (den_ne_zero D hD z.1.val)⟩
  have hf : Function.Injective f := by
    intro x y he
    have hx : x.2.1.val=y.2.1.val := congrArg (fun p => p.val.1) he
    have hy : x.2.2.val=y.2.2.val := congrArg (fun p => p.val.2) he
    have ht : t D x.1.val=t D y.1.val := by rw [← x.2.1.property,← y.2.1.property,hx]
    have hs : s D x.1.val=s D y.1.val := by rw [← x.2.2.property,← y.2.2.property,hy]
    have hu : x.1=y.1 := Subtype.ext (parameters_injective D hD h₂ (Prod.ext ht hs))
    rcases x with ⟨u,a,b⟩
    rcases y with ⟨v,c,d⟩
    dsimp at hu hx hy
    subst v
    congr 1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hc : Fintype.card I=Fintype.card {u : F // Good D u}*(Fintype.card F+1)^2 := by
    rw [Fintype.card_sigma]
    have ht (u : {u : F // Good D u}) :
        Fintype.card {x : E // Algebra.norm F x=t D u.val}=Fintype.card F+1 :=
      Erdos714TranslatedNorm.norm_fiber_card hE
        (t_ne_zero D u.val (den_ne_zero D hD u.val) u.property)
    have hs (u : {u : F // Good D u}) :
        Fintype.card {y : E // Algebra.norm F y=s D u.val}=Fintype.card F+1 :=
      Erdos714TranslatedNorm.norm_fiber_card hE
        (s_ne_zero D u.val h₂ (den_ne_zero D hD u.val) u.property)
    simp only [Fintype.card_prod,ht,hs,sum_const,card_univ,nsmul_eq_mul,pow_two,Nat.cast_id]
  calc
    _ ≤ Fintype.card {u : F // Good D u}*(Fintype.card F+1)^2 :=
      Nat.mul_le_mul_right _ (good_card D)
    _ = Fintype.card I := hc.symm
    _ ≤ _ := Fintype.card_le_of_injective f hf

/-- Translation gives a full neighborhood bijection, including all vertices. -/
def neighborEquiv (D : F) (x : Point E) : {y : Point E // rel D x y} ≃ Connection (E := E) D where
  toFun y := ⟨(x.1+y.val.1,x.2+y.val.2),y.property⟩
  invFun z := ⟨(z.val.1-x.1,z.val.2-x.2),by simpa [rel,add_comm] using z.property⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

omit [Fintype F] in
lemma edge_count (D : F) :
    (graph (E := E) D).edgeFinset.card=Fintype.card E^2*Fintype.card (Connection (E := E) D) := by
  rw [graph,Erdos714Packing.incidence_edges]
  have hc (x : Point E) : (neighbors D x).card=Fintype.card (Connection (E := E) D) := by
    simpa only [Fintype.card_subtype,neighbors] using Fintype.card_congr (neighborEquiv D x)
  simp only [hc,sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,pow_two,Nat.cast_id]

omit [Field F] [Field E] [Algebra F E] in
lemma vertex_count (hE : Fintype.card E=Fintype.card F^2) :
    Fintype.card (Point E ⊕ Point E)=2*Fintype.card F^4 := by
  simp only [Fintype.card_sum,Fintype.card_prod,hE]
  ring

/-- An explicit lower bound of order q^7 for the full host, for all nonsquare D. -/
theorem host_edges_lower (hE : Fintype.card E=Fintype.card F^2)
    (D : F) (hD : ¬ IsSquare D) (h₂ : (2 : F) ≠ 0) :
    Fintype.card F^4*((Fintype.card F-3)*(Fintype.card F+1)^2) ≤
      (graph (E := E) D).edgeFinset.card := by
  rw [edge_count,hE,← pow_mul]
  exact Nat.mul_le_mul_left _ (connection_lower hE D hD h₂)

/-- From q >= 6 onward the full graph already has at least q^7/2 edges. -/
theorem critical_host_size (hE : Fintype.card E=Fintype.card F^2)
    (D : F) (hD : ¬ IsSquare D) (h₂ : (2 : F) ≠ 0) (hq : 6 ≤ Fintype.card F) :
    Fintype.card F^7 ≤ 2*(graph (E := E) D).edgeFinset.card := by
  let q := Fintype.card F
  have he := host_edges_lower hE D hD h₂
  have hq₁ : q ≤ 2*(q-3) := by dsimp [q]; omega
  have hq₂ : q^2 ≤ (q+1)^2 := Nat.pow_le_pow_left (by omega) 2
  calc
    _ = q^4*(q*q^2) := by dsimp [q]; ring
    _ ≤ q^4*(2*(q-3)*(q+1)^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hq₁ hq₂)
    _ = 2*(q^4*((q-3)*(q+1)^2)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 2 he

/-- The fourth power of the retained edge fraction is at most an absolute
constant divided by q. This is a bound on every free edge thinning. -/
theorem relative_thinning (hE : Fintype.card E=Fintype.card F^2)
    (D : F) (hD : ¬ IsSquare D) (h₂ : (2 : F) ≠ 0) (hq : 6 ≤ Fintype.card F)
    (H : SimpleGraph (Point E ⊕ Point E)) (hH : H ≤ graph D)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card F*H.edgeFinset.card^4 ≤ 5435817984*(graph (E := E) D).edgeFinset.card^4 := by
  have he := thinning hE D H hH hfree
  have hd := critical_host_size hE D hD h₂ hq
  calc
    _ ≤ Fintype.card F*(339738624*Fintype.card F^27) := Nat.mul_le_mul_left _ he
    _ = 339738624*(Fintype.card F^7)^4 := by ring
    _ ≤ 339738624*(2*(graph (E := E) D).edgeFinset.card)^4 := by gcongr
    _ = _ := by ring

/-- The selected graph can have critical size only at bounded q, irrespective
of the parameter D or which edges and vertices were deleted. -/
theorem size_budget (hE : Fintype.card E=Fintype.card F^2) (D : F) (K : ℕ)
    (H : SimpleGraph (Point E ⊕ Point E)) (hH : H ≤ graph D)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) : Fintype.card F ≤ 339738624*K^4 := by
  have he := thinning hE D H hH hfree
  have hh : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(339738624*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(339738624*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos Fintype.card_pos 27)

end Graph
end Erdos714Biquadratic
#print axioms Erdos714Biquadratic.den_ne_zero
#print axioms Erdos714Biquadratic.conic
#print axioms Erdos714Biquadratic.good_card
#print axioms Erdos714Biquadratic.thinning
#print axioms Erdos714Biquadratic.gridCopy
#print axioms Erdos714Biquadratic.not_free
#print axioms Erdos714Biquadratic.connection_lower
#print axioms Erdos714Biquadratic.edge_count
#print axioms Erdos714Biquadratic.host_edges_lower
#print axioms Erdos714Biquadratic.size_budget

#print axioms Erdos714Biquadratic.critical_host_size
#print axioms Erdos714Biquadratic.relative_thinning
