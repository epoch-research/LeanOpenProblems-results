import Submission.ScalarProfileTranslation
import Submission.QuarticNormProduct

/-!
Every odd-characteristic quartic trace-zero additive norm graph has a
three-scalar local profile. This bounds arbitrary K44-free edge thinnings,
not only the full graph or selected vertices. It does not settle Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714QuarticAdditive
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
abbrev Point := LinearMap.ker (Algebra.trace F E)
abbrev frob := FiniteField.frobeniusAlgEquivOfAlgebraic F E

def anti : Submodule F E where
  carrier := {v | (frob (F := F) (E := E)^2) v = -v}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq] at *; simp only [map_add,hx,hy,neg_add_rev]; abel
  smul_mem' := by intro a x hx; simp only [Set.mem_setOf_eq] at *; simp [map_smul,hx]

lemma frob_iterate (j : ℕ) (z : E) : (frob (F := F) (E := E)^j) z = z^(Fintype.card F^j) := by
  induction j with
  | zero => simp
  | succ j hj =>
    rw [pow_succ',AlgEquiv.mul_apply,hj]
    simp only [frob,FiniteField.frobeniusAlgEquivOfAlgebraic_apply]
    rw [←pow_mul,pow_succ]

lemma trace_four (hd : Module.finrank F E=4) (z : E) :
    algebraMap F E (Algebra.trace F E z) =
      z+(frob (F := F)) z+(frob (F := F)^2) z+(frob (F := F)^3) z := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow,hd]
  simp only [sum_range_succ,sum_range_zero,Nat.card_eq_fintype_card,pow_zero,pow_one,zero_add]
  rw [frob_iterate 2,frob_iterate 3]
  rfl

lemma norm_four (hd : Module.finrank F E=4) (z : E) :
    algebraMap F E (Algebra.norm F z) =
      z*(frob (F := F)) z*(frob (F := F)^2) z*(frob (F := F)^3) z := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow,hd]
  simp only [prod_range_succ,prod_range_zero,Nat.card_eq_fintype_card,pow_zero,pow_one,one_mul]
  rw [frob_iterate 2,frob_iterate 3]
  rfl

lemma fourth_frob (hd : Module.finrank F E=4) : (frob (F := F) (E := E))^4=1 := by
  have h := pow_orderOf_eq_one (frob (F := F) (E := E))
  rwa [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,hd] at h

lemma fixed_descent (x : E) (hx : frob (F := F) x=x) : ∃ a : F, algebraMap F E a=x := by
  let p : F[X] := X^Fintype.card F-X
  have hp : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hs : p.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    dsimp [p]
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
    exact Finset.card_univ
  have hr : (p.map (algebraMap F E)).IsRoot x := by
    simpa [p,Polynomial.IsRoot,frob,FiniteField.frobeniusAlgEquivOfAlgebraic_apply] using sub_eq_zero.mpr hx
  exact hs.mem_range_of_isRoot hp hr

omit [Fintype F] [Fintype E] in
lemma two_extension (h2 : (2 : F) ≠ 0) : (2 : E) ≠ 0 := by
  intro h
  apply h2
  apply (algebraMap F E).injective
  simpa only [map_ofNat,map_zero] using h

/-- A transverse vector and one skew scalar coordinate parameterize the trace kernel. -/
def coordinates (h2 : (2 : F) ≠ 0) (u : E) (hu : frob (F := F) u = -u)
    (p : anti (F := F) (E := E) × F) : Point (F := F) (E := E) :=
  ⟨p.1.val+algebraMap F E p.2*u, by
    change Algebra.trace F E _=0
    rw [map_add]
    have hv := Erdos714QuarticNormProduct.trace_zero_of_skew h2
      (frob (F := F)^2) p.1.property
    have ht := Erdos714QuarticNormProduct.trace_zero_of_skew h2 (frob (F := F))
      (x := algebraMap F E p.2*u) (by rw [map_mul,AlgEquiv.commutes,hu]; ring)
    rw [hv,ht,add_zero]⟩

lemma coordinate_bijective (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (u : E) (hu0 : u ≠ 0) (hu : frob (F := F) u = -u) :
    Function.Bijective (coordinates h2 u hu) := by
  have h2E := two_extension (E := E) h2
  have hu2 : (frob (F := F)^2) u=u := by
    rw [pow_two,AlgEquiv.mul_apply,hu,map_neg,hu,neg_neg]
  constructor
  · rintro ⟨v,t⟩ ⟨w,s⟩ he
    have he1 : v.val+algebraMap F E t*u=w.val+algebraMap F E s*u := congrArg (fun z : Point (F := F) (E := E) => z.val) he
    have he2 := congrArg (fun z : E => (frob (F := F) (E := E)^2) z) he1
    have hv2 : (frob (F := F)^2) v.val=-v.val := v.property
    have hw2 : (frob (F := F)^2) w.val=-w.val := w.property
    simp only [map_add,map_mul,AlgEquiv.commutes,hv2,hw2,hu2] at he2
    have hv : v=w := by
      apply Subtype.ext
      have hh : (2 : E)*(v.val-w.val)=0 := by linear_combination he1-he2
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left h2E)
    subst w
    have ht : t=s := (algebraMap F E).injective (mul_right_cancel₀ hu0 (add_left_cancel he1))
    subst s
    rfl
  · intro x
    have h4 := fourth_frob (F := F) (E := E) hd
    have ht : x.val+(frob (F := F)) x.val+(frob (F := F)^2) x.val+(frob (F := F)^3) x.val=0 := by
      rw [←trace_four hd,x.property,map_zero]
    let z : E := (x.val+(frob (F := F)^2) x.val)/(2*u)
    have hz : frob (F := F) z=z := by
      have hnext : (frob (F := F)) ((frob (F := F)^2) x.val)=(frob (F := F)^3) x.val := by
        rw [show (3:ℕ)=1+2 by rfl,pow_add,pow_one,AlgEquiv.mul_apply]
      have hn : (frob (F := F)) x.val+(frob (F := F)^3) x.val = -(x.val+(frob (F := F)^2) x.val) := by
        linear_combination ht
      change (frob (F := F)) ((x.val+(frob (F := F)^2) x.val)/(2*u))=
        (x.val+(frob (F := F)^2) x.val)/(2*u)
      rw [map_div₀,map_add,map_mul,map_ofNat,hu,hnext,hn]
      field_simp
    obtain ⟨t,htt⟩ := fixed_descent z hz
    let v : E := (x.val-(frob (F := F)^2) x.val)/2
    have hv : (frob (F := F)^2) v=-v := by
      have hi : (frob (F := F)^2) ((frob (F := F)^2) x.val)=x.val := by
        rw [←AlgEquiv.mul_apply,←pow_add,show (2+2:ℕ)=4 by rfl,h4]
        rfl
      dsimp [v]
      rw [map_div₀,map_sub,map_ofNat,hi]
      ring
    refine ⟨(⟨v,hv⟩,t),?_⟩
    apply Subtype.ext
    change v+algebraMap F E t*u=x.val
    rw [htt]
    dsimp [v,z]
    field_simp
    ring

/-- This is a bijection of actual field elements, not a cardinality-only substitution. -/
def coordinateEquiv (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (u : E) (hu0 : u ≠ 0) (hu : frob (F := F) u=-u) :
    (anti (F := F) (E := E) × F) ≃ Point (F := F) (E := E) :=
  Equiv.ofBijective (coordinates h2 u hu) (coordinate_bijective hd h2 u hu0 hu)

lemma coordinates_add (h2 : (2 : F) ≠ 0) (u : E) (hu : frob (F := F) u=-u)
    (p q : anti (F := F) (E := E) × F) :
    coordinates h2 u hu (p+q)=coordinates h2 u hu p+coordinates h2 u hu q := by
  apply Subtype.ext
  simp only [coordinates,Prod.fst_add,Prod.snd_add,map_add,Submodule.coe_add]
  ring

lemma point_card (hd : Module.finrank F E=4) :
    Fintype.card (Point (F := F) (E := E))=Fintype.card F^3 := by
  have hk := (Algebra.trace F E).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective F E),finrank_top,
    Module.finrank_self,hd] at hk
  have hdim : Module.finrank F (Point (F := F) (E := E))=3 := by
    change 1+Module.finrank F (Point (F := F) (E := E))=4 at hk
    omega
  rw [Module.card_eq_pow_finrank (K := F),hdim]

lemma anti_card (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (u : E) (hu0 : u ≠ 0) (hu : frob (F := F) u=-u) :
    Fintype.card (anti (F := F) (E := E))=Fintype.card F^2 := by
  have h := Fintype.card_congr (coordinateEquiv hd h2 u hu0 hu)
  rw [Fintype.card_prod,point_card hd] at h
  have hh : Fintype.card (anti (F := F) (E := E))*Fintype.card F = Fintype.card F^2*Fintype.card F := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos hh

/-- The odd coefficients vanish along the skew direction. -/
lemma norm_coordinates (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (u : E) (hu : frob (F := F) u=-u) (v : anti (F := F) (E := E)) (t : F) :
    Algebra.norm F (coordinates h2 u hu (v,t)).val =
      Algebra.norm F u*t^4 + (Algebra.norm F (u+v.val)-Algebra.norm F u-Algebra.norm F v.val)*t^2+
        Algebra.norm F v.val := by
  have hu2 : (frob (F := F)^2) u=u := by
    rw [pow_two,AlgEquiv.mul_apply,hu,map_neg,hu,neg_neg]
  have hu3 : (frob (F := F)^3) u=-u := by
    rw [show (3:ℕ)=1+2 by rfl,pow_add,pow_one,AlgEquiv.mul_apply,hu2,hu]
  have hv2 : (frob (F := F)^2) v.val=-v.val := v.property
  have hv3 : (frob (F := F)^3) v.val= -(frob (F := F)) v.val := by
    rw [show (3:ℕ)=1+2 by rfl,pow_add,pow_one,AlgEquiv.mul_apply,v.property,map_neg]
  apply (algebraMap F E).injective
  simp only [map_add,map_mul,map_sub,map_pow,norm_four hd]
  simp only [coordinates,map_add,map_mul,AlgEquiv.commutes,hu,hu2,hu3,hv2,hv3]
  ring

/-- The actual additive-weight graph, on two copies of the full trace kernel. -/
def graph : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)) where
  Adj x y := match x,y with
    | .inl p,.inr q => Algebra.norm F (p.1.val+q.1.val)=p.2+q.2
    | .inr q,.inl p => Algebra.norm F (p.1.val+q.1.val)=p.2+q.2
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

def outer (u : E) (t a : F) : F := Algebra.norm F u*t^4+a*t^2

def transverse (u : E) (v : anti (F := F) (E := E)) : F :=
  Algebra.norm F (u+v.val)-Algebra.norm F u-Algebra.norm F v.val

def constant (v : anti (F := F) (E := E)) : F := Algebra.norm F v.val

def vertexEquiv (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (u : E) (hu0 : u ≠ 0) (hu : frob (F := F) u=-u) :
    ((anti (F := F) (E := E) × F) × F) ≃ (Point (F := F) (E := E) × F) :=
  (coordinateEquiv hd h2 u hu0 hu).prodCongr (Equiv.refl F)

/-- The coordinate graph is isomorphic to the original algebra-norm graph. -/
def hostIso (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (u : E) (hu0 : u ≠ 0) (hu : frob (F := F) u=-u) :
    Erdos714ScalarProfile.graph (outer (F := F) u) (transverse u) constant ≃g
      graph (F := F) (E := E) := by
  let e := vertexEquiv hd h2 u hu0 hu
  have hc (c d : (anti (F := F) (E := E) × F) × F) :
      graph.Adj (.inl (e c)) (.inr (e d)) ↔
        (Erdos714ScalarProfile.graph (outer (F := F) u) (transverse u) constant).Adj (.inl c) (.inr d) := by
    rw [Erdos714ScalarProfile.cross_adj]
    change Algebra.norm F ((coordinates h2 u hu c.1).val+(coordinates h2 u hu d.1).val)=c.2+d.2 ↔ _
    rw [←Submodule.coe_add,←coordinates_add,norm_coordinates hd h2 u hu]
    rfl
  exact {
    toEquiv := e.sumCongr e
    map_rel_iff' := by
      intro a b
      cases a with
      | inl c =>
        cases b with
        | inl d => rfl
        | inr d => exact hc c d
      | inr c =>
        cases b with
        | inl d => exact (hc d c).trans (by rw [adj_comm])
        | inr d => rfl }

/-- The bound includes all edge thinnings, with no symmetry of H assumed. -/
theorem fourth_power (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (H : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)))
    (hH : H ≤ graph (F := F) (E := E))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  obtain ⟨u,v,hu0,hv0,hu,hv⟩ := Erdos714QuarticNormProduct.skew_parameters
    (frob (F := F) (E := E))
    ((FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F E).trans hd)
  let c := hostIso hd h2 u hu0 hu
  let e := c.toEquiv
  let J := H.comap e
  have hJ : J ≤ Erdos714ScalarProfile.graph (outer (F := F) u) (transverse u) constant := by
    intro a b hab
    exact c.map_adj_iff.mp (hH hab)
  have hfJ : (completeBipartiteGraph (Fin 4) (Fin 4)).Free J :=
    Erdos714GraphAveraging.free_comap _ H e.toEmbedding hf
  have hb := Erdos714ScalarProfile.fourth_power (outer (F := F) u) (transverse u) constant
    J hJ hfJ (anti_card hd h2 u hu0 hu).le
  have he : J.edgeFinset.card=H.edgeFinset.card := (SimpleGraph.Iso.comap e H).card_edgeFinset_eq
  rwa [he] at hb

/-- Exact critical-scale counts for the full actual norm graph. -/
theorem host_size (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0) :
    Fintype.card ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)) =
      2*Fintype.card F^4 ∧
    (graph (F := F) (E := E)).edgeFinset.card=Fintype.card F^7 := by
  constructor
  · simp only [Fintype.card_sum,Fintype.card_prod,point_card hd]; ring
  · obtain ⟨u,v,hu0,hv0,hu,hv⟩ := Erdos714QuarticNormProduct.skew_parameters
      (frob (F := F) (E := E))
      ((FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F E).trans hd)
    rw [←(hostIso hd h2 u hu0 hu).card_edgeFinset_eq,Erdos714ScalarProfile.edge_count,
      anti_card hd h2 u hu0 hu]
    ring

/-- The retained fraction is at most a constant times q^(-1/4). -/
theorem relative_bound (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (H : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)))
    (hH : H ≤ graph (F := F) (E := E))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card F*H.edgeFinset.card^4 ≤ 165888*(graph (F := F) (E := E)).edgeFinset.card^4 := by
  have h := Nat.mul_le_mul_left (Fintype.card F) (fourth_power hd h2 H hH hf)
  rw [(host_size hd h2).2]
  convert h using 1; ring

theorem size_budget (hd : Module.finrank F E=4) (h2 : (2 : F) ≠ 0)
    (H : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)))
    (hH : H ≤ graph (F := F) (E := E))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (he : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have hb := fourth_power hd h2 H hH hf
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(165888*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms trace_four
#print axioms norm_four
#print axioms fixed_descent
#print axioms coordinate_bijective
#print axioms coordinateEquiv
#print axioms point_card
#print axioms anti_card
#print axioms norm_coordinates
#print axioms hostIso
#print axioms fourth_power
#print axioms host_size
#print axioms relative_bound
#print axioms size_budget
end Erdos714QuarticAdditive
