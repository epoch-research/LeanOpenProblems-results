import Submission.UnbalancedBounds
import Submission.TranslatedNormFibers

/-!
Additive tag perturbations of a scalar-weighted norm graph have a complete-block
edge partition. Arbitrary edge thinnings cannot retain the fourth-case critical
density. The tag kernel need not have bounded degree, rank, or any regularity.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714TaggedScalar
open Erdos714Packing

variable {F X Y U V : Type*} [Field F] [Fintype F]
  [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

abbrev Row := X × F × U
abbrev Col := Y × Fˣ × V
abbrev Index := X × (Fˣ × V) × F

def neighbors (ν : X → Y → F) (ψ : U → V → F) (p : Row (F := F) (X := X) (U := U)) :
    Finset (Col (F := F) (Y := Y) (V := V)) :=
  univ.filter (fun c => ν p.1 c.1 = p.2.1*c.2.1.val+ψ p.2.2 c.2.2)

def graph (ν : X → Y → F) (ψ : U → V → F) :
    SimpleGraph (Row (F := F) (X := X) (U := U) ⊕ Col (F := F) (Y := Y) (V := V)) :=
  incidence (neighbors ν ψ)

def fiber (ν : X → Y → F) (x : X) (c : F) : Finset Y :=
  univ.filter (fun y => ν x y = c)

def rows (ψ : U → V → F) (i : Index (F := F) (X := X) (V := V)) :
    U ↪ Row (F := F) (X := X) (U := U) :=
  ⟨fun t => (i.1,(i.2.1.1.val)⁻¹*(i.2.2-ψ t i.2.1.2),t),
    fun _ _ h => congrArg (fun p => p.2.2) h⟩

def columns (ν : X → Y → F) (i : Index (F := F) (X := X) (V := V)) :
    fiber ν i.1 i.2.2 ↪ Col (F := F) (Y := Y) (V := V) :=
  ⟨fun y => (y.val,i.2.1.1,i.2.1.2), fun _ _ h => Subtype.ext (congrArg Prod.fst h)⟩

omit [Fintype X] [Fintype U] in
/-- Each index specifies a full bipartite block. -/
lemma block_incidence (ν : X → Y → F) (ψ : U → V → F)
    (i : Index (F := F) (X := X) (V := V)) (t : U) (y : fiber ν i.1 i.2.2) :
    columns ν i y ∈ neighbors ν ψ (rows ψ i t) := by
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  change ν i.1 y.val = ((i.2.1.1.val)⁻¹*(i.2.2-ψ t i.2.1.2))*i.2.1.1.val+ψ t i.2.1.2
  rw [(mem_filter.mp y.property).2]
  field_simp
  ring

def block (ν : X → Y → F) (ψ : U → V → F)
    (R : Row (F := F) (X := X) (U := U) → Finset (Col (F := F) (Y := Y) (V := V)))
    (i : Index (F := F) (X := X) (V := V)) (t : U) : Finset (fiber ν i.1 i.2.2) :=
  univ.filter (fun y => columns ν i y ∈ R (rows ψ i t))

omit [Fintype F] [Fintype X] [Fintype U] [Fintype V] in
lemma block_free (ν : X → Y → F) (ψ : U → V → F)
    (R : Row (F := F) (X := X) (U := U) → Finset (Col (F := F) (Y := Y) (V := V)))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R))
    (i : Index (F := F) (X := X) (V := V)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (block ν ψ R i)) := by
  rw [free_iff_no_rectangle _ (by decide)] at hf ⊢
  intro f g h
  exact hf (f.trans (rows ψ i)) (g.trans (columns ν i)) (fun j k => (mem_filter.mp (h j k)).2)

/-- A selected edge determines its unique block; all scalar divisions are by units. -/
lemma edge_partition (ν : X → Y → F) (ψ : U → V → F)
    (R : Row (F := F) (X := X) (U := U) → Finset (Col (F := F) (Y := Y) (V := V)))
    (hR : ∀ p, R p ⊆ neighbors ν ψ p) :
    (incidence R).edgeFinset.card =
      ∑ i : Index (F := F) (X := X) (V := V), ∑ t : U, (block ν ψ R i t).card := by
  let f : (Σ i : Index (F := F) (X := X) (V := V), Σ t : U, block ν ψ R i t) →
      (Σ p : Row (F := F) (X := X) (U := U), R p) := fun p =>
    ⟨rows ψ p.1 p.2.1, columns ν p.1 p.2.2.val, (mem_filter.mp p.2.2.property).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨x,⟨b,s⟩,c⟩,t,⟨y,hy⟩⟩ ⟨⟨x',⟨b',s'⟩,c'⟩,t',⟨y',hy'⟩⟩ h
      have hx : x = x' := congrArg (fun p => p.1.1) h
      have ht : t = t' := congrArg (fun p => p.1.2.2) h
      have hb : b = b' := congrArg (fun p => p.2.val.2.1) h
      have hs : s = s' := congrArg (fun p => p.2.val.2.2) h
      have hyy : y.val = y'.val := congrArg (fun p => p.2.val.1) h
      subst x'; subst t'; subst b'; subst s'
      have hc : c = c' := by
        have h1 := (mem_filter.mp y.property).2
        have h2 := (mem_filter.mp y'.property).2
        exact h1.symm.trans ((congrArg (ν x) hyy).trans h2)
      subst c'
      have hy' : y = y' := Subtype.ext hyy
      subst y'
      rfl
    · rintro ⟨⟨x,a,t⟩,⟨⟨y,b,s⟩,he⟩⟩
      have hh : ν x y = a*b.val+ψ t s := (mem_filter.mp (hR (x,a,t) he)).2
      have ha : b.val⁻¹*(ν x y-ψ t s) = a := by
        rw [hh,add_sub_cancel_right,mul_comm a b.val,← mul_assoc,inv_mul_cancel₀ b.ne_zero,one_mul]
      refine ⟨⟨(x,(b,s),ν x y),t,⟨⟨y,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩,?_⟩⟩,?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        simpa only [rows,columns,Function.Embedding.coeFn_mk,ha] using he
      · subst a
        rfl
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [incidence_edges]
  simpa only [Fintype.card_sigma,Fintype.card_coe] using hc.symm

/-- General cardinal bound: |X|*|Fˣ|*|V|*|F| blocks, each at most |U| by d. -/
theorem set_system_fourth (ν : X → Y → F) (ψ : U → V → F)
    (R : Row (F := F) (X := X) (U := U) → Finset (Col (F := F) (Y := Y) (V := V)))
    (hR : ∀ p, R p ⊆ neighbors ν ψ p)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R))
    (d : ℕ) (hν : ∀ x c, (fiber ν x c).card ≤ d) :
    (incidence R).edgeFinset.card^4 ≤
      (Fintype.card X*Fintype.card Fˣ*Fintype.card V*Fintype.card F)^4 *
        (24*Fintype.card U^3*d^4+648*Fintype.card U^4) := by
  let I := Index (F := F) (X := X) (V := V)
  have hb (i : I) : (∑ t, (block ν ψ R i t).card)^4 ≤
      24*Fintype.card U^3*d^4+648*Fintype.card U^4 := by
    have h := Erdos714Unbalanced.fourth_power_bound (block ν ψ R i) (block_free ν ψ R hf i)
    simp only [Fintype.card_coe] at h
    exact h.trans (by gcongr; exact hν i.1 i.2.2)
  have hi : Fintype.card I = Fintype.card X*Fintype.card Fˣ*Fintype.card V*Fintype.card F := by
    simp only [I,Index,Fintype.card_prod]
    ring
  rw [edge_partition ν ψ R hR,← hi]
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset I))
    (f := fun i => ∑ t, (block ν ψ R i t).card) (by intros; omega) 3
  calc
    _ ≤ Fintype.card I^3*∑ i : I, (∑ t, (block ν ψ R i t).card)^4 := by simpa using hp
    _ ≤ Fintype.card I^3*∑ _i : I, (24*Fintype.card U^3*d^4+648*Fintype.card U^4) := by
      gcongr with i _
      exact hb i
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]; ring

/-- All actual graph edge thinnings are included. -/
theorem graph_fourth (ν : X → Y → F) (ψ : U → V → F)
    (H : SimpleGraph (Row (F := F) (X := X) (U := U) ⊕ Col (F := F) (Y := Y) (V := V)))
    (hH : H ≤ graph ν ψ) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (d : ℕ) (hν : ∀ x c, (fiber ν x c).card ≤ d) :
    H.edgeFinset.card^4 ≤
      (Fintype.card X*Fintype.card Fˣ*Fintype.card V*Fintype.card F)^4 *
        (24*Fintype.card U^3*d^4+648*Fintype.card U^4) := by
  let R := Erdos714Unbalanced.neighborhoods H
  have hbi : H ≤ completeBipartiteGraph (Row (F := F) (X := X) (U := U))
      (Col (F := F) (Y := Y) (V := V)) := by
    intro a b hab
    have h := hH hab
    cases a <;> cases b <;> simp_all [graph]
  have he : incidence R = H := Erdos714Unbalanced.incidence_neighborhoods H hbi
  have hr : ∀ p, R p ⊆ neighbors ν ψ p := by
    intro p q hq
    exact hH ((mem_filter.mp hq).2 : H.Adj (.inl p) (.inr q))
  have hb := set_system_fourth ν ψ R hr (by rwa [he]) d hν
  rw [he] at hb
  exact hb

/-- At the q^4-vertex, q^7-edge scale, every thinning loses a power of q. -/
theorem critical_fourth (ν : X → Y → F) (ψ : U → V → F)
    (H : SimpleGraph (Row (F := F) (X := X) (U := U) ⊕ Col (F := F) (Y := Y) (V := V)))
    (hH : H ≤ graph ν ψ) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F^2)
    (hU : Fintype.card U ≤ Fintype.card F) (hV : Fintype.card V ≤ Fintype.card F)
    (hν : ∀ x c, (fiber ν x c).card ≤ Fintype.card F+1) :
    H.edgeFinset.card^4 ≤ 1032*Fintype.card F^27 := by
  let q := Fintype.card F
  have hq : 0 < q := Fintype.card_pos
  have hu : Fintype.card Fˣ ≤ q := by rw [Fintype.card_units]; exact Nat.sub_le _ _
  have hp : q^4 ≤ q^7 := Nat.pow_le_pow_right hq (by decide)
  calc
    _ ≤ (Fintype.card X*Fintype.card Fˣ*Fintype.card V*q)^4 *
        (24*Fintype.card U^3*(q+1)^4+648*Fintype.card U^4) :=
      graph_fourth ν ψ H hH hf (q+1) hν
    _ ≤ (q^2*q*q*q)^4*(24*q^3*(2*q)^4+648*q^4) := by gcongr; omega
    _ = 384*q^27+648*q^20*q^4 := by ring
    _ ≤ 1032*q^27 := by
      have h := Nat.mul_le_mul_left (648*q^20) hp
      nlinarith [show q^20*q^7=q^27 by ring]

/-- The full host has the expected critical size; ν and ψ do not affect it. -/
theorem edge_count (ν : X → Y → F) (ψ : U → V → F) :
    (graph ν ψ).edgeFinset.card =
      Fintype.card X*Fintype.card Y*Fintype.card U*Fintype.card V*Fintype.card Fˣ := by
  have hb (i : Index (F := F) (X := X) (V := V)) (t : U) :
      block ν ψ (neighbors ν ψ) i t = univ := by
    ext y
    simp only [block,mem_filter,mem_univ,true_and,iff_true]
    exact block_incidence ν ψ i t y
  have hc (x : X) : (∑ c : F, (fiber ν x c).card) = Fintype.card Y := by
    simpa only [fiber,mem_univ,filter_true,card_univ] using
      sum_card_fiberwise_eq_card_filter (univ : Finset Y) (univ : Finset F) (ν x)
  rw [graph,edge_partition ν ψ (neighbors ν ψ) (fun _ => Subset.rfl)]
  simp_rw [hb,card_univ,Fintype.card_coe,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
  simp_rw [Fintype.sum_prod_type,← mul_sum,hc]
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
  ring

/-- No fixed multiplicative loss attains q^7 edges at unbounded field orders. -/
theorem size_budget (ν : X → Y → F) (ψ : U → V → F)
    (H : SimpleGraph (Row (F := F) (X := X) (U := U) ⊕ Col (F := F) (Y := Y) (V := V)))
    (hH : H ≤ graph ν ψ) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F^2)
    (hU : Fintype.card U ≤ Fintype.card F) (hV : Fintype.card V ≤ Fintype.card F)
    (hν : ∀ x c, (fiber ν x c).card ≤ Fintype.card F+1)
    (K : ℕ) (he : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 1032*K^4 := by
  have hb := critical_fourth ν ψ H hH hf hX hU hV hν
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(1032*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(1032*Fintype.card F^27) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

section Norm
variable {E : Type*} [Field E] [Fintype E] [Algebra F E]

/-- Translation does not change the size of a norm level. -/
lemma norm_fibers (hE : Fintype.card E = Fintype.card F^2) (x : E) (c : F) :
    (fiber (fun u v : E => Algebra.norm F (u+v)) x c).card ≤ Fintype.card F+1 := by
  have hc : (fiber (fun u v : E => Algebra.norm F (u+v)) x c).card =
      (univ.filter (fun y : E => Algebra.norm F y = c)).card := by
    apply card_nbij (fun y : E => x+y)
    · intro y hy
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
    · intro y hy z hz h
      exact add_left_cancel h
    · intro y hy
      refine ⟨y-x,?_,by abel_nf⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      change Algebra.norm F (x+(y-x))=c
      rw [show x+(y-x)=y by abel]
      exact (mem_filter.mp hy).2
  rw [hc]
  exact Erdos714TranslatedNorm.norm_fiber_bound hE c

/-- N(x+y)=ab+ψ(t,s), with completely arbitrary ψ, is included uniformly. -/
theorem norm_thinning (hE : Fintype.card E = Fintype.card F^2) (ψ : F → F → F)
    (H : SimpleGraph ((E × F × F) ⊕ (E × Fˣ × F)))
    (hH : H ≤ graph (fun x y : E => Algebra.norm F (x+y)) ψ)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 1032*Fintype.card F^27 :=
  critical_fourth _ ψ H hH hf hE.le le_rfl le_rfl (norm_fibers hE)

/-- This host really has order 2q^4-q^3 and q^7-q^6 undirected edges. -/
theorem norm_host_size (hE : Fintype.card E = Fintype.card F^2) (ψ : F → F → F) :
    Fintype.card ((E × F × F) ⊕ (E × Fˣ × F)) =
      Fintype.card F^4+Fintype.card F^3*(Fintype.card F-1) ∧
    (graph (fun x y : E => Algebra.norm F (x+y)) ψ).edgeFinset.card =
      Fintype.card F^6*(Fintype.card F-1) := by
  constructor
  · simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_units,hE]
    ring
  · rw [edge_count,Fintype.card_units,hE]
    ring

end Norm

#print axioms block_incidence
#print axioms block_free
#print axioms edge_partition
#print axioms set_system_fourth
#print axioms graph_fourth
#print axioms critical_fourth
#print axioms edge_count
#print axioms size_budget
#print axioms norm_fibers
#print axioms norm_thinning
#print axioms norm_host_size
end Erdos714TaggedScalar
