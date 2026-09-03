import Submission.TwoInputFiberThinning
import Submission.TranslatedNormCounts

/-!
Arbitrary two-input shifts of tagged weighted quadratic norm graphs. The
actual host has the fourth-case critical scale, but every K44-free edge
restriction loses a power. This does not cover arbitrary two-sided
permutations of the entire local norm-graph vertex set.
-/

noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714WeightedTagShift
variable {F E U V : Type*} [Field F] [Field E] [Algebra F E]
  [Fintype F] [Fintype E] [Fintype U] [Fintype V]

abbrev Tag (F U : Type*) [Field F] := Fˣ × U
abbrev Point (F E U : Type*) [Field F] := Tag F U × E

def neighbors (shift : Tag F U → Tag F V → E) (x : Point F E U) :
    Finset (Point F E V) := univ.filter (fun y =>
      Algebra.norm F (x.2+y.2+shift x.1 y.1) = (x.1.1 : F)*(y.1.1 : F))

def graph (shift : Tag F U → Tag F V → E) :
    SimpleGraph (Point F E U ⊕ Point F E V) := Erdos714Packing.incidence (neighbors shift)

omit [Fintype U] in
@[simp] lemma cross_adj (shift : Tag F U → Tag F V → E)
    (x : Point F E U) (y : Point F E V) :
    (graph shift).Adj (.inl x) (.inr y) ↔
      Algebra.norm F (x.2+y.2+shift x.1 y.1)=(x.1.1 : F)*(y.1.1 : F) := by
  simp [graph,neighbors]

omit [Fintype U] [Fintype E] in
/-- A nonzero row weight recovers the column weight from the level. -/
lemma level_fiber_bound (a : Tag F U) (r : F) :
    (univ.filter (fun b : Tag F V => (a.1 : F)*(b.1 : F)=r)).card ≤ Fintype.card V := by
  apply le_trans (card_le_card_of_injOn (s := univ.filter
    (fun b : Tag F V => (a.1 : F)*(b.1 : F)=r))
    (t := (univ : Finset V)) (fun b => b.2) (fun _ _ => mem_univ _) ?_) (by simp)
  intro b hb c hc hbc
  apply Prod.ext _ hbc
  apply Units.ext
  exact mul_left_cancel₀ a.1.ne_zero ((mem_filter.mp hb).2.trans (mem_filter.mp hc).2.symm)

/-- Exact change of variables in one original neighborhood. -/
def neighborEquiv (shift : Tag F U → Tag F V → E) (x : Point F E U) :
    {y : Point F E V // Algebra.norm F (x.2+y.2+shift x.1 y.1) =
      (x.1.1 : F)*(y.1.1 : F)} ≃
    (Σ b : Tag F V, {z : E // Algebra.norm F z=(x.1.1 : F)*(b.1 : F)}) where
  toFun y := ⟨y.val.1,⟨x.2+y.val.2+shift x.1 y.val.1,y.property⟩⟩
  invFun p := ⟨(p.1,p.2.val-x.2-shift x.1 p.1),by
    change Algebra.norm F (x.2+(p.2.val-x.2-shift x.1 p.1)+shift x.1 p.1)=_
    rw [show x.2+(p.2.val-x.2-shift x.1 p.1)+shift x.1 p.1=p.2.val by abel]
    exact p.2.property⟩
  left_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change (x.2+y.val.2+shift x.1 y.val.1)-x.2-shift x.1 y.val.1=y.val.2
    abel
  right_inv p := by
    apply Sigma.subtype_ext
    · rfl
    change x.2+(p.2.val-x.2-shift x.1 p.1)+shift x.1 p.1=p.2.val
    abel

omit [Fintype U] in
/-- Every original row has the same degree, independently of the shift table. -/
lemma neighbors_card (hE : Fintype.card E=Fintype.card F^2)
    (shift : Tag F U → Tag F V → E) (x : Point F E U) :
    (neighbors shift x).card =
      (Fintype.card F-1)*Fintype.card V*(Fintype.card F+1) := by
  have h := Fintype.card_congr (neighborEquiv shift x)
  simp only [Fintype.card_sigma] at h
  simp_rw [Erdos714TranslatedNorm.norm_fiber_card hE
    (mul_ne_zero x.1.1.ne_zero (Units.ne_zero _))] at h
  simpa only [neighbors,Fintype.card_subtype,sum_const,card_univ,nsmul_eq_mul,
    Fintype.card_prod,Fintype.card_units,Tag] using h

/-- Actual undirected edge count, not a heuristic parameter calculation. -/
theorem edge_count (hE : Fintype.card E=Fintype.card F^2)
    (shift : Tag F U → Tag F V → E) :
    (graph shift).edgeFinset.card =
      Fintype.card F^2*Fintype.card U*Fintype.card V*
        (Fintype.card F-1)^2*(Fintype.card F+1) := by
  rw [graph,Erdos714Packing.incidence_edges]
  simp_rw [neighbors_card hE]
  simp only [sum_const,card_univ,nsmul_eq_mul,Point,Tag,Fintype.card_prod,
    Fintype.card_units,hE,Nat.cast_id]
  ring

/-- Apply the two-input fiber cover to the ACTUAL field norm and shifted
weighted graph. Both scalar labels and both tags may affect the shift. -/
theorem fourth_power (hE : Fintype.card E=Fintype.card F^2)
    (shift : Tag F U → Tag F V → E)
    (hU : Fintype.card U ≤ Fintype.card F) (hV : Fintype.card V ≤ Fintype.card F)
    (H : SimpleGraph (Point F E U ⊕ Point F E V)) (hH : H ≤ graph shift)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 1327104*Fintype.card F^27 := by
  let f (a : Tag F U) (b : Tag F V) := -shift a b
  let g (a : Tag F U) (b : Tag F V) := (a.1 : F)*(b.1 : F)
  have hh : H ≤ Erdos714TwoInputFibers.graph (Algebra.norm F) f g := by
    intro a b hab
    have h := hH hab
    cases a with
    | inl x =>
      cases b with
      | inl y => exact False.elim h
      | inr y =>
        change Algebra.norm F (x.2+y.2-f x.1 y.1)=g x.1 y.1
        simpa only [f,g,sub_neg_eq_add] using (cross_adj shift x y).mp h
    | inr y =>
      cases b with
      | inr x => exact False.elim h
      | inl x =>
        change Algebra.norm F (x.2+y.2-f x.1 y.1)=g x.1 y.1
        simpa only [f,g,sub_neg_eq_add] using (cross_adj shift x y).mp h.symm
  have h := Erdos714TwoInputFibers.fourth_power (Algebra.norm F) f g
    (Fintype.card F+1) (Erdos714TranslatedNorm.norm_fiber_bound hE)
    (fun a r => (level_fiber_bound a r).trans (by omega)) H hh hf
  have ha : Fintype.card (Tag F U) ≤ Fintype.card F^2 := by
    simp only [Tag,Fintype.card_prod,Fintype.card_units]
    calc
      _ ≤ Fintype.card F*Fintype.card F := by gcongr; omega
      _ = _ := by ring
  have hq : 0 < Fintype.card F := Fintype.card_pos
  calc
    _ ≤ 10368*(Fintype.card (Tag F U)*Fintype.card E*Fintype.card F)^4*
        (Fintype.card F+1)^7 := h
    _ ≤ 10368*(Fintype.card F^2*Fintype.card F^2*Fintype.card F)^4*
        (2*Fintype.card F)^7 := by gcongr <;> omega
    _ = _ := by ring

/-- At field-sized tag sets, the host has precisely the required starting scale. -/
theorem host_size (hE : Fintype.card E=Fintype.card F^2)
    (shift : Tag F F → Tag F F → E) :
    Fintype.card (Point F E F ⊕ Point F E F)=2*Fintype.card F^3*(Fintype.card F-1) ∧
    (graph shift).edgeFinset.card=Fintype.card F^4*(Fintype.card F-1)^2*(Fintype.card F+1) := by
  constructor
  · simp only [Point,Tag,Fintype.card_sum,Fintype.card_prod,Fintype.card_units,hE]
    ring
  · rw [edge_count hE]
    ring

/-- The critical lower edge budget cannot persist along unbounded field orders. -/
theorem size_budget (hE : Fintype.card E=Fintype.card F^2)
    (shift : Tag F U → Tag F V → E)
    (hU : Fintype.card U ≤ Fintype.card F) (hV : Fintype.card V ≤ Fintype.card F)
    (H : SimpleGraph (Point F E U ⊕ Point F E V)) (hH : H ≤ graph shift)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 1327104*K^4 := by
  have he := fourth_power hE shift hU hV H hH hf
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(1327104*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := by ring
      _ ≤ K^4*(1327104*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms cross_adj
#print axioms level_fiber_bound
#print axioms neighborEquiv
#print axioms neighbors_card
#print axioms edge_count
#print axioms fourth_power
#print axioms host_size
#print axioms size_budget
end Erdos714WeightedTagShift
