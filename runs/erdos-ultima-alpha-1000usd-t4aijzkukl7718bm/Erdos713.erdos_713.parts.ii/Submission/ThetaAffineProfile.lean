import FormalConjecturesUtil
import Submission.ThetaProfileCompletion
import Submission.GlobalLightPairs

/-! Affine separated profiles and their exact incidence counts.
This construction does not settle the main extremal-exponent conjecture. -/
namespace Erdos713ThetaAffine
open Erdos713ThetaProfile Erdos713ThetaGram Erdos713GlobalLight

variable {F V A C : Type*} [Field F]

def profile (p : F × F) (i : F) : F := p.1*i+p.2

lemma separated : Separated (profile (F := F)) := by
  intro p q i j hij hi hj
  dsimp [profile] at hi hj
  have hz : (p.1-q.1)*(i-j)=0 := by linear_combination hi-hj
  have hp : p.1 = q.1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hij))
  apply Prod.ext hp
  rw [hp] at hi
  exact add_left_cancel hi

def through (i j t u : F) : F × F :=
  ((t-u)/(i-j),t-((t-u)/(i-j))*i)

lemma through_left (i j t u : F) : profile (through i j t u) i = t := by
  dsimp [profile,through]
  ring

lemma through_right {i j : F} (hij : i ≠ j) (t u : F) :
    profile (through i j t u) j = u := by
  dsimp [profile,through]
  field_simp [sub_ne_zero.mpr hij]
  ring

/-- The profile prescribes the type coordinate of the column. -/
def lift (S : C → F × V → Prop) (p : F × F) (a : C) (b : F × (F × V)) : Prop :=
  b.2.1 = profile p b.1 ∧ S a (b.1,b.2.2)

lemma lift_transversal {S : C → F × V → Prop} (hS : Transversal S Prod.fst)
    (p : F × F) : Transversal (lift S p) Prod.fst := by
  intro a x y hx hy he
  have hv := congrArg Prod.snd (hS a (x.1,x.2.2) (y.1,y.2.2) hx.2 hy.2 he)
  exact Prod.ext he (Prod.ext (hx.1.trans ((congrArg (profile p) he).trans hy.1.symm)) hv)

lemma lift_no_theta {S : C → F × V → Prop} (hS : ¬ HasTheta S) (p : F × F) :
    ¬ HasTheta (lift S p) := by
  rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
  let g' : Fin 4 → F × V := fun i => ((g i).1,(g i).2.2)
  have ht (i : Fin 4) : (g i).2.1 = profile p (g i).1 := by
    fin_cases i
    · exact h00.1
    · exact h01.1
    · exact h02.1
    · exact h13.1
  have hg' : Function.Injective g' := by
    intro i j he
    apply hgi
    have hi := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    exact Prod.ext hi (Prod.ext ((ht i).trans ((congrArg (profile p) hi).trans (ht j).symm)) hv)
  exact hS ⟨f,g',hfi,hg',h00.2,h10.2,h01.2,h11.2,h02.2,h22.2,h13.2,h23.2⟩

def complete (R : A → F × V → Prop) (S : C → F × V → Prop) :=
  assemble R (lift S)

lemma complete_no_theta {R : A → F × V → Prop} {S : C → F × V → Prop}
    (hR : ¬ HasTheta R) (hS : ¬ HasTheta S)
    (htR : Transversal R Prod.fst) (htS : Transversal S Prod.fst) :
    ¬ HasTheta (complete R S) :=
  no_theta_assemble hR (lift_no_theta hS) htR separated (lift_transversal htS)
    (fun _ _ _ h => h.1)

/-- Common neighbours of columns in different blocks use the unique
profile through the two prescribed types. -/
def crossCommonEquiv (R : A → F × V → Prop) (S : C → F × V → Prop)
    (i j t u : F) (v w : V) (hij : i ≠ j) :
    {a // complete R S a (i,(t,v)) ∧ complete R S a (j,(u,w))} ≃
      {a // S a (i,v) ∧ S a (j,w)} where
  toFun a := match a with
    | ⟨.inl a,ha⟩ => False.elim (hij (ha.1.1.symm.trans ha.2.1))
    | ⟨.inr a,ha⟩ => ⟨a.2,ha.1.2,ha.2.2⟩
  invFun a := ⟨.inr (through i j t u,a.val),
    ⟨(through_left i j t u).symm,a.property.1⟩,
    ⟨(through_right hij t u).symm,a.property.2⟩⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl a => exact False.elim (hij (ha.1.1.symm.trans ha.2.1))
    | inr a =>
      have he : a.1 = through i j t u := separated a.1 (through i j t u) i j hij
        (ha.1.1.symm.trans (through_left i j t u).symm)
        (ha.2.1.symm.trans (through_right hij t u).symm)
      apply Subtype.ext
      exact congrArg Sum.inr (Prod.ext he.symm rfl)
  right_inv a := rfl

lemma codegree_cross (R : A → F × V → Prop) (S : C → F × V → Prop)
    (i j t u : F) (v w : V) (hij : i ≠ j) :
    codegree (complete R S) (i,(t,v)) (j,(u,w)) = codegree S (i,v) (j,w) :=
  Nat.card_congr (crossCommonEquiv R S i j t u v w hij)

/-- A column receives one old neighbourhood and one new neighbourhood
for each possible slope. -/
def columnEquiv (R : A → F × V → Prop) (S : C → F × V → Prop)
    (i t : F) (v : V) :
    {a // complete R S a (i,(t,v))} ≃
      ({a // R a (t,v)} ⊕ (F × {a // S a (i,v)})) where
  toFun a := match a with
    | ⟨.inl a,ha⟩ => .inl ⟨a.2,ha.2⟩
    | ⟨.inr a,ha⟩ => .inr (a.1.1,⟨a.2,ha.2⟩)
  invFun a := match a with
    | .inl a => ⟨.inl (i,a.val),rfl,a.property⟩
    | .inr a => ⟨.inr ((a.1,t-a.1*i),a.2.val),by dsimp [complete,assemble,lift,profile]; constructor <;> first | ring | exact a.2.property⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    apply Subtype.ext
    cases a with
    | inl a => exact congrArg Sum.inl (Prod.ext ha.1.symm rfl)
    | inr a =>
      apply congrArg Sum.inr
      refine Prod.ext ?_ rfl
      refine Prod.ext rfl ?_
      change t-a.1.1*i = a.1.2
      have hh : t = a.1.1*i+a.1.2 := ha.1
      rw [hh]
      ring
  right_inv a := by cases a <;> rfl

lemma column_card [Finite F] [Finite A] [Finite C]
    (R : A → F × V → Prop) (S : C → F × V → Prop) (i t : F) (v : V) :
    Nat.card {a // complete R S a (i,(t,v))} =
      Nat.card {a // R a (t,v)} + Nat.card F * Nat.card {a // S a (i,v)} := by
  rw [Nat.card_congr (columnEquiv R S i t v),Nat.card_sum,Nat.card_prod]

#print axioms complete_no_theta
#print axioms codegree_cross

def oldRowEquiv (R : A → F × V → Prop) (S : C → F × V → Prop) (i : F) (a : A) :
    {b // complete R S (.inl (i,a)) b} ≃ {b // R a b} where
  toFun b := ⟨b.val.2,b.property.2⟩
  invFun b := ⟨(i,b.val),rfl,b.property⟩
  left_inv b := Subtype.ext (Prod.ext b.property.1 rfl)
  right_inv _b := rfl

def newRowEquiv (R : A → F × V → Prop) (S : C → F × V → Prop) (p : F × F) (a : C) :
    {b // complete R S (.inr (p,a)) b} ≃ {b // S a b} where
  toFun b := ⟨(b.val.1,b.val.2.2),b.property.2⟩
  invFun b := ⟨(b.val.1,(profile p b.val.1,b.val.2)),rfl,b.property⟩
  left_inv b := Subtype.ext (Prod.ext rfl (Prod.ext b.property.1.symm rfl))
  right_inv _b := rfl

lemma old_row_card (R : A → F × V → Prop) (S : C → F × V → Prop) (i : F) (a : A) :
    Nat.card {b // complete R S (.inl (i,a)) b} = Nat.card {b // R a b} :=
  Nat.card_congr (oldRowEquiv R S i a)

lemma new_row_card (R : A → F × V → Prop) (S : C → F × V → Prop) (p : F × F) (a : C) :
    Nat.card {b // complete R S (.inr (p,a)) b} = Nat.card {b // S a b} :=
  Nat.card_congr (newRowEquiv R S p a)

lemma incidence_sum {X Y : Type*} [Fintype X] [Fintype Y] (R : X → Y → Prop) :
    Nat.card {p : X × Y // R p.1 p.2} = ∑ a, Nat.card {b // R a b} := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype R),Nat.card_sigma]

lemma incidence_card [Fintype F] [Fintype A] [Fintype C] [Fintype V]
    (R : A → F × V → Prop) (S : C → F × V → Prop) :
    Nat.card {p : ((F × A) ⊕ ((F × F) × C)) × (F × (F × V)) // complete R S p.1 p.2} =
      Nat.card F * Nat.card {p : A × (F × V) // R p.1 p.2} +
      (Nat.card F)^2 * Nat.card {p : C × (F × V) // S p.1 p.2} := by
  classical
  rw [incidence_sum,Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type,old_row_card,new_row_card]
  rw [incidence_sum,incidence_sum]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
  ring

/-- Light pairs whose first coordinates differ. Diagonal pairs are not
in this subtype, whereas the original weighted estimate counts them. -/
abbrev CrossLight {X W : Type*} (R : X → F × W → Prop) :=
  {p : (F × W) × (F × W) // p.1.1 ≠ p.2.1 ∧ codegree R p.1 p.2 ≤ 2}

def crossLightEquiv (R : A → F × V → Prop) (S : C → F × V → Prop) :
    CrossLight (complete R S) ≃ (F × F) × CrossLight S where
  toFun p := ((p.val.1.2.1,p.val.2.2.1),
    ⟨((p.val.1.1,p.val.1.2.2),(p.val.2.1,p.val.2.2.2)),p.property.1,
      by rw [← codegree_cross R S _ _ p.val.1.2.1 p.val.2.2.1 _ _ p.property.1]; exact p.property.2⟩)
  invFun p := ⟨((p.2.val.1.1,(p.1.1,p.2.val.1.2)),(p.2.val.2.1,(p.1.2,p.2.val.2.2))),
    p.2.property.1,by rw [codegree_cross R S _ _ _ _ _ _ p.2.property.1]; exact p.2.property.2⟩
  left_inv p := rfl
  right_inv p := rfl

lemma cross_light_card [Finite F] [Finite C] [Finite V]
    (R : A → F × V → Prop) (S : C → F × V → Prop) :
    Nat.card (CrossLight (complete R S)) = (Nat.card F)^2 * Nat.card (CrossLight S) := by
  rw [Nat.card_congr (crossLightEquiv R S),Nat.card_prod,Nat.card_prod,pow_two]

/-- This part of the normalized light-pair count is inherited unchanged
from the transversal component, independently of the old relation. -/
lemma cross_light_scaled [Finite F] [Finite C] [Finite V]
    (R : A → F × V → Prop) (S : C → F × V → Prop) :
    (Nat.card (F × V))^2 * Nat.card (CrossLight (complete R S)) =
      (Nat.card (F × (F × V)))^2 * Nat.card (CrossLight S) := by
  rw [cross_light_card]
  simp only [Nat.card_prod]
  ring

lemma row_bound_preserved {R : A → F × V → Prop} {S : C → F × V → Prop} (r : ℕ)
    (hR : ∀ a, Nat.card {b // R a b} ≤ r) (hS : ∀ a, Nat.card {b // S a b} ≤ r)
    (a : (F × A) ⊕ ((F × F) × C)) : Nat.card {b // complete R S a b} ≤ r := by
  cases a with
  | inl a => rw [old_row_card]; exact hR a.2
  | inr a => rw [new_row_card]; exact hS a.2

/-- Self-completion cannot decrease the column-degree/column-count ratio:
for every old column, its diagonal lift has this exact cross-multiplied
identity. In particular it does not repair a failed degree cap. -/
lemma self_column_scaled [Finite F] [Finite A] [Finite V]
    (R : A → F × V → Prop) (i : F) (v : V) :
    Nat.card (F × V) * Nat.card {a // complete R R a (i,(i,v))} =
      Nat.card (F × (F × V)) * Nat.card {a // R a (i,v)} +
      Nat.card (F × V) * Nat.card {a // R a (i,v)} := by
  rw [column_card]
  simp only [Nat.card_prod]
  ring

omit [Field F] in
lemma transversal_row_card [Finite F] {X : Type*} {R : X → F × V → Prop}
    (hR : Transversal R Prod.fst) (a : X) : Nat.card {b // R a b} ≤ Nat.card F := by
  apply Nat.card_le_card_of_injective (fun b : {b // R a b} => b.val.1)
  intro b c he
  exact Subtype.ext (hR a b.val c.val b.property c.property he)

/-- This particular affine completion cannot give a super-3/2 incidence
exponent in its total number of vertices. No theta hypothesis is needed
for this size bound, only the two transversal hypotheses. -/
theorem incidence_square_le_order_cube [Fintype F] [Fintype A] [Fintype C] [Fintype V]
    {R : A → F × V → Prop} {S : C → F × V → Prop}
    (hR : Transversal R Prod.fst) (hS : Transversal S Prod.fst) :
    (Nat.card {p : ((F × A) ⊕ ((F × F) × C)) × (F × (F × V)) // complete R S p.1 p.2})^2 ≤
      (Nat.card ((F × A) ⊕ ((F × F) × C)) + Nat.card (F × (F × V)))^3 := by
  classical
  by_cases hV : Nonempty V
  · let X := (F × A) ⊕ ((F × F) × C)
    let Y := F × (F × V)
    let q := Nat.card F
    let m := Nat.card X
    let k := Nat.card Y
    have hrow (a : X) : Nat.card {b // complete R S a b} ≤ q :=
      row_bound_preserved q (transversal_row_card hR) (transversal_row_card hS) a
    have he : Nat.card {p : X × Y // complete R S p.1 p.2} ≤ q*m := by
      rw [incidence_sum]
      calc
        _ ≤ ∑ _a : X, q := Finset.sum_le_sum (fun a _ => hrow a)
        _ = q*m := by simp [m,Nat.card_eq_fintype_card,Nat.mul_comm]
    have hv : 1 ≤ Nat.card V := Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hV,inferInstance⟩)
    have hq : q^2 ≤ m+k := by
      have hqk : q^2 ≤ k := by
        dsimp [k,Y,q]
        simp only [Nat.card_prod,pow_two]
        nlinarith [Nat.zero_le (Nat.card F)]
      omega
    change (Nat.card {p : X × Y // complete R S p.1 p.2})^2 ≤ (m+k)^3
    calc
      _ ≤ (q*m)^2 := Nat.pow_le_pow_left he 2
      _ = q^2*m^2 := by ring
      _ ≤ (m+k)*(m+k)^2 := Nat.mul_le_mul hq (Nat.pow_le_pow_left (Nat.le_add_right m k) 2)
      _ = (m+k)^3 := by ring
  · haveI : IsEmpty V := not_nonempty_iff.mp hV
    simp

#print axioms incidence_square_le_order_cube


#print axioms row_bound_preserved
#print axioms self_column_scaled


#print axioms incidence_card
#print axioms cross_light_card
#print axioms cross_light_scaled

#print axioms column_card
end Erdos713ThetaAffine
