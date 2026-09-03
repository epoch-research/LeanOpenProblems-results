import FormalConjecturesUtil
import Submission.ThetaZeroLinks

/-! Almost regularity and high density alone do not bound singleton pairs
by incidences. A sparse added edge set can create a quadratic singleton
budget. These examples are not asserted forbidden-pattern-free. -/
open Finset
open scoped Classical
namespace Erdos713SingletonBudgetInstability
open Erdos713GlobalLight Erdos713ThetaZeroLinks
set_option maxHeartbeats 2000000
abbrev V (b q : ℕ) := Fin b × Fin q

def base (b q : ℕ) (x y : V b q) : Prop := x.1=y.1
def rel (b q : ℕ) (x y : V b q) : Prop := x.1=y.1 ∨ (x.1<y.1 ∧ x.2=y.2)
noncomputable def edges {b q : ℕ} (R : V b q → V b q → Prop) : ℕ :=
  Nat.card {p : V b q × V b q // R p.1 p.2}

lemma base_le (b q : ℕ) : ∀ x y, base b q x y → rel b q x y := fun _ _ h => Or.inl h

lemma singleton_of_lt {b q : ℕ} {i j : Fin b} {y z : Fin q}
    (hij : i<j) (hyz : y ≠ z) : codegree (rel b q) (i,y) (j,z) = 1 := by
  have he (a : V b q) : rel b q a (i,y) ∧ rel b q a (j,z) ↔ a=(i,z) := by
    constructor
    · rintro ⟨ha,hb⟩
      rcases ha with ha | ⟨hai,hay⟩ <;> rcases hb with hb | ⟨haj,haz⟩
      · exact ((ne_of_lt hij) (ha.symm.trans hb)).elim
      · exact Prod.ext ha haz
      · have hh : j < i := by simpa only [hb] using hai
        exact (not_lt_of_ge hij.le hh).elim
      · exact (hyz (hay.symm.trans haz)).elim
    · rintro rfl
      exact ⟨Or.inl rfl,Or.inr ⟨hij,rfl⟩⟩
  simp [codegree,Nat.card_eq_fintype_card,he]

lemma singleton_of_ne {b q : ℕ} {i j : Fin b} {y z : Fin q}
    (hij : i ≠ j) (hyz : y ≠ z) : codegree (rel b q) (i,y) (j,z) = 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact singleton_of_lt h hyz
  · have hh := singleton_of_lt h hyz.symm
    simpa only [codegree,and_comm] using hh

theorem singleton_lower (b q : ℕ) :
    b*(b-1)*(q*(q-1)) ≤ (singleSet (rel b q)).card := by
  let S := (univ : Finset (Fin b)).offDiag ×ˢ (univ : Finset (Fin q)).offDiag
  let f : ((Fin b × Fin b) × (Fin q × Fin q)) → V b q × V b q :=
    fun p => ((p.1.1,p.2.1),(p.1.2,p.2.2))
  have hf : Function.Injective f := by
    rintro ⟨⟨i,j⟩,⟨y,z⟩⟩ ⟨⟨i',j'⟩,⟨y',z'⟩⟩ he
    simp only [f,Prod.mk.injEq] at he ⊢
    tauto
  have hsub : S.image f ⊆ singleSet (rel b q) := by
    intro p hp
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hp
    have ht' := mem_product.mp ht
    apply mem_filter.mpr
    exact ⟨mem_univ _,singleton_of_ne (mem_offDiag.mp ht'.1).2.2 (mem_offDiag.mp ht'.2).2.2⟩
  have hh := card_le_card hsub
  rw [card_image_of_injective _ hf] at hh
  simpa only [S,card_product,offDiag_card,card_univ,Fintype.card_fin,
    Nat.mul_sub_left_distrib,Nat.mul_one] using hh

lemma row_bounds (b q : ℕ) (a : V b q) :
    q ≤ Nat.card {y // rel b q a y} ∧ Nat.card {y // rel b q a y} ≤ q+b := by
  let S : Finset (V b q) := univ.filter (rel b q a)
  have h₁ : univ.image (fun y : Fin q => (a.1,y)) ⊆ S := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    simp [S,rel]
  have h₂ : S ⊆ (univ.image (fun y : Fin q => (a.1,y))) ∪
      (univ.image (fun i : Fin b => (i,a.2))) := by
    intro y hy
    rcases (mem_filter.mp hy).2 with hi | ⟨_,hx⟩
    · exact mem_union_left _ (mem_image.mpr ⟨y.2,mem_univ _,Prod.ext hi rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨y.1,mem_univ _,Prod.ext rfl hx⟩)
  have hc₁ : (univ.image (fun y : Fin q => (a.1,y))).card=q := by
    rw [card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]
    simp
  have hc₂ : (univ.image (fun i : Fin b => (i,a.2))).card=b := by
    rw [card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
    simp
  have hCard : Nat.card {y // rel b q a y}=S.card := by
    simp only [S,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hCard]
  constructor
  · simpa only [hc₁] using card_le_card h₁
  · exact (card_le_card h₂).trans (by simpa only [hc₁,hc₂] using (card_union_le
      (univ.image (fun y : Fin q => (a.1,y))) (univ.image (fun i : Fin b => (i,a.2)))))

lemma column_bounds (b q : ℕ) (a : V b q) :
    q ≤ Nat.card {x // rel b q x a} ∧ Nat.card {x // rel b q x a} ≤ q+b := by
  let S : Finset (V b q) := univ.filter (fun x => rel b q x a)
  have h₁ : univ.image (fun y : Fin q => (a.1,y)) ⊆ S := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    simp [S,rel]
  have h₂ : S ⊆ (univ.image (fun y : Fin q => (a.1,y))) ∪
      (univ.image (fun i : Fin b => (i,a.2))) := by
    intro y hy
    rcases (mem_filter.mp hy).2 with hi | ⟨_,hx⟩
    · exact mem_union_left _ (mem_image.mpr ⟨y.2,mem_univ _,Prod.ext hi.symm rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨y.1,mem_univ _,Prod.ext rfl hx.symm⟩)
  have hc₁ : (univ.image (fun y : Fin q => (a.1,y))).card=q := by
    rw [card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]
    simp
  have hc₂ : (univ.image (fun i : Fin b => (i,a.2))).card=b := by
    rw [card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
    simp
  have hCard : Nat.card {x // rel b q x a}=S.card := by
    simp only [S,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hCard]
  constructor
  · simpa only [hc₁] using card_le_card h₁
  · exact (card_le_card h₂).trans (by simpa only [hc₁,hc₂] using (card_union_le
      (univ.image (fun y : Fin q => (a.1,y))) (univ.image (fun i : Fin b => (i,a.2)))))

lemma edges_upper (b q : ℕ) : edges (rel b q) ≤ b*q*(q+b) := by
  rw [edges,Erdos713ThetaSplit.edge_card_eq_rows]
  calc
    _ ≤ ∑ _a : V b q, (q+b) := sum_le_sum (fun a _ => (row_bounds b q a).2)
    _ = _ := by simp [V]

lemma base_codegree (b q : ℕ) (x y : V b q) :
    codegree (base b q) x y = if x.1=y.1 then q else 0 := by
  by_cases h : x.1=y.1
  · let e : {a : V b q // base b q a x ∧ base b q a y} ≃ Fin q := {
      toFun := fun a => a.val.2
      invFun := fun j => ⟨(x.1,j),rfl,h⟩
      left_inv := fun a => Subtype.ext (Prod.ext a.property.1.symm rfl)
      right_inv := fun _ => rfl }
    change Nat.card _ = _
    rw [Nat.card_congr e]
    simp [h]
  · have hh : IsEmpty {a : V b q // base b q a x ∧ base b q a y} :=
      ⟨fun a => h (a.property.1.symm.trans a.property.2)⟩
    letI := hh
    simp [codegree,h]

lemma base_no_singletons (b q : ℕ) (hq : 2 ≤ q) : singleSet (base b q)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh := (mem_filter.mp hp).2
  rw [base_codegree] at hh
  split_ifs at hh
  omega

lemma base_edges (b q : ℕ) : edges (base b q)=b*q^2 := by
  let e : {p : V b q × V b q // base b q p.1 p.2} ≃ Fin b × (Fin q × Fin q) := {
    toFun := fun p => (p.val.1.1,p.val.1.2,p.val.2.2)
    invFun := fun p => ⟨((p.1,p.2.1),(p.1,p.2.2)),rfl⟩
    left_inv := fun p => Subtype.ext (Prod.ext rfl (Prod.ext p.property rfl))
    right_inv := fun _ => rfl }
  rw [edges,Nat.card_congr e]
  simp [pow_two]

lemma added_edges_le (b q : ℕ) :
    Nat.card {p : V b q × V b q // rel b q p.1 p.2 ∧ ¬ base b q p.1 p.2} ≤ b^2*q := by
  let f : {p : V b q × V b q // rel b q p.1 p.2 ∧ ¬ base b q p.1 p.2} →
      (Fin b × Fin b) × Fin q := fun p => ((p.val.1.1,p.val.2.1),p.val.1.2)
  have hf : Function.Injective f := by
    intro p s he
    have hp : p.val.1.2=p.val.2.2 := (p.property.1.resolve_left p.property.2).2
    have hs : s.val.1.2=s.val.2.2 := (s.property.1.resolve_left s.property.2).2
    have hi := congrArg (fun x : (Fin b × Fin b) × Fin q => x.1.1) he
    have hj := congrArg (fun x : (Fin b × Fin b) × Fin q => x.1.2) he
    have hk := congrArg Prod.snd he
    exact Subtype.ext (Prod.ext (Prod.ext hi hk) (Prod.ext hj (hp.symm.trans (hk.trans hs))))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin,pow_two] using
    Fintype.card_le_of_injective f hf

/-- The singleton-to-edge ratio is unbounded even when every degree lies
between q and 2q. This conclusion does not assert forbiddenness. -/
theorem singleton_ratio {b q C : ℕ} (hb : 2 ≤ b) (hbq : b ≤ q) (hC : 8*C < b) :
    C*edges (rel b q) < (singleSet (rel b q)).card := by
  have hq : 2 ≤ q := hb.trans hbq
  have h₁ : b ≤ 2*(b-1) := by omega
  have h₂ : q ≤ 2*(q-1) := by omega
  have hm := Nat.mul_le_mul h₁ h₂
  have hm' := Nat.mul_le_mul_left (b*q) hm
  have hZ := Nat.mul_le_mul_left 4 (singleton_lower b q)
  have hZ' : b^2*q^2 ≤ 4*(singleSet (rel b q)).card := by nlinarith only [hm',hZ]
  have hE : edges (rel b q) ≤ 2*b*q^2 := by
    have hh := Nat.mul_le_mul_left (b*q) (show q+b ≤ 2*q by omega)
    exact (edges_upper b q).trans (by nlinarith only [hh])
  have hCE := Nat.mul_le_mul_left (4*C) hE
  have ht := Nat.mul_lt_mul_of_pos_right hC (show 0 < b*q^2 by positivity)
  nlinarith only [hZ',hCE,ht]

/-- With q=b^2, deleting the added matching edges costs at most 1/b of
the retained block edges, yet eliminates every singleton pair for b>=2. -/
theorem cheap_cleanup (b : ℕ) (hb : 2 ≤ b) :
    b*Nat.card {p : V b (b^2) × V b (b^2) //
      rel b (b^2) p.1 p.2 ∧ ¬ base b (b^2) p.1 p.2} ≤ edges (base b (b^2)) ∧
    singleSet (base b (b^2))=∅ := by
  refine ⟨?_,base_no_singletons b (b^2) (by nlinarith)⟩
  have hh := Nat.mul_le_mul_left b (added_edges_le b (b^2))
  rw [base_edges]
  nlinarith only [hh]

#print axioms singleton_ratio
#print axioms cheap_cleanup
#print axioms singleton_lower
#print axioms row_bounds
#print axioms column_bounds
#print axioms edges_upper
#print axioms base_no_singletons
#print axioms base_edges
#print axioms added_edges_le
end Erdos713SingletonBudgetInstability
