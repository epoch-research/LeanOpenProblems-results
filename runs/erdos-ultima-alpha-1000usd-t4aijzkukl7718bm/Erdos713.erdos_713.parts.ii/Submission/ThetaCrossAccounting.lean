import FormalConjecturesUtil
import Submission.ThetaOverlapAccounting

/-! Weighted accounting for all row overlaps of size at least two.
This does not assert the capped weighted theta estimate or settle Erdos 713. -/
open Finset
namespace Erdos713ThetaCrossAccounting
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma cross_light_of_two_common [Fintype A] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {a b : A} (hab : a ≠ b)
    {z w x y : B} (hzw : z ≠ w) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hxy : x ≠ y)
    (haz : R a z) (haw : R a w) (hbz : R b z) (hbw : R b w)
    (hax : R a x) (hby : R b y) : codegree R x y ≤ 2 := by
  classical
  by_contra h
  obtain ⟨c,hca,hcb,hcx,hcy⟩ := third_common_of_codegree
    (R := R) (x := x) (y := y) (by omega) a b
  let f : Fin 3 → A := ![a,b,c]
  let g : Fin 4 → B := ![z,w,x,y]
  have hfi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hgi : Function.Injective g := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  exact hf ⟨f,g,hfi,hgi,haz,hbz,haw,hbw,hax,hcx,hby,hcy⟩

open scoped Classical in
noncomputable def overlapPairs [Fintype A] [Fintype B]
    (R : A → B → Prop) : Finset (A × A) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ 2 ≤ (row R p.1 ∩ row R p.2).card)

lemma cross_card_lower [DecidableEq B] (S T : Finset B) :
    S.card*(T.card-1) ≤ ((S ×ˢ T).filter (fun p => p.1 ≠ p.2)).card := by
  classical
  have he : ((S ×ˢ T).filter (fun p => p.1 ≠ p.2)) =
      S.biUnion (fun x => ({x} : Finset B) ×ˢ (T.erase x)) := by
    ext p
    simp only [mem_filter,mem_product,mem_biUnion,mem_erase,mem_singleton]
    constructor
    · rintro ⟨⟨hx,hy⟩,hne⟩
      exact ⟨p.1,hx,rfl,Ne.symm hne,hy⟩
    · rintro ⟨x,hx,hpx,hne,hy⟩
      subst x
      exact ⟨⟨hx,hy⟩,Ne.symm hne⟩
  rw [he,card_biUnion]
  · simp only [card_product,card_singleton,one_mul]
    calc
      _ = ∑ _x ∈ S, (T.card-1) := by simp
      _ ≤ _ := sum_le_sum (fun x _ => by
        by_cases hx : x ∈ T
        · rw [card_erase_of_mem hx]
        · rw [erase_eq_of_notMem hx]
          omega)
  · intro x hx y hy hxy
    apply disjoint_left.mpr
    rintro p hp hq
    have hpx : p.1 = x := by simpa using (mem_product.mp hp).1
    have hpy : p.1 = y := by simpa using (mem_product.mp hq).1
    exact hxy (hpx.symm.trans hpy)

open scoped Classical in
/-- Two chosen common columns leave a cross rectangle whose distinct pairs
are all light. This statement includes intersections of size two or three. -/
lemma row_pair_charge [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (p : ↥(overlapPairs R)) :
    ∃ X : Finset (B × B),
      X ⊆ lightSet R ∧
      (∀ q ∈ X, R p.val.1 q.1 ∧ R p.val.2 q.2) ∧
      ((row R p.val.1).card-2)*((row R p.val.2).card-3) ≤ X.card := by
  classical
  have hp := (mem_filter.mp p.property).2
  obtain ⟨Z,hZsub,hZcard⟩ := exists_subset_card_eq hp.2
  obtain ⟨z,w,hzw,hZ⟩ := card_eq_two.mp hZcard
  subst Z
  have hz : z ∈ row R p.val.1 ∩ row R p.val.2 := hZsub (by simp)
  have hw : w ∈ row R p.val.1 ∩ row R p.val.2 := hZsub (by simp)
  let S := row R p.val.1 \ {z,w}
  let T := row R p.val.2 \ {z,w}
  let X := (S ×ˢ T).filter (fun q => q.1 ≠ q.2)
  have hS : S.card = (row R p.val.1).card-2 := by
    rw [card_sdiff_of_subset (hZsub.trans inter_subset_left)]
    simp [hzw]
  have hT : T.card = (row R p.val.2).card-2 := by
    rw [card_sdiff_of_subset (hZsub.trans inter_subset_right)]
    simp [hzw]
  refine ⟨X,?_,?_,?_⟩
  · intro q hq
    obtain ⟨hprod,hxy⟩ := mem_filter.mp hq
    obtain ⟨hx,hy⟩ := mem_product.mp hprod
    have hxs := mem_sdiff.mp hx
    have hys := mem_sdiff.mp hy
    have hxzw : q.1 ≠ z ∧ q.1 ≠ w := by simpa using hxs.2
    have hyzw : q.2 ≠ z ∧ q.2 ≠ w := by simpa using hys.2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    exact cross_light_of_two_common hf hp.1 hzw hxzw.1 hxzw.2 hyzw.1 hyzw.2 hxy
      ((mem_row R _ _).mp (mem_inter.mp hz).1)
      ((mem_row R _ _).mp (mem_inter.mp hw).1)
      ((mem_row R _ _).mp (mem_inter.mp hz).2)
      ((mem_row R _ _).mp (mem_inter.mp hw).2)
      ((mem_row R _ _).mp hxs.1) ((mem_row R _ _).mp hys.1)
  · intro q hq
    have hq' := mem_product.mp (mem_filter.mp hq).1
    exact ⟨(mem_row R _ _).mp (mem_sdiff.mp hq'.1).1,
      (mem_row R _ _).mp (mem_sdiff.mp hq'.2).1⟩
  · have hc := cross_card_lower S T
    simpa only [hS,hT,Nat.sub_sub] using hc

open scoped Classical in
/-- The charge multiplicity of an ordered light pair (x,y) is at most the
product of its two column degrees. No bounded absolute multiplicity is assumed. -/
theorem weighted_cross_sum [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) :
    (∑ p ∈ overlapPairs R,
      ((row R p.1).card-2)*((row R p.2).card-3)) ≤
      ∑ q ∈ lightSet R, Nat.card {a // R a q.1}*Nat.card {a // R a q.2} := by
  classical
  choose X hXsub hXadj hXcard using row_pair_charge hf
  let P := ↥(overlapPairs R)
  let Inc : P → (B × B) → Prop := fun p q => q ∈ X p
  have hleft : (∑ p ∈ overlapPairs R,
      ((row R p.1).card-2)*((row R p.2).card-3)) ≤ ∑ p : P, (X p).card := by
    rw [← sum_coe_sort (overlapPairs R)
      (fun p : A × A => ((row R p.1).card-2)*((row R p.2).card-3))]
    exact sum_le_sum (fun p _ => hXcard p)
  have habove (p : P) : (lightSet R).bipartiteAbove Inc p = X p := by
    ext q
    simp only [bipartiteAbove,mem_filter,Inc]
    exact and_iff_right_of_imp (fun h => hXsub p h)
  have hbelow (q : B × B) :
      ((univ : Finset P).bipartiteBelow Inc q).card ≤
        Nat.card {a // R a q.1}*Nat.card {a // R a q.2} := by
    let f : ↥((univ : Finset P).bipartiteBelow Inc q) →
        {a // R a q.1} × {a // R a q.2} := fun p =>
      ⟨⟨p.val.val.1,(hXadj p.val q (mem_filter.mp p.property).2).1⟩,
       ⟨p.val.val.2,(hXadj p.val q (mem_filter.mp p.property).2).2⟩⟩
    have hf : Function.Injective f := by
      intro p r he
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z => z.1.val) he) (congrArg (fun z => z.2.val) he)
    have hh := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_prod] using hh
  calc
    _ ≤ ∑ p : P, (X p).card := hleft
    _ = ∑ p : P, ((lightSet R).bipartiteAbove Inc p).card := by simp only [habove]
    _ = ∑ q ∈ lightSet R, ((univ : Finset P).bipartiteBelow Inc q).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ _ := sum_le_sum (fun q _ => hbelow q)

open scoped Classical in
/-- A maximum-column-degree corollary, without any D <= K*|B| assumption. -/
theorem cross_sum_le_degree_sq_light [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (D : ℕ)
    (hD : ∀ b, Nat.card {a // R a b} ≤ D) :
    (∑ p ∈ overlapPairs R,
      ((row R p.1).card-2)*((row R p.2).card-3)) ≤ D^2*lightCount R := by
  classical
  apply (weighted_cross_sum hf).trans
  calc
    _ ≤ ∑ _q ∈ lightSet R, D*D := sum_le_sum (fun q _ => Nat.mul_le_mul (hD q.1) (hD q.2))
    _ = _ := by simp [lightSet_card,pow_two,Nat.mul_comm]

#print axioms cross_light_of_two_common
#print axioms row_pair_charge
#print axioms weighted_cross_sum
#print axioms cross_sum_le_degree_sq_light
end Erdos713ThetaCrossAccounting
