import FormalConjecturesUtil
import Submission.ThetaGram
import Submission.GlobalLightPairs

/-! A linear bound for an oriented-theta-free relation with no light
pair of distinct columns. This is not a general extremal exponent bound. -/
open Finset
namespace Erdos713ThetaHeavyShadow
open Erdos713ThetaGram Erdos713GlobalLight
variable {A B : Type*}

open scoped Classical in
noncomputable def row [Fintype B] (R : A → B → Prop) (a : A) : Finset B :=
  univ.filter (R a)

lemma mem_row [Fintype B] (R : A → B → Prop) (a : A) (b : B) : b ∈ row R a ↔ R a b := by
  classical
  simp [row]

def Heavy (R : A → B → Prop) : Prop := ∀ x y : B, x ≠ y → 3 ≤ codegree R x y

lemma third_common [Fintype A] {R : A → B → Prop} (h : Heavy R)
    {x y : B} (hxy : x ≠ y) (a b : A) :
    ∃ c : A, c ≠ a ∧ c ≠ b ∧ R c x ∧ R c y := by
  classical
  let S := (univ : Finset A).filter (fun c => R c x ∧ R c y)
  have hS : 3 ≤ S.card := by
    simpa only [S,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using h x y hxy
  have hc : ({a,b} : Finset A).card < S.card := (Finset.card_le_two.trans_lt (by omega))
  obtain ⟨c,hcS,hc⟩ := exists_mem_notMem_of_card_lt_card hc
  simp only [mem_insert,mem_singleton,not_or] at hc
  exact ⟨c,hc.1,hc.2,(mem_filter.mp hcS).2⟩

lemma no_large_overlap [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) {a b : A} (hab : a ≠ b)
    (ha : 4 ≤ (row R a).card) (hb : 3 ≤ (row R b).card)
    {z w : B} (hzw : z ≠ w) (haz : R a z) (haw : R a w)
    (hbz : R b z) (hbw : R b w) : False := by
  classical
  obtain ⟨y,hyR,hy⟩ := exists_mem_notMem_of_card_lt_card
    (show ({z,w} : Finset B).card < (row R b).card from Finset.card_le_two.trans_lt (by omega))
  have hby := (mem_row R b y).mp hyR
  simp only [mem_insert,mem_singleton,not_or] at hy
  have hsmall : ({z,w,y} : Finset B).card ≤ 3 := by
    exact (card_insert_le _ _).trans (by have := (Finset.card_le_two (a := w) (b := y)); omega)
  obtain ⟨x,hxR,hx⟩ := exists_mem_notMem_of_card_lt_card
    (show ({z,w,y} : Finset B).card < (row R a).card from hsmall.trans_lt (by omega))
  have hax := (mem_row R a x).mp hxR
  simp only [mem_insert,mem_singleton,not_or] at hx
  obtain ⟨c,hca,hcb,hcx,hcy⟩ := third_common hh hx.2.2 a b
  let f : Fin 3 → A := ![a,b,c]
  let g : Fin 4 → B := ![z,w,x,y]
  have hfi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hgi : Function.Injective g := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  exact hf ⟨f,g,hfi,hgi,haz,hbz,haw,hbw,hax,hcx,hby,hcy⟩

lemma high_pair_unique [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) {a b : A}
    (ha : 4 ≤ (row R a).card) (hb : 4 ≤ (row R b).card)
    (P : Finset B) (hP : P.card = 2) (hPa : P ⊆ row R a) (hPb : P ⊆ row R b) : a = b := by
  classical
  obtain ⟨z,w,hzw,rfl⟩ := card_eq_two.mp hP
  by_contra hab
  exact no_large_overlap hf hh hab ha (by omega) hzw
    ((mem_row R a z).mp (hPa (by simp))) ((mem_row R a w).mp (hPa (by simp)))
    ((mem_row R b z).mp (hPb (by simp))) ((mem_row R b w).mp (hPb (by simp)))

lemma pair_has_low_row [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) {a : A}
    (ha : 4 ≤ (row R a).card) (P : Finset B) (hP : P.card = 2) (hPa : P ⊆ row R a) :
    ∃ b : A, (row R b).card ≤ 2 ∧ row R b = P := by
  classical
  obtain ⟨z,w,hzw,rfl⟩ := card_eq_two.mp hP
  obtain ⟨b,hba,_,hbz,hbw⟩ := third_common hh hzw a a
  have hlow : (row R b).card ≤ 2 := by
    by_contra hbad
    exact no_large_overlap hf hh hba.symm ha (by omega) hzw
      ((mem_row R a z).mp (hPa (by simp))) ((mem_row R a w).mp (hPa (by simp))) hbz hbw
  have hsub : ({z,w} : Finset B) ⊆ row R b := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl <;> apply (mem_row R _ _).mpr <;> assumption
  refine ⟨b,hlow,(eq_of_subset_of_card_le hsub ?_).symm⟩
  simpa [hzw] using hlow

open scoped Classical in
noncomputable def highRows [Fintype A] [Fintype B] (R : A → B → Prop) : Finset A :=
  univ.filter (fun a => 4 ≤ (row R a).card)
open scoped Classical in
noncomputable def lowRows [Fintype A] [Fintype B] (R : A → B → Prop) : Finset A :=
  univ.filter (fun a => (row R a).card ≤ 2)

lemma high_pairs_le_low_rows [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) :
    (∑ a ∈ highRows R, (row R a).card.choose 2) ≤ (lowRows R).card := by
  classical
  let T := (a : highRows R) × ((row R a.val).powersetCard 2)
  have hex (p : T) : ∃ b : lowRows R, row R b.val = p.2.val := by
    have ha : 4 ≤ (row R p.1.val).card := (mem_filter.mp p.1.property).2
    have hP := mem_powersetCard.mp p.2.property
    obtain ⟨b,hb,he⟩ := pair_has_low_row hf hh ha p.2.val hP.2 hP.1
    exact ⟨⟨b,by simp [lowRows,hb]⟩,he⟩
  choose b hb using hex
  have hinj : Function.Injective b := by
    rintro ⟨a,P⟩ ⟨a',P'⟩ he
    have hPP : P.val = P'.val := (hb ⟨a,P⟩).symm.trans ((congrArg (fun b : lowRows R => row R b.val) he).trans (hb ⟨a',P'⟩))
    have haa : a.val = a'.val := by
      have ha : 4 ≤ (row R a.val).card := (mem_filter.mp a.property).2
      have ha' : 4 ≤ (row R a'.val).card := (mem_filter.mp a'.property).2
      have hP := mem_powersetCard.mp P.property
      have hP' := mem_powersetCard.mp P'.property
      exact high_pair_unique hf hh ha ha' P.val hP.2 hP.1 (hPP ▸ hP'.1)
    have haa' : a = a' := Subtype.ext haa
    subst a'
    congr 1
    exact Subtype.ext hPP
  have hc := Fintype.card_le_of_injective b hinj
  have heq : Fintype.card T = ∑ a ∈ highRows R, (row R a).card.choose 2 := by
    simp only [T,Fintype.card_sigma,Fintype.card_coe,card_powersetCard]
    exact sum_coe_sort (highRows R) (fun a => (row R a).card.choose 2)
  rw [heq,Fintype.card_coe] at hc
  exact hc

lemma le_choose_two {r : ℕ} (hr : 3 ≤ r) : r ≤ r.choose 2 := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    change n+1 ≤ n+n.choose 2
    omega

/-- Without light pairs, high-degree rows force sufficiently many
low-degree rows that the total incidence count is linear in the row count. -/
theorem incidences_le_three_rows [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hh : Heavy R) :
    (∑ a : A, (row R a).card) ≤ 3*Fintype.card A := by
  classical
  have hhigh : (∑ a ∈ highRows R, (row R a).card) ≤ (lowRows R).card := by
    apply le_trans _ (high_pairs_le_low_rows hf hh)
    apply sum_le_sum
    intro a ha
    have h : 4 ≤ (row R a).card := by simpa [highRows] using ha
    exact le_choose_two (by omega)
  have hp (a : A) : (row R a).card + (if (row R a).card ≤ 2 then 1 else 0) ≤
      (if 4 ≤ (row R a).card then (row R a).card else 0)+3 := by
    split_ifs <;> omega
  have hs := sum_le_sum (s := (univ : Finset A)) (fun a _ => hp a)
  have hlow : (∑ a : A, if (row R a).card ≤ 2 then 1 else 0) = (lowRows R).card := by
    simp only [lowRows,card_eq_sum_ones,sum_filter]
  have hhi : (∑ a : A, if 4 ≤ (row R a).card then (row R a).card else 0) =
      ∑ a ∈ highRows R, (row R a).card := by simp [highRows,sum_filter]
  simp only [sum_add_distrib,sum_const,card_univ,Nat.nsmul_eq_mul,hlow,hhi] at hs
  omega


/-- Removing a vertex cover of the light-pair graph gives a genuinely
heavy restriction. The cost is the sum of degrees of removed columns. -/
theorem incidences_le_of_light_cover [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (X : Finset B) (D : ℕ)
    (hD : ∀ b : B, Nat.card {a // R a b} ≤ D)
    (hX : ∀ x ∉ X, ∀ y ∉ X, x ≠ y → 3 ≤ codegree R x y) :
    (∑ a : A, (row R a).card) ≤ 3*Fintype.card A+D*X.card := by
  classical
  let I : Finset B := univ \ X
  let Q : A → I → Prop := fun a b => R a b.val
  have hQ : ¬ HasTheta Q := by
    rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
    exact hf ⟨f,fun j => (g j).val,hfi,Subtype.val_injective.comp hgi,
      h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hheavy : Heavy Q := by
    intro x y hxy
    exact hX x.val (mem_sdiff.mp x.property).2 y.val (mem_sdiff.mp y.property).2
      (fun h => hxy (Subtype.ext h))
  have hbound := incidences_le_three_rows hQ hheavy
  have hrow (a : A) : (row Q a).card = (row R a \ X).card := by
    apply card_bij (fun (b : I) _ => b.val)
    · intro b hb
      exact mem_sdiff.mpr ⟨(mem_row R a b.val).mpr ((mem_row Q a b).mp hb),
        (mem_sdiff.mp b.property).2⟩
    · intro b hb c hc hbc
      exact Subtype.ext hbc
    · intro b hb
      obtain ⟨hbR,hbX⟩ := mem_sdiff.mp hb
      let b' : I := ⟨b,mem_sdiff.mpr ⟨mem_univ _,hbX⟩⟩
      exact ⟨b',(mem_row Q a b').mpr ((mem_row R a b).mp hbR),rfl⟩
  have hkeep : (∑ a : A, (row R a \ X).card) ≤ 3*Fintype.card A := by
    simpa only [hrow] using hbound
  have hdrop : (∑ a : A, (row R a ∩ X).card) ≤ D*X.card := by
    have he (a : A) : row R a ∩ X = X.bipartiteAbove R a := by
      ext b
      simp [row,bipartiteAbove,and_comm]
    simp_rw [he]
    rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R (s := univ) (t := X)]
    calc
      (∑ b ∈ X, ((univ : Finset A).bipartiteBelow R b).card) ≤ ∑ _b ∈ X, D := by
        apply sum_le_sum
        intro b hb
        simpa only [bipartiteBelow,Nat.card_eq_fintype_card,Fintype.card_subtype] using hD b
      _ = D*X.card := by simp [Nat.mul_comm]
  have hsplit : (∑ a : A, (row R a).card) =
      (∑ a : A, (row R a \ X).card)+(∑ a : A, (row R a ∩ X).card) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    exact (card_sdiff_add_card_inter (row R a) X).symm
  rw [hsplit]
  exact Nat.add_le_add hkeep hdrop

/-- In particular, a nonempty relation of minimum row degree at least
four cannot have all distinct column pairs heavy while avoiding theta. -/
theorem exists_light_pair_of_min_row [Fintype A] [Fintype B] [Nonempty A]
    {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hmin : ∀ a : A, 4 ≤ (row R a).card) :
    ∃ x y : B, x ≠ y ∧ codegree R x y ≤ 2 := by
  by_contra hh
  push_neg at hh
  have hheavy : Heavy R := fun x y hxy => by have := hh x y hxy; omega
  have hu := incidences_le_three_rows hf hheavy
  have hl := sum_le_sum (s := (univ : Finset A)) (fun a _ => hmin a)
  simp only [sum_const,card_univ,Nat.nsmul_eq_mul] at hl
  have hp : 0 < Fintype.card A := Fintype.card_pos
  omega

#print axioms no_large_overlap
#print axioms pair_has_low_row
#print axioms high_pairs_le_low_rows
#print axioms incidences_le_three_rows
#print axioms incidences_le_of_light_cover
#print axioms exists_light_pair_of_min_row
end Erdos713ThetaHeavyShadow
