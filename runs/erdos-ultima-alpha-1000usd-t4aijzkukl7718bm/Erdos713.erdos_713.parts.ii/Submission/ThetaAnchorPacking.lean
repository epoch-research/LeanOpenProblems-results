import FormalConjecturesUtil
import Submission.ThetaCrossAccounting

/-! Packing anchor witnesses around a fixed row. These finite statements do
not assert a solution to the rationality conjecture. -/
open Finset
namespace Erdos713ThetaAnchorPacking
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaCrossAccounting
variable {A B : Type*}
set_option maxHeartbeats 2000000

open scoped Classical in
noncomputable def commonRows [Fintype B] (R : A → B → Prop)
    (S : Finset A) (p : B × B) : Finset A := S.filter (fun a => R a p.1 ∧ R a p.2)

open scoped Classical in
noncomputable def anchors [Fintype B] (R : A → B → Prop)
    (S : Finset A) (a : A) : Finset (B × B) :=
  (row R a).offDiag.filter (fun p => 3 ≤ (commonRows R S p).card)

open scoped Classical in
noncomputable def lightAt [Fintype B] (R : A → B → Prop) (a : A) : Finset (B × B) :=
  (lightSet R).filter (fun p => R a p.1)

lemma anchor_heavy [Fintype A] [Fintype B] {R : A → B → Prop}
    {S : Finset A} {a : A} {p : B × B} (hp : p ∈ anchors R S a) :
    3 ≤ codegree R p.1 p.2 := by
  classical
  have hp' := (mem_filter.mp hp).2
  have hsub : commonRows R S p ⊆ (univ : Finset A).filter (fun b => R b p.1 ∧ R b p.2) := by
    intro b hb
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hb).2⟩
  have hh := hp'.trans (card_le_card hsub)
  simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh

open scoped Classical in
lemma anchor_witness [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {S : Finset A} {a : A}
    (p : ↥(anchors R S a)) :
    ∃ b ∈ S, b ≠ a ∧ R b p.val.1 ∧ R b p.val.2 ∧
      (row R a ∩ row R b).card ≤ 3 := by
  classical
  have hp := mem_filter.mp p.property
  have hpa := mem_offDiag.mp hp.1
  obtain ⟨b,hb,hba⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a} : Finset A).card < (commonRows R S p.val).card by simpa using (by omega : 1 < (commonRows R S p.val).card))
  have hb' := mem_filter.mp hb
  have hba' : b ≠ a := by simpa using hba
  refine ⟨b,hb'.1,hba',hb'.2.1,hb'.2.2,?_⟩
  by_contra hlarge
  have hl := large_overlap_cross_light hf hba'.symm (by omega) hpa.2.2
    ((mem_row R _ _).mp hpa.1) hb'.2.2
  have hh := anchor_heavy p.property
  omega

/-- Distinct witness rows sharing an outside column can only witness the
same unordered anchor pair. -/
lemma other_witness_endpoint [Fintype A] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {a b c : A}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {z w x y : B} (hzw : z ≠ w)
    (haz : R a z) (haw : R a w) (hbz : R b z) (hbw : R b w)
    (hax : R a x) (hcx : R c x) (hby : R b y) (hcy : R c y)
    (hay : ¬ R a y) : x = z ∨ x = w := by
  classical
  by_contra hh
  push_neg at hh
  have hyz : y ≠ z := fun h => hay (h ▸ haz)
  have hyw : y ≠ w := fun h => hay (h ▸ haw)
  have hxy : x ≠ y := fun h => hay (h ▸ hax)
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
/-- At most six ordered heavy anchors can have their chosen witnesses
pass through one fixed column outside the root row. -/
lemma outside_multiplicity [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {S : Finset A} {a : A}
    (b : ↥(anchors R S a) → A)
    (hb : ∀ p, b p ≠ a ∧ R (b p) p.val.1 ∧ R (b p) p.val.2 ∧
      (row R a ∩ row R (b p)).card ≤ 3)
    (y : B) (hay : ¬ R a y) :
    ((univ : Finset ↥(anchors R S a)).filter (fun p => R (b p) y)).card ≤ 6 := by
  classical
  let T := (univ : Finset ↥(anchors R S a)).filter (fun p => R (b p) y)
  by_cases hT : T.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hT
    have hy₀ : R (b p₀) y := (mem_filter.mp hp₀).2
    let I := row R a ∩ row R (b p₀)
    have hI : I.card ≤ 3 := (hb p₀).2.2.2
    have hp₀a := mem_offDiag.mp (mem_filter.mp p₀.property).1
    have hsub : ∀ p ∈ T, p.val ∈ I.offDiag := by
      intro p hp
      have hpa := mem_offDiag.mp (mem_filter.mp p.property).1
      have hpy : R (b p) y := (mem_filter.mp hp).2
      have hfirst : R (b p₀) p.val.1 := by
        by_cases he : b p = b p₀
        · simpa only [he] using (hb p).2.1
        · rcases other_witness_endpoint hf (hb p₀).1.symm (hb p).1 he hp₀a.2.2
            ((mem_row R _ _).mp hp₀a.1) ((mem_row R _ _).mp hp₀a.2.1)
            (hb p₀).2.1 (hb p₀).2.2.1
            ((mem_row R _ _).mp hpa.1) (hb p).2.1 hy₀ hpy hay with h | h
          · simpa only [h] using (hb p₀).2.1
          · simpa only [h] using (hb p₀).2.2.1
      have hsecond : R (b p₀) p.val.2 := by
        by_cases he : b p = b p₀
        · simpa only [he] using (hb p).2.2.1
        · rcases other_witness_endpoint hf (hb p₀).1.symm (hb p).1 he hp₀a.2.2
            ((mem_row R _ _).mp hp₀a.1) ((mem_row R _ _).mp hp₀a.2.1)
            (hb p₀).2.1 (hb p₀).2.2.1
            ((mem_row R _ _).mp hpa.2.1) (hb p).2.2.1 hy₀ hpy hay with h | h
          · simpa only [h] using (hb p₀).2.1
          · simpa only [h] using (hb p₀).2.2.1
      exact mem_offDiag.mpr ⟨mem_inter.mpr ⟨hpa.1,(mem_row R _ _).mpr hfirst⟩,
        mem_inter.mpr ⟨hpa.2.1,(mem_row R _ _).mpr hsecond⟩,hpa.2.2⟩
    have hc : T.card ≤ I.offDiag.card := card_le_card_of_injOn Subtype.val hsub
      (fun _ _ _ _ h => Subtype.ext h)
    have hi : I.offDiag.card ≤ 6 := by
      rw [offDiag_card]
      interval_cases h : I.card <;> simp
    exact hc.trans hi
  · have he : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 6
    simp [he]

open scoped Classical in
/-- Packing outside columns bounds the anchor mass at a fixed root. -/
theorem root_anchor_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card) (a : A) :
    (anchors R S a).card*((row R a).card-3)*(r-3) ≤ 6*(lightAt R a).card := by
  classical
  choose b hbS hbne hb1 hb2 hbI using (anchor_witness hf (S := S) (a := a))
  let P := ↥(anchors R S a)
  let X (p : P) : Finset (B × B) :=
    (row R a \ row R (b p)) ×ˢ (row R (b p) \ row R a)
  have hXsub (p : P) : X p ⊆ lightAt R a := by
    intro q hq
    obtain ⟨hx,hy⟩ := mem_product.mp hq
    obtain ⟨hax,hbx⟩ := mem_sdiff.mp hx
    obtain ⟨hby,hay⟩ := mem_sdiff.mp hy
    have haxR := (mem_row R _ _).mp hax
    have hbyR := (mem_row R _ _).mp hby
    have hbxR : ¬ R (b p) q.1 := by simpa [mem_row] using hbx
    have hayR : ¬ R a q.2 := by simpa [mem_row] using hay
    have hp := mem_offDiag.mp (mem_filter.mp p.property).1
    have hpa1 := (mem_row R _ _).mp hp.1
    have hpa2 := (mem_row R _ _).mp hp.2.1
    have hx1 : q.1 ≠ p.val.1 := fun h => hbxR (h ▸ hb1 p)
    have hx2 : q.1 ≠ p.val.2 := fun h => hbxR (h ▸ hb2 p)
    have hy1 : q.2 ≠ p.val.1 := fun h => hayR (h ▸ hpa1)
    have hy2 : q.2 ≠ p.val.2 := fun h => hayR (h ▸ hpa2)
    have hxy : q.1 ≠ q.2 := fun h => hayR (h ▸ haxR)
    have hl := cross_light_of_two_common hf (hbne p).symm hp.2.2
      hx1 hx2 hy1 hy2 hxy hpa1 hpa2 (hb1 p) (hb2 p) haxR hbyR
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hl⟩,haxR⟩
  have hXcard (p : P) : ((row R a).card-3)*(r-3) ≤ (X p).card := by
    have h1 : (row R a).card-3 ≤ (row R a \ row R (b p)).card := by
      rw [card_sdiff,inter_comm]
      exact Nat.sub_le_sub_left (hbI p) _
    have h2 : r-3 ≤ (row R (b p) \ row R a).card := by
      rw [card_sdiff]
      exact (Nat.sub_le_sub_right (hmin _ (hbS p)) 3).trans
        (Nat.sub_le_sub_left (hbI p) _)
    simpa only [X,card_product] using Nat.mul_le_mul h1 h2
  let Inc : P → (B × B) → Prop := fun p q => q ∈ X p
  have habove (p : P) : (lightAt R a).bipartiteAbove Inc p = X p := by
    ext q
    simp only [bipartiteAbove,mem_filter,Inc]
    exact and_iff_right_of_imp (fun h => hXsub p h)
  have hbelow (q : B × B) : ((univ : Finset P).bipartiteBelow Inc q).card ≤ 6 := by
    by_cases hay : R a q.2
    · have he : (univ : Finset P).bipartiteBelow Inc q = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hq : q ∈ X p := (mem_filter.mp hp).2
        exact (mem_sdiff.mp (mem_product.mp hq).2).2 ((mem_row R _ _).mpr hay)
      simp [he]
    · have hsub : (univ : Finset P).bipartiteBelow Inc q ⊆
          (univ : Finset P).filter (fun p => R (b p) q.2) := by
        intro p hp
        have hq : q ∈ X p := (mem_filter.mp hp).2
        exact mem_filter.mpr ⟨mem_univ _,(mem_row R _ _).mp
          (mem_sdiff.mp (mem_product.mp hq).2).1⟩
      exact (card_le_card hsub).trans (outside_multiplicity hf b
        (fun p => ⟨hbne p,hb1 p,hb2 p,hbI p⟩) q.2 hay)
  calc
    _ = ∑ _p : P, ((row R a).card-3)*(r-3) := by simp [P,Nat.mul_assoc]
    _ ≤ ∑ p : P, (X p).card := sum_le_sum (fun p _ => hXcard p)
    _ = ∑ p : P, ((lightAt R a).bipartiteAbove Inc p).card := by simp only [habove]
    _ = ∑ q ∈ lightAt R a, ((univ : Finset P).bipartiteBelow Inc q).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _q ∈ lightAt R a, 6 := sum_le_sum (fun q _ => hbelow q)
    _ = _ := by simp [Nat.mul_comm]

open scoped Classical in
/-- Summing the root packing bound costs only ONE column degree per
ordered light pair, not its product with the other column degree. -/
theorem total_anchor_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r D : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card)
    (hD : ∀ x, Nat.card {a // R a x} ≤ D) :
    (∑ a ∈ S, (anchors R S a).card*((row R a).card-3)*(r-3)) ≤
      6*D*lightCount R := by
  classical
  have hs : (∑ a ∈ S, (lightAt R a).card) ≤ D*lightCount R := by
    let Inc : A → (B × B) → Prop := fun a p => R a p.1
    have ha (a : A) : (lightSet R).bipartiteAbove Inc a = lightAt R a := rfl
    have hb (p : B × B) : (S.bipartiteBelow Inc p).card ≤ D := by
      have hsub : S.bipartiteBelow Inc p ⊆ (univ : Finset A).filter (fun a => R a p.1) := by
        intro a ha
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩
      apply (card_le_card hsub).trans
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hD p.1
    calc
      _ = ∑ a ∈ S, ((lightSet R).bipartiteAbove Inc a).card := by simp only [ha]
      _ = ∑ p ∈ lightSet R, (S.bipartiteBelow Inc p).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
      _ ≤ ∑ _p ∈ lightSet R, D := sum_le_sum (fun p _ => hb p)
      _ = _ := by simp [lightSet_card,Nat.mul_comm]
  calc
    _ ≤ ∑ a ∈ S, 6*(lightAt R a).card := sum_le_sum (fun a _ => root_anchor_bound hf S r hmin a)
    _ = 6*(∑ a ∈ S, (lightAt R a).card) := by rw [mul_sum]
    _ ≤ 6*(D*lightCount R) := Nat.mul_le_mul_left 6 hs
    _ = _ := by ring

#print axioms anchor_witness
#print axioms other_witness_endpoint
#print axioms outside_multiplicity
#print axioms root_anchor_bound
#print axioms total_anchor_bound
end Erdos713ThetaAnchorPacking
