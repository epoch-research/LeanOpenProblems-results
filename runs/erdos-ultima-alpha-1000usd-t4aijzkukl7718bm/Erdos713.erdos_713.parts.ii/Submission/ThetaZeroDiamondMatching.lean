import FormalConjecturesUtil
import Submission.ThetaRigidHeavyMatching

/-! Conditional heavy-pair matching under induced zero-diamond exclusion.
The extra exclusion is not proved for arbitrary extremal hosts, so these
lemmas do not settle the theta density gap or Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaZeroDiamondMatching
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaAnchorPacking Erdos713ThetaPrivatePetals
open Erdos713ThetaDisjointSupports Erdos713ThetaRigidBookMass
open Erdos713ThetaRigidHeavyMatching
variable {A B : Type*} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

/-- The graph of zero-codegree pairs has no induced diamond. The missing
edge of the diamond is the positive-codegree pair x,y. -/
def NoZeroDiamond (R : A → B → Prop) : Prop :=
  ∀ x y z w : B, x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
    codegree R x y ≠ 0 → codegree R x z = 0 → codegree R x w = 0 →
    codegree R y z = 0 → codegree R y w = 0 → codegree R z w = 0 → False

omit [Fintype A] [Fintype B] in
lemma noZeroDiamond_of_noZeroTriangle {R : A → B → Prop}
    (hz : Erdos713ThetaZeroTriangle.NoZeroTriangle R) : NoZeroDiamond R := by
  intro x y z w _hxy hxz hxw _hyz _hyw hzw _hpos hxz0 hxw0 _hyz0 _hyw0 hzw0
  exact hz x z w hxz hxw hzw hxz0 hxw0 hzw0


omit [Fintype B] in
lemma ne_of_zero_of_inc {R : A → B → Prop} {x y : B}
    (hz : codegree R x y = 0) {a : A} (hx : R a x) : x ≠ y := by
  intro he
  exact not_common_of_codegree_zero hz a ⟨hx,he ▸ hx⟩

/-- A heavy pair with a large supporting row has an exact-pair row. -/
theorem exact_pair_of_large {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroDiamond R) {x y : B} (hxy : x ≠ y)
    (hh : 3 ≤ codegree R x y) {a : A} (hax : R a x) (hay : R a y)
    (hlarge : 4 ≤ (row R a).card) : ∃ b : A, row R b = {x,y} := by
  by_contra h
  let T := commonRows R univ (x,y)
  have ha : a ∈ T := mem_filter.mpr ⟨mem_univ _,hax,hay⟩
  have hT : 3 ≤ T.card := by
    simpa only [T,commonRows,mem_filter,mem_univ,true_and,codegree,
      Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  have hmin (b : A) (hb : b ∈ T) : 3 ≤ (row R b).card := by
    have hb' : R b x ∧ R b y := (mem_filter.mp hb).2
    have hs : ({x,y} : Finset B) ⊆ row R b := by
      simp only [insert_subset_iff,singleton_subset_iff,mem_row]
      exact hb'
    by_contra hc
    have he : row R b = {x,y} :=
      (eq_of_subset_of_card_le hs (by simp [hxy]; omega)).symm
    exact h ⟨b,he⟩
  have hrest : 1 < (T.erase a).card := by
    rw [card_erase_of_mem ha]
    omega
  obtain ⟨b,hb,c,hc,hbc⟩ := one_lt_card.mp hrest
  have hba : b ≠ a := (mem_erase.mp hb).1
  have hca : c ≠ a := (mem_erase.mp hc).1
  have hbT : b ∈ T := (mem_erase.mp hb).2
  have hcT : c ∈ T := (mem_erase.mp hc).2
  have hpa : 1 < (privatePetal R univ (x,y) a).card := by
    rw [private_card hr univ hxy ha]
    omega
  obtain ⟨u,hu,v,hv,huv⟩ := one_lt_card.mp hpa
  have hpb : (privatePetal R univ (x,y) b).Nonempty := by
    rw [← card_pos,private_card hr univ hxy hbT]
    have hd := hmin b hbT
    omega
  have hpc : (privatePetal R univ (x,y) c).Nonempty := by
    rw [← card_pos,private_card hr univ hxy hcT]
    have hd := hmin c hcT
    omega
  obtain ⟨z,hz'⟩ := hpb
  obtain ⟨w,hw⟩ := hpc
  have huz := private_cross_zero hf univ hxy ha hbT hba.symm hu hz'
  have huw := private_cross_zero hf univ hxy ha hcT hca.symm hu hw
  have hvz := private_cross_zero hf univ hxy ha hbT hba.symm hv hz'
  have hvw := private_cross_zero hf univ hxy ha hcT hca.symm hv hw
  have hzw := private_cross_zero hf univ hxy hbT hcT hbc hz' hw
  have hua : R a u := (mem_privatePetal R univ (x,y) a u).mp hu |>.1
  have hva : R a v := (mem_privatePetal R univ (x,y) a v).mp hv |>.1
  have hzb : R b z := (mem_privatePetal R univ (x,y) b z).mp hz' |>.1
  exact hz u v z w huv (ne_of_zero_of_inc huz hua) (ne_of_zero_of_inc huw hua)
    (ne_of_zero_of_inc hvz hva) (ne_of_zero_of_inc hvw hva) (ne_of_zero_of_inc hzw hzb)
    (fun he => not_common_of_codegree_zero he a ⟨hua,hva⟩) huz huw hvz hvw hzw

/-- A general Hall criterion: only pairs with large supporting rows need
an exact-pair witness. All other rows have pair capacity at most three. -/
theorem hall_of_exact_large {R : A → B → Prop}
    (hlarge : ∀ p : HeavyPair R,
      (∃ a ∈ supports R p.val, 4 ≤ (row R a).card) → ∃ b, row R b = p.val.val)
    (S : Finset (HeavyPair R)) : S.card ≤ (S.biUnion (fun p => supports R p.val)).card := by
  let N := S.biUnion (fun p => supports R p.val)
  let T := S.filter (fun p => ∃ a, row R a = p.val.val)
  let U := S \ T
  let E := N.filter (fun a => (row R a).card ≤ 2)
  let M := N.filter (fun a => (row R a).card = 3)
  have hTsub : T ⊆ S := filter_subset _ _
  have hUsub : U ⊆ S := sdiff_subset
  have hTcard : T.card ≤ E.card := by
    have hex (p : T) : ∃ b : E, row R b.val = p.val.val.val := by
      obtain ⟨b,hb⟩ := (mem_filter.mp p.property).2
      have hbN : b ∈ N := mem_biUnion.mpr ⟨p.val,(mem_filter.mp p.property).1,
        (mem_supports R _ _).mpr (by rw [hb])⟩
      have hbE : b ∈ E := mem_filter.mpr ⟨hbN,by rw [hb,pair_card]⟩
      exact ⟨⟨b,hbE⟩,hb⟩
    choose f hf using hex
    have hi : Function.Injective f := by
      intro p q he
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact (hf p).symm.trans ((congrArg (fun b : E => row R b.val) he).trans (hf q))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi
  have hdeg (p : HeavyPair R) (hp : p ∈ U) (a : A)
      (ha : p.val.val ⊆ row R a) : (row R a).card = 3 := by
    have hpS := hUsub hp
    have hpT : p ∉ T := (mem_sdiff.mp hp).2
    have hnexact : ¬ ∃ b, row R b = p.val.val := by
      intro he
      exact hpT (mem_filter.mpr ⟨hpS,he⟩)
    have hnotlarge : ¬ 4 ≤ (row R a).card := by
      intro hh
      exact hnexact (hlarge p ⟨a,(mem_supports R _ _).mpr ha,hh⟩)
    have hnsmall : ¬ (row R a).card ≤ 2 := by
      intro hs
      exact hnexact ⟨a,(eq_of_subset_of_card_le ha (by rw [pair_card]; exact hs)).symm⟩
    omega
  let load : A → ℕ := fun a => (U.filter (fun p => p.val.val ⊆ row R a)).card
  have hcap (a : A) : load a ≤ (row R a).card.choose 2 := by
    rw [← card_powersetCard]
    apply card_le_card_of_injOn (fun p : HeavyPair R => p.val.val)
    · intro p hp
      exact mem_powersetCard.mpr ⟨(mem_filter.mp hp).2,pair_card p.val⟩
    · intro p hp q hq he
      exact Subtype.ext (Subtype.ext he)
  have hpoint (a : A) : load a ≤ if (row R a).card = 3 then 3 else 0 := by
    by_cases hd : (row R a).card = 3
    · simpa only [hd,if_pos rfl,show (3 : ℕ).choose 2 = 3 from by decide] using hcap a
    · rw [if_neg hd]
      apply Nat.le_zero.mpr
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hd (hdeg p (mem_filter.mp hp).1 a (mem_filter.mp hp).2)
  have hsum : ∑ a ∈ N, load a = ∑ p ∈ U, (supports R p.val).card := by
    let I : A → HeavyPair R → Prop := fun a p => p.val.val ⊆ row R a
    have hp (p : HeavyPair R) (hpU : p ∈ U) : N.bipartiteBelow I p = supports R p.val := by
      ext a
      simp only [bipartiteBelow,mem_filter,mem_supports,I]
      exact ⟨fun h => h.2,fun h => ⟨mem_biUnion.mpr
        ⟨p,hUsub hpU,(mem_supports R _ _).mpr h⟩,h⟩⟩
    calc
      _ = ∑ a ∈ N, (U.bipartiteAbove I a).card := rfl
      _ = ∑ p ∈ U, (N.bipartiteBelow I p).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
      _ = _ := sum_congr rfl (fun p hp' => by rw [hp p hp'])
  have hupper := sum_le_sum (s := N) (fun a _ => hpoint a)
  have hMsum : (∑ a ∈ N, if (row R a).card = 3 then 3 else 0) = M.card*3 := by
    rw [← sum_filter]
    simp only [M,sum_const,Nat.nsmul_eq_mul]
  rw [hsum,hMsum] at hupper
  have hlower := sum_le_sum (s := U) (fun p _ => p.property)
  simp only [sum_const,Nat.nsmul_eq_mul] at hlower
  have hUcard : U.card ≤ M.card := by omega
  have hdis : Disjoint E M := by
    apply disjoint_left.mpr
    intro a ha hb
    have hh := (mem_filter.mp ha).2
    have he := (mem_filter.mp hb).2
    omega
  have hEM : E.card+M.card ≤ N.card := by
    rw [← card_union_of_disjoint hdis]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have hsplit : U.card+T.card = S.card := card_sdiff_add_card_eq_card hTsub
  change S.card ≤ N.card
  omega

theorem large_witness {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroDiamond R) (p : HeavyPair R)
    (hp : ∃ a ∈ supports R p.val, 4 ≤ (row R a).card) :
    ∃ b, row R b = p.val.val := by
  obtain ⟨a,ha,hlarge⟩ := hp
  obtain ⟨x,y,hxy,he⟩ := card_eq_two.mp (pair_card p.val)
  have heq : supports R p.val = univ.filter (fun a => R a x ∧ R a y) := by
    ext a
    simp [mem_supports,he,insert_subset_iff,singleton_subset_iff,mem_row]
  have hh : 3 ≤ codegree R x y := by
    have h := p.property
    rw [heq] at h
    simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using h
  rw [heq] at ha
  obtain ⟨b,hb⟩ := exact_pair_of_large hf hr hz hxy hh
    (mem_filter.mp ha).2.1 (mem_filter.mp ha).2.2 hlarge
  exact ⟨b,hb.trans he.symm⟩

/-- Heavy unordered pairs inject into supporting rows under the additional
induced zero-diamond exclusion. The assigned rows need not have degree two. -/
theorem exists_matching {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroDiamond R) :
    ∃ f : HeavyPair R → A, Function.Injective f ∧
      ∀ p, p.val.val ⊆ row R (f p) := by
  obtain ⟨f,hi,hf'⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun p : HeavyPair R => supports R p.val)).mp
      (hall_of_exact_large (large_witness hf hr hz))
  exact ⟨f,hi,fun p => (mem_supports R _ _).mp (hf' p)⟩

theorem heavy_pair_card_le {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroDiamond R) : Nat.card (HeavyPair R) ≤ Nat.card A := by
  obtain ⟨f,hi,_⟩ := exists_matching hf hr hz
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hi

#print axioms exact_pair_of_large
#print axioms hall_of_exact_large
#print axioms exists_matching
#print axioms heavy_pair_card_le
end Erdos713ThetaZeroDiamondMatching
