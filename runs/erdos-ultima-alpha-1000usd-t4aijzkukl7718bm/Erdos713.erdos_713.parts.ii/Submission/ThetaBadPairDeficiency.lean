import FormalConjecturesUtil
import Submission.ThetaZeroDiamondMatching

/-! Hall deficiency is bounded by the number of heavy pairs with a large
supporting row and no exact-pair row. No global bound on those exceptional
pairs is proved, and the density gap and Erdős 713 remain unresolved. -/
open Finset
open scoped Classical
namespace Erdos713ThetaBadPairDeficiency
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaRigidHeavyMatching
open Erdos713ThetaZeroDiamondMatching
variable {A B : Type*} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

def Bad (R : A → B → Prop) (p : HeavyPair R) : Prop :=
  (∃ a ∈ supports R p.val, 4 ≤ (row R a).card) ∧ ¬ ∃ b, row R b = p.val.val

abbrev BadPair (R : A → B → Prop) := {p : HeavyPair R // Bad R p}

/-- The exact-large-row hypothesis need only hold on the selected family. -/
theorem hall_of_exact_large_on {R : A → B → Prop} (S : Finset (HeavyPair R))
    (hlarge : ∀ p ∈ S,
      (∃ a ∈ supports R p.val, 4 ≤ (row R a).card) → ∃ b, row R b = p.val.val) : S.card ≤ (S.biUnion (fun p => supports R p.val)).card := by
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
      exact hnexact (hlarge p hpS ⟨a,(mem_supports R _ _).mpr ha,hh⟩)
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

/-- No theta or rigidity hypothesis is needed for this abstract deficiency
estimate. Those conditions would be used to control the exceptional set. -/
theorem hall_deficiency (R : A → B → Prop) (S : Finset (HeavyPair R)) :
    S.card ≤ (S.biUnion (fun p => supports R p.val)).card + (S.filter (Bad R)).card := by
  let T := S.filter (fun p => ¬ Bad R p)
  have hT : T.card ≤ (T.biUnion (fun p => supports R p.val)).card := by
    apply hall_of_exact_large_on
    intro p hp hl
    by_contra he
    exact (mem_filter.mp hp).2 ⟨hl,he⟩
  have hN : T.biUnion (fun p => supports R p.val) ⊆
      S.biUnion (fun p => supports R p.val) := by
    intro a ha
    obtain ⟨p,hp,hap⟩ := mem_biUnion.mp ha
    exact mem_biUnion.mpr ⟨p,(mem_filter.mp hp).1,hap⟩
  have hTbound := hT.trans (card_le_card hN)
  have hsplit := card_filter_add_card_filter_not (s := S) (p := Bad R)
  change (S.filter (Bad R)).card + T.card = S.card at hsplit
  omega

/-- A concrete universal cardinal bound, still requiring an independent
estimate on the bad-pair term before it yields a density gap. -/
theorem heavy_card_le_rows_add_bad (R : A → B → Prop) :
    Nat.card (HeavyPair R) ≤ Nat.card A + Nat.card (BadPair R) := by
  have hh := hall_deficiency R univ
  have hn := card_le_univ ((univ : Finset (HeavyPair R)).biUnion (fun p => supports R p.val))
  have hb : ((univ : Finset (HeavyPair R)).filter (Bad R)).card = Nat.card (BadPair R) := by
    simp only [BadPair,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [card_univ,hb] at hh
  simpa only [Nat.card_eq_fintype_card] using hh.trans (Nat.add_le_add_right hn _)

/-- The older induced-zero-diamond hypothesis kills the new exceptional term,
but the unrestricted global zero-pair estimate is not established here. -/
theorem no_bad_of_noZeroDiamond {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroDiamond R) (p : HeavyPair R) : ¬ Bad R p := by
  rintro ⟨hl,he⟩
  exact he (large_witness hf hr hz p hl)

#print axioms hall_of_exact_large_on
#print axioms hall_deficiency
#print axioms heavy_card_le_rows_add_bad
#print axioms no_bad_of_noZeroDiamond
end Erdos713ThetaBadPairDeficiency
