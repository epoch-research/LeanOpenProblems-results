import FormalConjecturesUtil
import Submission.ThetaHeavyShadow

/-! A matching strengthening of the all-heavy row bound.
This does not prove the density-gap assertion with light pairs, or Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaHeavyMatching
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
variable {A B : Type*} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

abbrev Pair (B : Type*) [Fintype B] := ↥((univ : Finset B).powersetCard 2)

noncomputable def supports (R : A → B → Prop) (p : Pair B) : Finset A :=
  univ.filter (fun a => p.val ⊆ row R a)

lemma pair_card (p : Pair B) : p.val.card = 2 := (mem_powersetCard.mp p.property).2

lemma mem_supports (R : A → B → Prop) (p : Pair B) (a : A) :
    a ∈ supports R p ↔ p.val ⊆ row R a := by simp [supports]

lemma supports_card {R : A → B → Prop} (hh : Heavy R) (p : Pair B) :
    3 ≤ (supports R p).card := by
  obtain ⟨x,y,hxy,hp⟩ := card_eq_two.mp (pair_card p)
  have he : supports R p = univ.filter (fun a => R a x ∧ R a y) := by
    ext a
    simp [mem_supports,hp,Finset.insert_subset_iff,Finset.singleton_subset_iff,mem_row]
  rw [he]
  simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh x y hxy

omit [Fintype A] in
lemma load_le (R : A → B → Prop) (S : Finset (Pair B)) (a : A) :
    (S.filter (fun p => p.val ⊆ row R a)).card ≤ (row R a).card.choose 2 := by
  rw [← card_powersetCard]
  apply card_le_card_of_injOn (fun p : Pair B => p.val)
  · intro p hp
    exact mem_powersetCard.mpr ⟨(mem_filter.mp hp).2,pair_card p⟩
  · intro p hp q hq he
    exact Subtype.ext he

/-- An arbitrary family of pairs satisfies Hall's inequality. The global
all-heavy hypothesis is retained; it is not inferred for row restrictions. -/
theorem hall {R : A → B → Prop} (hf : ¬ HasTheta R) (hh : Heavy R)
    (S : Finset (Pair B)) : S.card ≤ (S.biUnion (supports R)).card := by
  let N := S.biUnion (supports R)
  let H := N.filter (fun a => 4 ≤ (row R a).card)
  let L := N.filter (fun a => (row R a).card ≤ 2)
  let load : A → ℕ := fun a => (S.filter (fun p => p.val ⊆ row R a)).card
  have hlow : (∑ a ∈ H, load a) ≤ L.card := by
    let T := (a : H) × ↥(S.filter (fun p => p.val ⊆ row R a.val))
    have hex (z : T) : ∃ b : L, row R b.val = z.2.val.val := by
      have ha : 4 ≤ (row R z.1.val).card := (mem_filter.mp z.1.property).2
      have hp := mem_filter.mp z.2.property
      obtain ⟨b,hb,he⟩ := pair_has_low_row hf hh ha z.2.val.val (pair_card _) hp.2
      have hbN : b ∈ N := mem_biUnion.mpr ⟨z.2.val,hp.1,
        (mem_supports R _ b).mpr (by rw [he])⟩
      exact ⟨⟨b,mem_filter.mpr ⟨hbN,hb⟩⟩,he⟩
    choose f hf' using hex
    have hi : Function.Injective f := by
      rintro ⟨a,p⟩ ⟨b,q⟩ he
      have hpq : p.val.val = q.val.val :=
        (hf' ⟨a,p⟩).symm.trans ((congrArg (fun z : L => row R z.val) he).trans (hf' ⟨b,q⟩))
      have hab : a.val = b.val := high_pair_unique hf hh
        (mem_filter.mp a.property).2 (mem_filter.mp b.property).2
        p.val.val (pair_card _) (mem_filter.mp p.property).2
        (hpq.symm ▸ (mem_filter.mp q.property).2)
      have hab' : a = b := Subtype.ext hab
      subst b
      have hpq' : p = q := Subtype.ext (Subtype.ext hpq)
      subst q
      rfl
    have hc := Fintype.card_le_of_injective f hi
    have hT : Fintype.card T = ∑ a ∈ H, load a := by
      simp only [T,Fintype.card_sigma,Fintype.card_coe,load]
      exact sum_coe_sort H (fun a => (S.filter (fun p => p.val ⊆ row R a)).card)
    rw [hT,Fintype.card_coe] at hc
    exact hc
  have hpoint (a : A) : load a + 2*(if (row R a).card ≤ 2 then 1 else 0) ≤
      (if 4 ≤ (row R a).card then load a else 0)+3 := by
    by_cases hhi : 4 ≤ (row R a).card
    · have hlo : ¬ (row R a).card ≤ 2 := by omega
      simp [hhi,hlo]
    · have hb := load_le R S a
      change load a ≤ (row R a).card.choose 2 at hb
      have hs : (row R a).card ≤ 3 := by omega
      interval_cases he : (row R a).card <;> norm_num [he] at hb ⊢ <;> omega
  have hs := sum_le_sum (s := N) (fun a _ => hpoint a)
  have hL : (∑ a ∈ N, if (row R a).card ≤ 2 then 1 else 0) = L.card := by
    simp only [L,card_eq_sum_ones,sum_filter]
  have hH : (∑ a ∈ N, if 4 ≤ (row R a).card then load a else 0) = ∑ a ∈ H, load a := by
    simp only [H,sum_filter]
  simp only [sum_add_distrib,← mul_sum,sum_const,Nat.nsmul_eq_mul,hL,hH] at hs
  have hsum : ∑ a ∈ N, load a = ∑ p ∈ S, (supports R p).card := by
    let I : A → Pair B → Prop := fun a p => p.val ⊆ row R a
    have ha (a : A) : (S.bipartiteAbove I a).card = load a := rfl
    have hp (p : Pair B) (hp : p ∈ S) : N.bipartiteBelow I p = supports R p := by
      ext a
      simp only [bipartiteBelow,mem_filter,mem_supports,I]
      exact ⟨fun h => h.2,fun h => ⟨mem_biUnion.mpr ⟨p,hp,(mem_supports _ _ _).mpr h⟩,h⟩⟩
    calc
      _ = ∑ a ∈ N, (S.bipartiteAbove I a).card := rfl
      _ = ∑ p ∈ S, (N.bipartiteBelow I p).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
      _ = _ := sum_congr rfl (fun p hp' => by rw [hp p hp'])
  have hlower := sum_le_sum (s := S) (fun p _ => supports_card hh p)
  simp only [sum_const,Nat.nsmul_eq_mul] at hlower
  rw [hsum] at hs
  change S.card ≤ N.card
  omega

/-- A distinct supporting row can be assigned to every unordered pair. -/
theorem exists_matching {R : A → B → Prop} (hf : ¬ HasTheta R) (hh : Heavy R) :
    ∃ f : Pair B → A, Function.Injective f ∧ ∀ p, p.val ⊆ row R (f p) := by
  obtain ⟨f,hi,hf'⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' (supports R)).mp (hall hf hh)
  exact ⟨f,hi,fun p => (mem_supports R p (f p)).mp (hf' p)⟩

#print axioms hall
#print axioms exists_matching
end Erdos713ThetaHeavyMatching
