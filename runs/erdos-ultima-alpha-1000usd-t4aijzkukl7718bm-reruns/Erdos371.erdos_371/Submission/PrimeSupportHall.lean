import FormalConjecturesUtil
import Submission.FixedSupportFavorableCount

/-! Exact compression of a shared-prime matching problem to finite support
inequalities, and eventual matchings for a fixed bounded support. No uniform
bound over growing supports is established here. -/

namespace Erdos371PrimeSupportHall

open Finset Filter

/-- Hall's condition for an intersection graph can be indexed by subsets of
the union of source supports, instead of subsets of the source vertices. -/
theorem support_hall_iff {ι β γ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (B : Finset β) (U : ι → Finset γ) (V : β → Finset γ) :
    (∀ R : Finset γ, R ⊆ univ.biUnion U →
      (univ.filter (fun i => U i ⊆ R)).card ≤
        (B.filter (fun j => (R ∩ V j).Nonempty)).card) ↔
      ∃ f : ι → β, Function.Injective f ∧
        ∀ i, f i ∈ B ∧ (U i ∩ V (f i)).Nonempty := by
  constructor
  · intro h
    let t : ι → Finset β := fun i => B.filter (fun j => (U i ∩ V j).Nonempty)
    have ht : ∀ S : Finset ι, S.card ≤ (S.biUnion t).card := by
      intro S
      let R := S.biUnion U
      have hR : R ⊆ univ.biUnion U := by
        intro r hr
        obtain ⟨i, hi, hir⟩ := mem_biUnion.mp hr
        exact mem_biUnion.mpr ⟨i, mem_univ i, hir⟩
      have hS : S ⊆ univ.filter (fun i => U i ⊆ R) := by
        intro i hi
        exact mem_filter.mpr ⟨mem_univ i, fun r hr => mem_biUnion.mpr ⟨i, hi, hr⟩⟩
      have he : B.filter (fun j => (R ∩ V j).Nonempty) = S.biUnion t := by
        ext j
        simp only [mem_filter, nonempty_def, mem_inter, mem_biUnion, R, t]
        aesop
      exact (Finset.card_le_card hS).trans ((h R hR).trans_eq (congrArg card he))
    obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp ht
    exact ⟨f, hf, fun i => mem_filter.mp (hmem i)⟩
  · rintro ⟨f, hf, hmem⟩ R _
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      obtain ⟨_, hiR⟩ := mem_filter.mp hi
      obtain ⟨r, hr⟩ := (hmem i).2
      obtain ⟨hri, hrv⟩ := mem_inter.mp hr
      exact mem_filter.mpr ⟨(hmem i).1, ⟨r, mem_inter.mpr ⟨hiR hri, hrv⟩⟩⟩
    · exact hf.injOn

lemma shared_prime_iff_gcd_gt_one {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.primeFactors ∩ b.primeFactors).Nonempty ↔ 1 < a.gcd b := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hra, hrb⟩ := mem_inter.mp hr
    obtain ⟨hprime, hdiva, _⟩ := Nat.mem_primeFactors.mp hra
    have hdivb := Nat.dvd_of_mem_primeFactors hrb
    exact hprime.one_lt.trans_le (Nat.le_of_dvd
      (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)) (Nat.dvd_gcd hdiva hdivb))
  · intro h
    obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd (by omega : a.gcd b ≠ 1)
    exact ⟨r, mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr, hd.trans (Nat.gcd_dvd_left _ _), ha⟩,
      Nat.mem_primeFactors.mpr ⟨hr, hd.trans (Nat.gcd_dvd_right _ _), hb⟩⟩⟩

/-- If each relevant prime has enough targets to accommodate the entire source
set, Hall's condition follows. This is stronger than the support condition. -/
lemma matching_of_single_prime_capacity {ι β γ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (B : Finset β) (U : ι → Finset γ) (V : β → Finset γ)
    (hne : ∀ i, (U i).Nonempty)
    (hcap : ∀ r ∈ univ.biUnion U,
      Fintype.card ι ≤ (B.filter (fun j => r ∈ V j)).card) :
    ∃ f : ι → β, Function.Injective f ∧
      ∀ i, f i ∈ B ∧ (U i ∩ V (f i)).Nonempty := by
  apply (support_hall_iff B U V).mp
  intro R hR
  by_cases he : (univ.filter (fun i => U i ⊆ R)).Nonempty
  · obtain ⟨i, hi⟩ := he
    obtain ⟨r, hr⟩ := hne i
    have hrR := (mem_filter.mp hi).2 hr
    have hrU : r ∈ univ.biUnion U := mem_biUnion.mpr ⟨i, mem_univ i, hr⟩
    have hsub : B.filter (fun j => r ∈ V j) ⊆ B.filter (fun j => (R ∩ V j).Nonempty) := by
      intro j hj
      obtain ⟨hjB, hjr⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨hjB, ⟨r, mem_inter.mpr ⟨hrR, hjr⟩⟩⟩
    exact (Finset.card_le_univ _).trans ((hcap r hrU).trans (Finset.card_le_card hsub))
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, card_empty]
    omega

/-- A fixed finite prime support permits one common threshold for the capacity
bounds at all primes in that support. The threshold may depend on the support. -/
theorem eventually_matching_fixed_support
    (R : Finset ℕ) (S G : ℕ → Finset ℕ) (F : ℕ → ℕ)
    (hR : ∀ A a, a ∈ S A → (F a).primeFactors ⊆ R)
    (hne : ∀ A a, a ∈ S A → (F a).primeFactors.Nonempty)
    (hcap : ∀ r ∈ R, ∀ᶠ A in atTop,
      (S A).card ≤ ((G A).filter (fun b => r ∈ (F b).primeFactors)).card) :
    ∀ᶠ A in atTop, ∃ f : S A → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ G A ∧ ((F a).primeFactors ∩ (F (f a)).primeFactors).Nonempty := by
  classical
  have h := (Filter.eventually_all_finset R).mpr hcap
  filter_upwards [h] with A hA
  apply matching_of_single_prime_capacity (G A)
    (fun a : S A => (F a).primeFactors) (fun b => (F b).primeFactors)
  · intro a
    exact hne A a a.property
  · intro r hr
    obtain ⟨a, _, hra⟩ := mem_biUnion.mp hr
    simpa only [Fintype.card_coe] using hA r (hR A a a.property hra)

end Erdos371PrimeSupportHall

#print axioms Erdos371PrimeSupportHall.support_hall_iff
#print axioms Erdos371PrimeSupportHall.eventually_matching_fixed_support
