import FormalConjecturesUtil
import Submission.PrimeSupportHall

/-! Eventual shared-prime matchings for affine inputs with a fixed finite prime
support. The support must remain fixed; the unrestricted finite-range matching
and Erdős 371 remain unproved. -/

namespace Erdos371BoundedSupportMatching

open Finset Filter Erdos371PrimeSupportHall Erdos371FixedSupportFavorableCount
open Erdos371FavorableTargetFamilies

def sources (F : ℕ → ℕ) (R : Finset ℕ) (A : ℕ) : Finset ℕ :=
  (Icc 1 A).filter (fun a => 1 < F a ∧ (F a).primeFactors ⊆ R)

def targets (F : ℕ → ℕ) (A : ℕ) : Finset ℕ :=
  (Icc 1 A).filter (fun b => P b < P (F b))

lemma fixed_support_matching_of_capacity (F : ℕ → ℕ) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime)
    (hF : ∀ b, 1 ≤ b → F b ≠ 0)
    (hcap : ∀ r ∈ R, ∀ᶠ A in atTop,
      ((Icc 1 A).filter (fun a => (F a).primeFactors ⊆ R)).card ≤
        ((Icc 1 A).filter (fun b => r ∣ F b ∧ P b < P (F b))).card) :
    ∀ᶠ A in atTop, ∃ f : sources F R A → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ Icc 1 A ∧ P (f a) < P (F (f a)) ∧ 1 < (F a).gcd (F (f a)) := by
  classical
  have h := eventually_matching_fixed_support R (sources F R) (targets F) F
    (fun A a ha => (mem_filter.mp ha).2.2)
    (fun A a ha => by
      have haF := (mem_filter.mp ha).2.1
      obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd (by omega : F a ≠ 1)
      exact ⟨r, Nat.mem_primeFactors.mpr ⟨hr, hd, by omega⟩⟩)
    (fun r hr => by
      filter_upwards [hcap r hr] with A hA
      have hsrc : (sources F R A).card ≤
          ((Icc 1 A).filter (fun a => (F a).primeFactors ⊆ R)).card := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨haA, _, haR⟩ := mem_filter.mp ha
        exact mem_filter.mpr ⟨haA, haR⟩
      have he : ((targets F A).filter (fun b => r ∈ (F b).primeFactors)) =
          (Icc 1 A).filter (fun b => r ∣ F b ∧ P b < P (F b)) := by
        ext b
        constructor
        · intro hb
          obtain ⟨hbT, hbr⟩ := mem_filter.mp hb
          obtain ⟨hbA, hbP⟩ := mem_filter.mp hbT
          exact mem_filter.mpr ⟨hbA, Nat.dvd_of_mem_primeFactors hbr, hbP⟩
        · intro hb
          obtain ⟨hbA, hbr, hbP⟩ := mem_filter.mp hb
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨hbA, hbP⟩,
            Nat.mem_primeFactors.mpr ⟨hR r hr, hbr, hF b (mem_Icc.mp hbA).1⟩⟩
      rw [he]
      exact hsrc.trans hA)
  filter_upwards [h] with A hA
  obtain ⟨f, hf, hmem⟩ := hA
  refine ⟨f, hf, ?_⟩
  intro a
  obtain ⟨haI, haP⟩ := mem_filter.mp (hmem a).1
  refine ⟨haI, haP, ?_⟩
  exact (shared_prime_iff_gcd_gt_one
    (hF a (mem_Icc.mp (mem_filter.mp a.property).1).1)
    (hF (f a) (mem_Icc.mp haI).1)).mp (hmem a).2

/-- The plus affine shared-prime graph admits an eventual matching when the
sources have a fixed finite prime support coprime to the slope. -/
theorem plus_fixed_support_matching {p : ℕ} (hp : 2 ≤ p) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ r.Coprime p) :
    ∀ᶠ A in atTop, ∃ f : sources (fun a => p*a+1) R A → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ Icc 1 A ∧ P (f a) < P (p*f a+1) ∧
        1 < (p*a+1).gcd (p*f a+1) := by
  apply fixed_support_matching_of_capacity (fun a => p*a+1) R (fun r hr => (hR r hr).1)
  · intro b _
    omega
  · intro r hr
    exact plus_fixed_support hp (hR r hr).1 (hR r hr).2 R

/-- The same matching result for minus affine values. The affine value `1`
is excluded from `sources`, since it has no prime divisor to share. -/
theorem minus_fixed_support_matching {p : ℕ} (hp : 2 ≤ p) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ r.Coprime p) :
    ∀ᶠ A in atTop, ∃ f : sources (fun a => p*a-1) R A → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ Icc 1 A ∧ P (f a) < P (p*f a-1) ∧
        1 < (p*a-1).gcd (p*f a-1) := by
  apply fixed_support_matching_of_capacity (fun a => p*a-1) R (fun r hr => (hR r hr).1)
  · intro b hb
    have hpB : 2 ≤ p*b := by nlinarith
    omega
  · intro r hr
    exact minus_fixed_support hp (hR r hr).1 (hR r hr).2 R

end Erdos371BoundedSupportMatching

#print axioms Erdos371BoundedSupportMatching.plus_fixed_support_matching
#print axioms Erdos371BoundedSupportMatching.minus_fixed_support_matching
