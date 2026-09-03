import Submission.Forest93CRT

/-! Arithmetic realization of the93-class forest obstruction. -/
namespace Erdos7Forest93Arithmetic
open scoped BigOperators
open Erdos7Reduction Erdos7Digits Erdos7Compression Erdos7CardinalitySieve
open Erdos7Forest93Certificate Erdos7Forest93Shapes Erdos7Forest93Profile
open Erdos7Forest93ShapeArithmetic Erdos7Forest93Concrete
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option Elab.async false

lemma profile_not_cover {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hclosed : ∀ i d,1 < d → d ∣ m i → ∃ j,m j = d)
    (hpriv : ∀ i,∃ x : ℤ,∀ j,j ≠ i → ¬(m j:ℤ) ∣ x-a j)
    (hP : Finset.univ.biUnion (fun k => (m k).primeFactors) = primeSet)
    (hE : ∀ j,(Finset.univ.lcm m).factorization (primes j) = caps j)
    (hcard : Fintype.card κ ≤ 93) : False := by
  classical
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  obtain ⟨f,hfi,hfm,hfe⟩ := exists_encoding m hm0 hc.1 hP hE
  obtain ⟨t,hprime,hcop,hc'⟩ := composite_residues_coprime_after_normalization m a hc hclosed hpriv
  let a' (k : κ) := a k-t
  obtain ⟨k₉,hk₉⟩ : ∃ k,m k = 9 := by
    obtain ⟨k,hk⟩ := Erdos7No9Certificate.arithmetic_exists_nine m a hc
    exact hclosed k 9 (by decide) hk
  let b : Fin 9 := arithResidue (a' k₉) 0
  have hb : b.val%3 ≠ 0 := by
    intro hh
    have hdiv : (3:ℤ) ∣ a' k₉ := (residueFin_mod_zero 9 3 (by decide) (by decide) (a' k₉)).mp hh
    apply coprime_not_prime_dvd (a' k₉) (m k₉) 3 (by norm_num)
      (hcop k₉ (by rw [hk₉]; norm_num)) (by rw [hk₉]; decide) hdiv
  let T := Finset.univ.filter (fun k => mixed (f k))
  have hT : T.card ≤ 84 := by
    have hh := divisor_closed_mixed_card_bound m hm0 hclosed primes
      (fun j => (prime_properties.2 j).1) prime_properties.1 93 hcard
    have hmax (j : Fin 8) : Finset.univ.sup (fun k => (m k).factorization (primes j)) = caps j :=
      (factorization_finset_lcm Finset.univ m (fun k _ => hm0 k) (primes j)).symm.trans (hE j)
    simp_rw [hmax] at hh
    rw [cap_sum] at hh
    convert hh using 1
    congr 1
    ext k
    simp only [T,Finset.mem_filter,Finset.mem_univ,true_and,mixed,support,exponentSupport,hfe]
  let S : Finset Index := T.image f
  have hS : S.card ≤ 84 := Finset.card_image_le.trans hT
  have hSmixed (i : Index) (hi : i ∈ S) : mixed i := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hk).2
  let r : Index → Space := Function.extend f (fun k => arithResidue (a' k)) (fun _ => arithResidue 0)
  have hr (k : κ) : r (f k) = arithResidue (a' k) := hfi.extend_apply _ _ k
  have hgood (i : Index) (hi : i ∈ S) : good i (r i) := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    rw [hr]
    apply arithResidue_good
    rw [hfm]
    apply hcop k
    rw [← hfm k]
    exact mixed_not_prime (f k) (Finset.mem_filter.mp hk).2
  obtain ⟨x,hx,havoid⟩ := exists_uncovered b hb S hS hSmixed r hgood
  obtain ⟨z,hz⟩ := exists_crt x
  obtain ⟨k,hk⟩ := hc'.2.2 z
  change (m k:ℤ) ∣ z-a' k at hk
  by_cases hmix : mixed (f k)
  · have hmem : f k ∈ S := Finset.mem_image.mpr
      ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmix⟩,rfl⟩
    apply havoid (f k) hmem
    rw [hr]
    apply coverage_box (f k) (a' k) z x hz
    rwa [hfm]
  · rcases nonmixed_classification (f k) hmix with h1 | h9 | hp
    · have hgt := (hc.2.1 k).1
      rw [hfm] at h1
      omega
    · have heq : k = k₉ := hc.1 (by rw [← hfm k,h9,hk₉])
      subst k
      rw [hk₉] at hk
      exact allowed_not_nine (a' k₉) x hx z hz hk
    · obtain ⟨j,hj,_⟩ := prime_classification (f k) hp
      have hka : (m k:ℤ) ∣ a' k := hprime k (by rwa [hfm] at hp)
      have hdz : (m k:ℤ) ∣ z := by simpa only [sub_add_cancel] using dvd_add hk hka
      apply allowed_not_prime b x hx z hz j
      rwa [← hfm k,hj] at hdz

#print axioms profile_not_cover
end Erdos7Forest93Arithmetic
