import Submission.CofactorChain

/-! Cofactor-chain capacity after several coordinate groups are merged.
The correct bound is a sum of complementary capacities, not preservation of
the original scalar chain cap under compression. -/
namespace Erdos7GroupedCofactorCapacity
open scoped BigOperators
open Erdos7CofactorChain
set_option maxHeartbeats 1500000

/-- Group a projected family by its complementary modulus. Each group has
its own residue injection, so its capacity can be added before normalization. -/
theorem active_card_le_sum_capacity {κ : Type*} (K : Finset κ)
    (q n : κ → ℕ) (a : κ → ℤ)
    (hq : ∀ i ∈ K, 0 < q i) (hcop : ∀ i ∈ K, Nat.Coprime (q i) (n i))
    (hchain : ∀ i ∈ K, ∀ j ∈ K, q i=q j → n i ∣ n j ∨ n j ∣ n i)
    (hsep : ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
      q i*n i ∣ q j*n j → ¬ ((q i*n i : ℕ) : ℤ) ∣ a j-a i)
    (x : ℤ) :
    (K.filter (fun i => (n i : ℤ) ∣ x-a i)).card ≤ ∑ r ∈ K.image q, r := by
  classical
  let A := K.filter (fun i => (n i : ℤ) ∣ x-a i)
  have hgroup (r : ℕ) (hr : r ∈ K.image q) :
      (A.filter (fun i => q i=r)).card ≤ r := by
    obtain ⟨k, hk, hkr⟩ := Finset.mem_image.mp hr
    have hr0 : 0 < r := hkr ▸ hq k hk
    let S := A.filter (fun i => q i=r)
    have hmem (i : S) : i.val ∈ K :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).1
    have heq (i : S) : q i.val=r := (Finset.mem_filter.mp i.property).2
    have h := card_le r hr0 (fun i : S => n i.val) (fun i : S => a i.val)
      (fun i => by simpa only [heq i] using hcop i.val (hmem i))
      (fun i j => hchain i.val (hmem i) j.val (hmem j) ((heq i).trans (heq j).symm))
      (by
        intro i j hij hd
        have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
        have hprod : q i.val*n i.val ∣ q j.val*n j.val := by
          rw [heq i, heq j]
          exact Nat.mul_dvd_mul_left r hd
        have hh := hsep i.val (hmem i) j.val (hmem j) hij' hprod
        simpa only [heq i] using hh)
      x (fun i => (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).2)
    simpa only [Fintype.card_coe] using h
  change A.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise (s := A) (t := K.image q)
    (f := q) (by
      intro i hi
      exact Finset.mem_image_of_mem q (Finset.mem_filter.mp hi).1)]
  exact Finset.sum_le_sum (fun r hr => hgroup r hr)

/-- Specialization to a single remaining prime coordinate. Its exponent
cofactors form a chain, even if several deleted-coordinate groups were merged. -/
theorem prime_power_active_capacity {κ : Type*} (K : Finset κ)
    (q e : κ → ℕ) (a : κ → ℤ) (p : ℕ)
    (hq : ∀ i ∈ K, 0 < q i) (hcop : ∀ i ∈ K, Nat.Coprime (q i) p)
    (hsep : ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
      q i*p^(e i) ∣ q j*p^(e j) → ¬ ((q i*p^(e i) : ℕ) : ℤ) ∣ a j-a i)
    (x : ℤ) :
    (K.filter (fun i => ((p^(e i) : ℕ) : ℤ) ∣ x-a i)).card ≤
      ∑ r ∈ K.image q, r := by
  apply active_card_le_sum_capacity K q (fun i => p^(e i)) a hq
    (fun i hi => (hcop i hi).pow_right _) ?_ hsep x
  intro i hi j hj _
  rcases le_total (e i) (e j) with h | h
  · exact Or.inl (pow_dvd_pow p h)
  · exact Or.inr (pow_dvd_pow p h)

/-- Merging exponent levels 0,...,a divides by a+1 after summing the actual
complementary capacities. This is not the old cap multiplied merely by a+1. -/
lemma normalized_capacity_step (Q M p : ℚ) (a : ℕ) :
    (∑ b ∈ Finset.range (a+1), Q*p^b) / ((a+1 : ℕ)*M) =
      (Q/M) * ((∑ b ∈ Finset.range (a+1), p^b)/(a+1 : ℕ)) := by
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms active_card_le_sum_capacity
#print axioms prime_power_active_capacity
end Erdos7GroupedCofactorCapacity
