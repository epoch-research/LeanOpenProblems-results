import Submission.ShiftedFullFiberCapacity
import Submission.FiniteTailCapacity

/-!
A two-thirds ceiling for whole square-Sidon unions of arbitrarily shifted,
unequal full fibers over a prime-power modulus.  Arbitrary partial fibers
are not covered.  The height bound is required to be at least the modulus.
-/
namespace Erdos773.UnequalShiftedFullFibers

open Finset MatchedResidueLifting

set_option maxHeartbeats 2000000

def roots (q : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ) : Finset ℕ :=
  R.biUnion (fun r => (range (lengths r + 1)).image (fun i => q * (starts r + i) + r))

lemma roots_card (q : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hq : 0 < q) (hR : ∀ r ∈ R, r < q) :
    (roots q R starts lengths).card = ∑ r ∈ R, (lengths r + 1) := by
  classical
  rw [roots, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro i j hij
    have hh := Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel hij)
    omega
  · intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro x hxr hxs
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hxr
    obtain ⟨j, hj, he'⟩ := Finset.mem_image.mp hxs
    have hh := congrArg (fun n : ℕ => n % q) (he.trans he'.symm)
    have hres : r = s := by
      simpa only [Nat.add_mod, Nat.mul_mod_right, zero_add,
        Nat.mod_eq_of_lt (hR r hr), Nat.mod_eq_of_lt (hR s hs)] using hh
    exact hrs hres

lemma common_subset {q t : ℕ} {R S : Finset ℕ} {starts lengths : ℕ → ℕ}
    (hSR : S ⊆ R) (ht : ∀ r ∈ S, t ≤ lengths r) :
    ShiftedFullFiberCapacity.roots q t S starts ⊆ roots q R starts lengths := by
  intro x hx
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hr, hi⟩ := Finset.mem_product.mp hri
  dsimp only at hr hi ⊢
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hSR hr, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr ?_, rfl⟩⟩
  have hindex := Finset.mem_range.mp hi
  have hlen := ht r hr
  omega

/-- All upper length tails satisfy the common-length geometric capacity. -/
theorem length_tail (p k N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hp : p.Prime) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + lengths r) + r ≤ N)
    (hS : IsSidon (((roots (p ^ k) R starts lengths).image (fun n => n ^ 2)) : Set ℕ))
    (t : ℕ) :
    (R.filter (fun r => t ≤ lengths r)).card * t ^ 2 ≤ 2400 * N := by
  let S := R.filter (fun r => t ≤ lengths r)
  have hSR : S ⊆ R := Finset.filter_subset _ _
  have hlen : ∀ r ∈ S, t ≤ lengths r := fun r hr => (Finset.mem_filter.mp hr).2
  apply ShiftedFullFiberCapacity.prime_power_capacity p k N t S starts hp
    (fun r hr => hR r (hSR hr))
  · intro r hr
    have hh := Nat.mul_le_mul_left (p ^ k) (Nat.add_le_add_left (hlen r hr) (starts r))
    exact (Nat.add_le_add_right hh r).trans (hheight r (hSR hr))
  · exact Set.IsSidon.subset hS (Finset.image_subset_image (common_subset hSR hlen))

/-- The finite weak-square-tail inequality removes the potential logarithmic loss. -/
theorem mass_square_bound (p k N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hp : p.Prime) (hqN : p ^ k ≤ N) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + lengths r) + r ≤ N)
    (hS : IsSidon (((roots (p ^ k) R starts lengths).image (fun n => n ^ 2)) : Set ℕ)) :
    (roots (p ^ k) R starts lengths).card ^ 2 ≤ 38400 * N * R.card := by
  have hRc := (PrimePowerFullFiberBound.labels_card (p ^ k) R hR).trans hqN
  have hA : (R.card : ℝ) ≤ 2400 * N := by
    have hh : (R.card : ℝ) ≤ N := by exact_mod_cast hRc
    nlinarith only [hh, show (0 : ℝ) ≤ N by positivity]
  have ht (t : ℕ) (_ht : 0 < t) :
      ((R.filter (fun r => t ≤ lengths r)).card : ℝ) * (t : ℝ) ^ 2 ≤ 2400 * N := by
    exact_mod_cast length_tail p k N R starts lengths hp hR hheight hS t
  have hh := FiniteTailCapacity.mass_square_bound R lengths (2400 * N) hA ht
  have hh' : ((∑ r ∈ R, (lengths r + 1) : ℕ) : ℝ) ^ 2 ≤ 38400 * N * R.card := by
    push_cast at hh ⊢
    convert hh using 1; ring
  rw [roots_card _ _ _ _ (Nat.pow_pos hp.pos) hR]
  exact_mod_cast hh'

lemma mass_height_bound (q N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hq : 0 < q) (hqN : q ≤ N) (hR : ∀ r ∈ R, r < q)
    (hheight : ∀ r ∈ R, q * (starts r + lengths r) + r ≤ N) :
    (roots q R starts lengths).card * q ≤ 2 * N * R.card := by
  rw [roots_card _ _ _ _ hq hR, Finset.sum_mul]
  calc
    _ ≤ ∑ r ∈ R, (2 * N) := by
      apply Finset.sum_le_sum
      intro r hr
      have hh : q * lengths r ≤ N := by
        calc
          _ ≤ q * (starts r + lengths r) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
          _ ≤ q * (starts r + lengths r) + r := Nat.le_add_right _ _
          _ ≤ N := hheight r hr
      nlinarith only [hh, hqN]
    _ = _ := by simp [mul_comm]

/-- This is a restricted construction ceiling, not an original-conjecture upper bound. -/
theorem card_bound (p k N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hp : p.Prime) (hqN : p ^ k ≤ N) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + lengths r) + r ≤ N)
    (hM : PairMatching (p ^ k) R)
    (hS : IsSidon (((roots (p ^ k) R starts lengths).image (fun n => n ^ 2)) : Set ℕ)) :
    (roots (p ^ k) R starts lengths).card ^ 3 ≤ 153600 * N ^ 2 := by
  have hq : 0 < p ^ k := Nat.pow_pos hp.pos
  have hmass := mass_square_bound p k N R starts lengths hp hqN hR hheight hS
  have hheight' := mass_height_bound (p ^ k) N R starts lengths hq hqN hR hheight
  have hlabels := pairMatching_card (p ^ k) R hq hM
  have hprod := Nat.mul_le_mul hmass hheight'
  have hprod' := Nat.mul_le_mul_left (76800 * N ^ 2) hlabels
  have hh : p ^ k * (roots (p ^ k) R starts lengths).card ^ 3 ≤
      p ^ k * (153600 * N ^ 2) := by nlinarith only [hprod, hprod']
  exact Nat.le_of_mul_le_mul_left hh hq

theorem real_bound (p k N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hp : p.Prime) (hqN : p ^ k ≤ N) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + lengths r) + r ≤ N)
    (hM : PairMatching (p ^ k) R)
    (hS : IsSidon (((roots (p ^ k) R starts lengths).image (fun n => n ^ 2)) : Set ℕ)) :
    ((roots (p ^ k) R starts lengths).card : ℝ) ≤ 54 * (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hc : ((roots (p ^ k) R starts lengths).card : ℝ) ^ 3 ≤ 153600 * (N : ℝ) ^ 2 := by
    exact_mod_cast card_bound p k N R starts lengths hp hqN hR hheight hM hS
  have hpow : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ N)]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ 153600 * (N : ℝ) ^ 2 := hc
    _ ≤ 157464 * (N : ℝ) ^ 2 := by nlinarith only [sq_nonneg (N : ℝ)]
    _ = (54 * (N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := by rw [mul_pow, hpow]; norm_num


/-- Squaring does not change cardinality on natural roots. -/
theorem square_value_bound (p k N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hp : p.Prime) (hqN : p ^ k ≤ N) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + lengths r) + r ≤ N)
    (hM : PairMatching (p ^ k) R)
    (hS : IsSidon (((roots (p ^ k) R starts lengths).image (fun n => n ^ 2)) : Set ℕ)) :
    (((roots (p ^ k) R starts lengths).image (fun n => n ^ 2)).card : ℝ) ≤
      54 * (N : ℝ) ^ (2 / 3 : ℝ) := by
  rw [Finset.card_image_of_injective _ (Nat.pow_left_injective (by decide : 2 ≠ 0))]
  exact real_bound p k N R starts lengths hp hqN hR hheight hM hS

#print axioms square_value_bound

#print axioms roots_card
#print axioms length_tail
#print axioms mass_square_bound
#print axioms card_bound
#print axioms real_bound

end Erdos773.UnequalShiftedFullFibers
