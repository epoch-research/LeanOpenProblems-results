import Submission.UnitIntervalDensity
import Submission.UnequalShiftedFullFibers
import Submission.DivisorBound

/-!
An arbitrary-modulus extension of the full-fiber capacity bound.
This concerns WHOLE full-fiber unions, not arbitrary sparse square-Sidon sets.
-/
namespace Erdos773.ArbitraryModulusFullFibers

open Finset MatchedResidueLifting

set_option maxHeartbeats 2000000

lemma divisor_card_pos (q : ℕ) (hq : 0 < q) : 0 < q.divisors.card :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hq.ne'⟩

/-- The only modulus loss is a subpower divisor factor. -/
theorem common_capacity (q N H : ℕ) (R : Finset ℕ) (starts : ℕ → ℕ)
    (hq : 0 < q) (hR : ∀ r ∈ R, r < q)
    (hheight : ∀ r ∈ R, q * (starts r + H) + r ≤ N)
    (hS : IsSidon (((ShiftedFullFiberCapacity.roots q H R starts).image
      (fun n => n ^ 2)) : Set ℕ)) :
    R.card * H ^ 2 ≤ 2400 * q.divisors.card ^ 2 * N := by
  by_cases hne : R.Nonempty
  · obtain ⟨r, hr⟩ := hne
    have hτ := divisor_card_pos q hq
    have hτsq : q.divisors.card ≤ q.divisors.card ^ 2 := by nlinarith
    have hqH : q * H ≤ N := by
      calc
        _ ≤ q * (starts r + H) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
        _ ≤ q * (starts r + H) + r := Nat.le_add_right _ _
        _ ≤ N := hheight r hr
    have hRc := PrimePowerFullFiberBound.labels_card q R hR
    by_cases hsmall : H < 40 * q.divisors.card ^ 2
    · have hRH := (Nat.mul_le_mul_right H hRc).trans hqH
      have hh := Nat.mul_le_mul_right H hRH
      have hNH := Nat.mul_le_mul_left N (show H ≤ 40 * q.divisors.card ^ 2 by omega)
      nlinarith only [hh, hNH]
    · let L := H / 10
      have hLlarge : 2 * q.divisors.card ^ 2 ≤ L := by dsimp only [L]; omega
      have hL : 0 < L := by nlinarith only [hLlarge, hτ]
      have hHL : 10 * L ≤ H := Nat.mul_div_le H 10
      have hHLarge : H ≤ 20 * L := by dsimp only [L] at hL ⊢; omega
      obtain ⟨U, hU, hgap, hUL⟩ := UnitIntervalDensity.unit_gaps q L hq hLlarge
      have hc := ShiftedFullFiberCapacity.scaled_gap_capacity N q H L R U starts
        hq hL hHL hR hU hgap hheight hS
      have hqL : q * L ≤ N :=
        (Nat.mul_le_mul_left _ (show L ≤ H by omega)).trans hqH
      have hmul := Nat.mul_le_mul_left (R.card * L) hUL
      have hcap := Nat.mul_le_mul_left (2 * q.divisors.card) (show R.card * U.card * L ≤ 3 * N by omega)
      have hcap' : R.card * L ^ 2 ≤ 6 * q.divisors.card * N := by
        nlinarith only [hmul, hcap]
      have hsquare := Nat.mul_le_mul_left R.card (Nat.pow_le_pow_left hHLarge 2)
      have hτmul := Nat.mul_le_mul_right (2400 * N) hτsq
      nlinarith only [hsquare, hcap', hτmul]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

open UnequalShiftedFullFibers

/-- Truncation to a full common-length union preserves Sidonness. -/
theorem length_tail (q N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hq : 0 < q) (hR : ∀ r ∈ R, r < q)
    (hheight : ∀ r ∈ R, q * (starts r + lengths r) + r ≤ N)
    (hS : IsSidon (((roots q R starts lengths).image (fun n => n ^ 2)) : Set ℕ))
    (t : ℕ) :
    (R.filter (fun r => t ≤ lengths r)).card * t ^ 2 ≤ 2400 * q.divisors.card ^ 2 * N := by
  let S := R.filter (fun r => t ≤ lengths r)
  have hSR : S ⊆ R := Finset.filter_subset _ _
  have hlen : ∀ r ∈ S, t ≤ lengths r := fun r hr => (Finset.mem_filter.mp hr).2
  apply common_capacity q N t S starts hq (fun r hr => hR r (hSR hr))
  · intro r hr
    have hh := Nat.mul_le_mul_left q (Nat.add_le_add_left (hlen r hr) (starts r))
    exact (Nat.add_le_add_right hh r).trans (hheight r (hSR hr))
  · exact Set.IsSidon.subset hS (Finset.image_subset_image (common_subset hSR hlen))

theorem mass_square_bound (q N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hq : 0 < q) (hqN : q ≤ N) (hR : ∀ r ∈ R, r < q)
    (hheight : ∀ r ∈ R, q * (starts r + lengths r) + r ≤ N)
    (hS : IsSidon (((roots q R starts lengths).image (fun n => n ^ 2)) : Set ℕ)) :
    (roots q R starts lengths).card ^ 2 ≤ 38400 * q.divisors.card ^ 2 * N * R.card := by
  have hRc := (PrimePowerFullFiberBound.labels_card q R hR).trans hqN
  have hτ : (1 : ℝ) ≤ q.divisors.card := by exact_mod_cast divisor_card_pos q hq
  have hA : (R.card : ℝ) ≤ 2400 * (q.divisors.card : ℝ) ^ 2 * N := by
    have hh : (R.card : ℝ) ≤ N := by exact_mod_cast hRc
    have hτsq : (1 : ℝ) ≤ 2400 * (q.divisors.card : ℝ) ^ 2 := by nlinarith
    have hn := mul_le_mul_of_nonneg_right hτsq (show (0 : ℝ) ≤ N by positivity)
    nlinarith only [hh, hn]
  have ht (t : ℕ) (_ht : 0 < t) :
      ((R.filter (fun r => t ≤ lengths r)).card : ℝ) * (t : ℝ) ^ 2 ≤
        2400 * (q.divisors.card : ℝ) ^ 2 * N := by
    exact_mod_cast length_tail q N R starts lengths hq hR hheight hS t
  have hh := FiniteTailCapacity.mass_square_bound R lengths
    (2400 * (q.divisors.card : ℝ) ^ 2 * N) hA ht
  have hh' : ((∑ r ∈ R, (lengths r + 1) : ℕ) : ℝ) ^ 2 ≤
      38400 * (q.divisors.card : ℝ) ^ 2 * N * R.card := by
    push_cast at hh ⊢
    convert hh using 1; ring
  rw [roots_card _ _ _ _ hq hR]
  exact_mod_cast hh'

/-- The modulus-height and modular pair-matching hypotheses remain essential. -/
theorem card_bound (q N : ℕ) (R : Finset ℕ) (starts lengths : ℕ → ℕ)
    (hq : 0 < q) (hqN : q ≤ N) (hR : ∀ r ∈ R, r < q)
    (hheight : ∀ r ∈ R, q * (starts r + lengths r) + r ≤ N)
    (hM : PairMatching q R)
    (hS : IsSidon (((roots q R starts lengths).image (fun n => n ^ 2)) : Set ℕ)) :
    (roots q R starts lengths).card ^ 3 ≤ 153600 * q.divisors.card ^ 2 * N ^ 2 := by
  have hmass := mass_square_bound q N R starts lengths hq hqN hR hheight hS
  have hheight' := mass_height_bound q N R starts lengths hq hqN hR hheight
  have hlabels := pairMatching_card q R hq hM
  have hprod := Nat.mul_le_mul hmass hheight'
  have hprod' := Nat.mul_le_mul_left (76800 * q.divisors.card ^ 2 * N ^ 2) hlabels
  have hh : q * (roots q R starts lengths).card ^ 3 ≤
      q * (153600 * q.divisors.card ^ 2 * N ^ 2) := by nlinarith only [hprod, hprod']
  exact Nat.le_of_mul_le_mul_left hh hq

/-- Uniformly over positive moduli below the height, these restricted whole-fiber
constructions have exponent at most two thirds. This is not a bound on the
maximum Sidon subset of all squares. -/
theorem eventual_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ q : ℕ, ∀ R : Finset ℕ, ∀ starts lengths : ℕ → ℕ,
      0 < q → q ≤ N → (∀ r ∈ R, r < q) →
      (∀ r ∈ R, q * (starts r + lengths r) + r ≤ N) → PairMatching q R →
      IsSidon (((roots q R starts lengths).image (fun n => n ^ 2)) : Set ℕ) →
      ((roots q R starts lengths).card : ℝ) ≤ (N : ℝ) ^ (2 / 3 + ε) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_card_subpower ε hε
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop, 153600 * C ^ 2 ≤ (N : ℝ) ^ ε :=
    Filter.tendsto_atTop.mp
      ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop) (153600 * C ^ 2)
  filter_upwards [hlarge, Filter.eventually_ge_atTop 1] with N hlarge hN
  intro q R starts lengths hq hqN hR hheight hM hS
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : ((roots q R starts lengths).card : ℝ) ^ 3 ≤
      153600 * (q.divisors.card : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
    exact_mod_cast card_bound q N R starts lengths hq hqN hR hheight hM hS
  have hdiv' : (q.divisors.card : ℝ) ≤ C * (N : ℝ) ^ ε := by
    calc
      _ ≤ C * (q : ℝ) ^ ε := hdiv q
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqN) hε.le) hC.le
  have hpow : ((N : ℝ) ^ (2 / 3 + ε)) ^ 3 = (N : ℝ) ^ (2 + 3 * ε) := by
    rw [← Real.rpow_mul_natCast hNR.le]
    congr 1
    norm_num
    ring
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
  rw [hpow]
  calc
    _ ≤ 153600 * (q.divisors.card : ℝ) ^ 2 * (N : ℝ) ^ 2 := hc
    _ ≤ 153600 * (C * (N : ℝ) ^ ε) ^ 2 * (N : ℝ) ^ 2 := by
      gcongr
    _ = (153600 * C ^ 2) * ((N : ℝ) ^ ε) ^ 2 * (N : ℝ) ^ 2 := by ring
    _ ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ ε) ^ 2 * (N : ℝ) ^ 2 := by
      gcongr
    _ = (N : ℝ) ^ (2 + 3 * ε) := by
      rw [← pow_succ', ← Real.rpow_mul_natCast hNR.le, ← Real.rpow_natCast (N : ℝ) 2,
        ← Real.rpow_add hNR]
      congr 1
      norm_num
      ring

#print axioms eventual_power_bound

#print axioms common_capacity
#print axioms mass_square_bound
#print axioms card_bound

end Erdos773.ArbitraryModulusFullFibers
