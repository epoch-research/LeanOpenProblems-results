import Submission.ClosedSmoothFibers
import Submission.IteratedTotientFibers

/-!
# Counting cheap intermediate radicals

Small radicals can occur at outputs with large fibers, but they cannot
occur at polynomially many intermediate values of a fixed fiber while
remaining uniformly subpower. This is a restricted-fiber bound, not a
resolution of Erdős 821 or an exclusion of other lifting constructions.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.RadicalLift

lemma card_le_of_bounded_radical (S : Finset ℕ) (n R : ℕ)
    (hS : ∀ m ∈ S, totient m = n ∧ radical m ≤ R) : S.card ≤ R := by
  have hmap : Set.MapsTo radical (S : Set ℕ) (Finset.Icc 1 R : Set ℕ) := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨radical_pos m, (hS m hm).2⟩
  have hinj : Set.InjOn radical (S : Set ℕ) := by
    intro a ha b hb hab
    exact radical_injOn_totient_fiber n (hS a ha).1 (hS b hb).1 hab
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
    Finset.card_le_card_of_injOn radical hmap hinj

lemma card_le_real_of_bounded_radical (S : Finset ℕ) (n : ℕ) (R : ℝ)
    (hR : 0 ≤ R) (hS : ∀ m ∈ S, totient m = n ∧ (radical m : ℝ) ≤ R) :
    (S.card : ℝ) ≤ R := by
  have h : S.card ≤ ⌊R⌋₊ := card_le_of_bounded_radical S n ⌊R⌋₊ (by
    intro m hm
    exact ⟨(hS m hm).1, Nat.le_floor (hS m hm).2⟩)
  exact (by exact_mod_cast h : (S.card : ℝ) ≤ ⌊R⌋₊).trans (Nat.floor_le hR)

lemma small_radical_first_fiber_card_le (n : ℕ) (η : ℝ) :
    (((IteratedTotient.fiber 1 n).filter
      (fun m => (radical m : ℝ) ≤ (n : ℝ)^η)).card : ℝ) ≤ (n : ℝ)^η := by
  apply card_le_real_of_bounded_radical _ n _ (Real.rpow_nonneg (Nat.cast_nonneg n) η)
  intro m hm
  obtain ⟨hm, hr⟩ := Finset.mem_filter.mp hm
  exact ⟨by simpa only [IteratedTotient.mem_fiber, Function.iterate_one] using hm, hr⟩

/-- An upper exponent on all one-step fibers still applies, up to the
specified radical allowance, to a two-step fiber restricted to cheap middle
values. Unlike the unrestricted recurrence, this does not add two copies
of the one-step upper exponent. -/
theorem eventually_small_radical_second_le (a η ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^a) :
    ∀ᶠ n : ℕ in atTop,
      (IteratedTotient.restrictedSecondMultiplicity
        (fun m => (radical m : ℝ) ≤ (n : ℝ)^η) n : ℝ) ≤
      (n : ℝ)^(a + η + ε) := by
  let δ : ℝ := ε / (a + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨M, hM⟩ := eventually_atTop.mp H
  filter_upwards [IteratedTotient.eventually_input_le_rpow δ hδ,
    eventually_ge_atTop M, eventually_ge_atTop 1] with n hsize hnM hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hbudget : (1 + δ) * a ≤ a + ε := by
    have hδeq : δ * (a + 1) = ε := div_mul_cancel₀ ε (by linarith : a + 1 ≠ 0)
    nlinarith
  rw [IteratedTotient.restricted_second_eq_sum, Nat.cast_sum]
  calc
    (∑ m ∈ (IteratedTotient.fiber 1 n).filter
        (fun m => (radical m : ℝ) ≤ (n : ℝ)^η), (g m : ℝ)) ≤
        ∑ _m ∈ (IteratedTotient.fiber 1 n).filter
          (fun m => (radical m : ℝ) ≤ (n : ℝ)^η), (n : ℝ)^(a + ε) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmF := (Finset.mem_filter.mp hm).1
      have hφ : totient m = n := by
        simpa only [IteratedTotient.mem_fiber, Function.iterate_one] using hmF
      calc
        (g m : ℝ) ≤ (m : ℝ)^a := hM m (hnM.trans (IteratedTotient.output_le_of_mem hmF))
        _ ≤ ((n : ℝ)^(1 + δ))^a :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) (hsize m hφ) ha
        _ = (n : ℝ)^((1 + δ)*a) := (Real.rpow_mul hnpos.le _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR hbudget
    _ = (((IteratedTotient.fiber 1 n).filter
        (fun m => (radical m : ℝ) ≤ (n : ℝ)^η)).card : ℝ) * (n : ℝ)^(a + ε) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ)^η * (n : ℝ)^(a + ε) :=
      mul_le_mul_of_nonneg_right (small_radical_first_fiber_card_le n η)
        (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ)^(a + η + ε) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

end Erdos821.RadicalLift
