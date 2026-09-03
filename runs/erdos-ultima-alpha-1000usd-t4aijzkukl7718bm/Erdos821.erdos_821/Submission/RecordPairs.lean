import Submission.RecordFibers
import Submission.LcmFibers

/-!
# Large-overlap pair frequencies at full-fiber records

These results test the input needed by the conditional LCM amplification
criterion. They do not prove or disprove Erdős 821. In particular, an upper
bound on pair frequencies is not a lower bound providing amplification.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- The normalized record principle works at any exponent strictly below
the given witness exponent, not only at half that exponent. -/
lemma exists_large_normalized_record_at (f : ℕ → ℕ) (δ s : ℝ) (hs : s < δ)
    (H : {n : ℕ | (n : ℝ) ^ δ < (f n : ℝ)}.Infinite) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ (n : ℝ) ^ δ < (f n : ℝ) ∧
      ∀ j : ℕ, j ≤ n → (f j : ℝ) / (j : ℝ) ^ s ≤ (f n : ℝ) / (n : ℝ) ^ s := by
  let F : ℕ → ℝ := fun n => (f n : ℝ) / (n : ℝ) ^ s
  let C := ∑ j ∈ Finset.range (N + 1), F j
  have hFnonneg (j : ℕ) : 0 ≤ F j := by dsimp [F]; positivity
  have hgap : 0 < δ - s := sub_pos.mpr hs
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ - s)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_atTop C))
  obtain ⟨m, hmf, hmM⟩ := H.exists_gt M
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmPow : 0 < (m : ℝ) ^ s := Real.rpow_pos_of_pos hmpos s
  have hFmbig : (m : ℝ) ^ (δ - s) < F m := by
    apply (lt_div_iff₀ hmPow).mpr
    rw [← Real.rpow_add hmpos, sub_add_cancel]
    exact hmf
  obtain ⟨n, hnmem, hmax⟩ := Finset.exists_max_image (Finset.range (m + 1)) F
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hnm : n ≤ m := by have := Finset.mem_range.mp hnmem; omega
  have hFn : F m ≤ F n := hmax m (Finset.mem_range.mpr (by omega))
  have hNn : N < n := by
    by_contra h
    have hnN : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hFC : F n ≤ C := Finset.single_le_sum (fun j _ => hFnonneg j) hnN
    exact (not_lt_of_ge hFC) ((hM m hmM.le).trans (hFmbig.trans_le hFn))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnPow : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hnpos s
  refine ⟨n, hNn, ?_, ?_⟩
  · calc
      (n : ℝ) ^ δ = (n : ℝ) ^ (δ - s) * (n : ℝ) ^ s := by
        rw [← Real.rpow_add hnpos, sub_add_cancel]
      _ ≤ (m : ℝ) ^ (δ - s) * (n : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnm) hgap.le) hnPow.le
      _ < F n * (n : ℝ) ^ s := mul_lt_mul_of_pos_right (hFmbig.trans_le hFn) hnPow
      _ = (f n : ℝ) := div_mul_cancel₀ _ hnPow.ne'
  · intro j hj
    exact hmax j (Finset.mem_range.mpr (by omega))

noncomputable def oddLargeOverlapPairs (n : ℕ) (η : ℝ) : Finset (ℕ × ℕ) :=
  ((oddSquarefreeFiber n) ×ˢ (oddSquarefreeFiber n)).filter
    (fun ab => (n : ℝ) ^ η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ))

lemma card_oddLargeOverlapPairs_eq_sum (n : ℕ) (η : ℝ) :
    (oddLargeOverlapPairs n η).card = ∑ a ∈ oddSquarefreeFiber n,
      ((oddSquarefreeFiber n).filter
        (fun b => (n : ℝ) ^ η ≤ (totient (Nat.gcd a b) : ℝ))).card := by
  simp only [oddLargeOverlapPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]

/-- For a fixed first input, group possible partners by their GCD, which
must be a divisor of that first input. -/
lemma normalized_record_odd_overlap_row_bound (n a : ℕ) (hn : 0 < n)
    (ha : a ∈ oddSquarefreeFiber n) (s η : ℝ) (hs : 0 ≤ s)
    (hrec : ∀ j : ℕ, j ≤ n →
      (gOddSquarefree j : ℝ) / (j : ℝ) ^ s ≤ (gOddSquarefree n : ℝ) / (n : ℝ) ^ s) :
    (n : ℝ) ^ (s * η) *
      (((oddSquarefreeFiber n).filter
        (fun b => (n : ℝ) ^ η ≤ (totient (Nat.gcd a b) : ℝ))).card : ℝ) ≤
      (a.divisors.card : ℝ) * (gOddSquarefree n : ℝ) := by
  let R := (oddSquarefreeFiber n).filter
    (fun b => (n : ℝ) ^ η ≤ (totient (Nat.gcd a b) : ℝ))
  have ha0 : a ≠ 0 := (mem_oddSquarefreeFiber.mp ha).1.ne_zero
  have hmap : ∀ b ∈ R, Nat.gcd a b ∈ a.divisors := by
    intro b _hb
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, ha0⟩
  have hcount : R.card = ∑ d ∈ a.divisors, (R.filter (fun b => Nat.gcd a b = d)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hpoint (d : ℕ) (_hd : d ∈ a.divisors) :
      (n : ℝ) ^ (s * η) * ((R.filter (fun b => Nat.gcd a b = d)).card : ℝ) ≤
        (gOddSquarefree n : ℝ) := by
    by_cases hne : (R.filter (fun b => Nat.gcd a b = d)).Nonempty
    · obtain ⟨b, hb⟩ := hne
      obtain ⟨hbR, hbd⟩ := Finset.mem_filter.mp hb
      have he : (n : ℝ) ^ η ≤ (totient d : ℝ) := by
        rw [← hbd]
        exact (Finset.mem_filter.mp hbR).2
      have hpow : (n : ℝ) ^ (s * η) ≤ (totient d : ℝ) ^ s := by
        calc
          (n : ℝ) ^ (s * η) = ((n : ℝ) ^ η) ^ s := by
            rw [← Real.rpow_mul (Nat.cast_nonneg n)]; congr 1; ring
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) he hs
      have hsub : R.filter (fun b => Nat.gcd a b = d) ⊆
          (oddSquarefreeFiber n).filter (fun b => d ∣ b) := by
        intro c hc
        obtain ⟨hcR, hcd⟩ := Finset.mem_filter.mp hc
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hcR).1, hcd ▸ Nat.gcd_dvd_right a c⟩
      have hcard : ((R.filter (fun b => Nat.gcd a b = d)).card : ℝ) ≤
          (((oddSquarefreeFiber n).filter (fun b => d ∣ b)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact (mul_le_mul hpow hcard (Nat.cast_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
          (normalized_record_odd_fiber_core_bound n d hn s hrec)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty,
        Nat.cast_zero, mul_zero, Nat.cast_nonneg]
  change (n : ℝ) ^ (s * η) * (R.card : ℝ) ≤ _
  rw [hcount, Nat.cast_sum, Finset.mul_sum]
  calc
    (∑ d ∈ a.divisors, (n : ℝ) ^ (s * η) * ((R.filter (fun b => Nat.gcd a b = d)).card : ℝ)) ≤
        ∑ _d ∈ a.divisors, (gOddSquarefree n : ℝ) := Finset.sum_le_sum hpoint
    _ = _ := by simp

/-- The full pair count inherits a divisor-count loss, rather than a
factor equal to the whole fiber size, from possible GCDs in each row. -/
lemma normalized_record_odd_overlap_pair_bound (n : ℕ) (hn : 0 < n)
    (s η : ℝ) (hs : 0 ≤ s)
    (hrec : ∀ j : ℕ, j ≤ n →
      (gOddSquarefree j : ℝ) / (j : ℝ) ^ s ≤ (gOddSquarefree n : ℝ) / (n : ℝ) ^ s) :
    (n : ℝ) ^ (s * η) * ((oddLargeOverlapPairs n η).card : ℝ) ≤
      (gOddSquarefree n : ℝ) * ∑ a ∈ oddSquarefreeFiber n, (a.divisors.card : ℝ) := by
  rw [card_oddLargeOverlapPairs_eq_sum, Nat.cast_sum, Finset.mul_sum]
  calc
    _ ≤ ∑ a ∈ oddSquarefreeFiber n, (a.divisors.card : ℝ) * (gOddSquarefree n : ℝ) :=
      Finset.sum_le_sum (fun a ha => normalized_record_odd_overlap_row_bound n a hn ha s η hs hrec)
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma eventually_normalized_record_odd_overlap_bound (ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, 0 ≤ s →
      (∀ j : ℕ, j ≤ n →
        (gOddSquarefree j : ℝ) / (j : ℝ) ^ s ≤ (gOddSquarefree n : ℝ) / (n : ℝ) ^ s) →
      ∀ η : ℝ, (n : ℝ) ^ (s * η) * ((oddLargeOverlapPairs n η).card : ℝ) ≤
        (n : ℝ) ^ ζ * (gOddSquarefree n : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop 1, eventually_uniform_lcm_divisor_bound ζ hζ]
    with n hn hD
  intro s hs hrec η
  have hn0 : 0 < n := by omega
  have hsum : (∑ a ∈ oddSquarefreeFiber n, (a.divisors.card : ℝ)) ≤
      (gOddSquarefree n : ℝ) * (n : ℝ) ^ ζ := by
    calc
      _ ≤ ∑ _a ∈ oddSquarefreeFiber n, (n : ℝ) ^ ζ := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨haSq, haOdd, haφ⟩ := mem_oddSquarefreeFiber.mp ha
        have haBound : a ≤ n ^ 2 := by
          simpa only [haφ] using le_totient_sq_of_squarefree_odd a haSq haOdd
        apply hD a
        calc
          a ≤ n ^ 2 := haBound
          _ ≤ n ^ 4 := Nat.pow_le_pow_right hn (by decide)
          _ ≤ 576 * n ^ 4 := by omega
      _ = _ := by simp [card_oddSquarefreeFiber]
  calc
    _ ≤ (gOddSquarefree n : ℝ) * ∑ a ∈ oddSquarefreeFiber n, (a.divisors.card : ℝ) :=
      normalized_record_odd_overlap_pair_bound n hn0 s η hs hrec
    _ ≤ (gOddSquarefree n : ℝ) * ((gOddSquarefree n : ℝ) * (n : ℝ) ^ ζ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Unconditionally, there are polynomial-size full odd squarefree fibers
whose pair-overlap frequencies satisfy these upper bounds at every root
threshold. The same `n` works for all `η`. -/
theorem exists_full_odd_fibers_with_sparse_overlap_pairs :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ s : ℝ, 0 ≤ s → s < δ →
      ∀ ζ : ℝ, 0 < ζ → ∀ N : ℕ, ∃ n : ℕ,
        N < n ∧ (n : ℝ) ^ δ < (gOddSquarefree n : ℝ) ∧
        ∀ η : ℝ, (n : ℝ) ^ (s * η) * ((oddLargeOverlapPairs n η).card : ℝ) ≤
          (n : ℝ) ^ ζ * (gOddSquarefree n : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_positive_power_gOddSquarefree
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro s hs hsδ ζ hζ N
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_normalized_record_odd_overlap_bound ζ hζ)
  obtain ⟨n, hn, hnG, hrec⟩ := exists_large_normalized_record_at gOddSquarefree δ s hsδ H (max N M)
  exact ⟨n, (le_max_left _ _).trans_lt hn, hnG,
    hM n ((le_max_right _ _).trans hn.le) s hs hrec⟩

#print axioms exists_large_normalized_record_at
#print axioms normalized_record_odd_overlap_pair_bound
#print axioms exists_full_odd_fibers_with_sparse_overlap_pairs

end Erdos821
