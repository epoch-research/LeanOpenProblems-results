import Submission.DyadicHarmonicCancellation

/-!
The bounded non-between harmonic partial sums have infinite total variation.
In fact, both their positive and negative increments have divergent sums.
This rules out absolute convergence and eventual monotonicity, but it does
not rule out conditional convergence of the partial sums. The latter is the
unproved property equivalent to the density conjecture in
`SingleDyadicWindowCriterion`.
-/

namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def nonBetweenHarmonicTerm (n : ℕ) : ℝ :=
  if factorBetween (n+1) then 0 else factorSign (n+1)/(n+1 : ℝ)

lemma nonBetweenHarmonicSum_eq_sum (N : ℕ) :
    nonBetweenHarmonicSum N = ∑ n ∈ range N, nonBetweenHarmonicTerm n := rfl

lemma nonBetweenHarmonicSum_increment (N : ℕ) :
    nonBetweenHarmonicSum (N+1)-nonBetweenHarmonicSum N =
      nonBetweenHarmonicTerm N := by
  rw [nonBetweenHarmonicSum_eq_sum, sum_range_succ,
    ← nonBetweenHarmonicSum_eq_sum]
  ring

lemma not_factorBetween_of_middle_prime (n : ℕ) (hp : (2*n+1).Prime) :
    ¬ factorBetween n := by
  have h0 : 0 < n := by
    have := hp.two_le
    omega
  have hn : Nat.maxPrimeFac n ≤ n := Nat.maxPrimeFac_le
  have hn1 : Nat.maxPrimeFac (n+1) ≤ n+1 := Nat.maxPrimeFac_le
  simp only [factorBetween, hp.maxPrimeFac_eq_self]
  omega

lemma abs_nonBetweenHarmonicTerm_of_prime (n : ℕ) (hp : (2*n+3).Prime) :
    |nonBetweenHarmonicTerm n| = 1/(n+1 : ℝ) := by
  have hnb : ¬ factorBetween (n+1) :=
    not_factorBetween_of_middle_prime (n+1) (by convert hp using 1)
  have hf : |factorSign (n+1)| = 1 := by
    unfold factorSign predicateSign
    split_ifs <;> norm_num
  simp only [nonBetweenHarmonicTerm, hnb, if_false, abs_div, hf,
    abs_of_nonneg (show (0 : ℝ) ≤ n+1 by positivity)]

/-- Absolute convergence fails because the odd-prime middle points already
contribute a divergent reciprocal sum. -/
theorem not_summable_abs_nonBetweenHarmonicTerm :
    ¬ Summable (fun n => |nonBetweenHarmonicTerm n|) := by
  intro hs
  let g : ℕ → ℝ := fun p => if p.Prime ∧ p ≠ 2 then 1/(p : ℝ) else 0
  have hodd : Summable (fun n => g (2*n+3)) := by
    apply hs.of_nonneg_of_le
    · intro n
      dsimp only [g]
      split_ifs <;> positivity
    · intro n
      dsimp only [g]
      split_ifs with hp
      · rw [abs_nonBetweenHarmonicTerm_of_prime n hp.1]
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith [show (0 : ℝ) ≤ n by positivity]
      · exact abs_nonneg _
  have hinj : Function.Injective (fun n : ℕ => 2*n+3) := by
    intro m n h
    dsimp only at h
    omega
  have hzero : ∀ p ∉ Set.range (fun n : ℕ => 2*n+3), g p = 0 := by
    intro p hp
    dsimp only [g]
    split_ifs with h
    · exfalso
      apply hp
      have hm : p%2=1 := h.1.mod_two_eq_one_iff_ne_two.mpr h.2
      have ht := h.1.two_le
      have hd := Nat.div_add_mod p 2
      exact ⟨p/2-1, by dsimp only; omega⟩
    · rfl
  have hg : Summable g := (hinj.summable_iff hzero).mp hodd
  apply not_summable_one_div_on_primes
  apply (summable_congr_atTop (f₁ := g) (g₁ :=
    Set.indicator {p | p.Prime} (fun p : ℕ => (1 : ℝ)/p)) ?_).mp hg
  filter_upwards [eventually_gt_atTop (2 : ℕ)] with p hp
  simp [g, Set.indicator_apply, show p ≠ 2 by omega]

/-- `Summable` for real-valued families is unconditional summability. This
statement does NOT say that the ordered partial sums fail to converge. -/
theorem not_summable_nonBetweenHarmonicTerm :
    ¬ Summable nonBetweenHarmonicTerm :=
  fun h => not_summable_abs_nonBetweenHarmonicTerm h.abs

lemma abs_eq_twice_positive_sub (x : ℝ) : |x| = 2*max x 0-x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_right hx']
    ring

lemma abs_eq_twice_negative_add (x : ℝ) : |x| = 2*max (-x) 0+x := by
  have h := abs_eq_twice_positive_sub (-x)
  simpa only [abs_neg, sub_neg_eq_add] using h

lemma nonBetween_abs_sum_eq_positive (N : ℕ) :
    (∑ n ∈ range N, |nonBetweenHarmonicTerm n|) =
      2*(∑ n ∈ range N, max (nonBetweenHarmonicTerm n) 0)-nonBetweenHarmonicSum N := by
  simp_rw [abs_eq_twice_positive_sub]
  rw [sum_sub_distrib, ← mul_sum, nonBetweenHarmonicSum_eq_sum]

lemma nonBetween_abs_sum_eq_negative (N : ℕ) :
    (∑ n ∈ range N, |nonBetweenHarmonicTerm n|) =
      2*(∑ n ∈ range N, max (-nonBetweenHarmonicTerm n) 0)+nonBetweenHarmonicSum N := by
  simp_rw [abs_eq_twice_negative_add]
  rw [sum_add_distrib, ← mul_sum, nonBetweenHarmonicSum_eq_sum]

/-- Each sign carries infinite harmonic mass, despite the bounded signed
partial sums. No assertion about conditional convergence is made. -/
theorem not_summable_nonBetween_positive :
    ¬ Summable (fun n => max (nonBetweenHarmonicTerm n) 0) := by
  intro hs
  apply not_summable_abs_nonBetweenHarmonicTerm
  apply summable_of_sum_range_le (fun n => abs_nonneg _) (c :=
    2*(∑' n, max (nonBetweenHarmonicTerm n) 0)+3)
  intro N
  rw [nonBetween_abs_sum_eq_positive]
  have hp := Summable.sum_le_tsum (range N) (fun n _ => le_max_right _ _) hs
  have hb := (abs_le.mp (nonBetweenHarmonicSum_bound N)).1
  linarith

theorem not_summable_nonBetween_negative :
    ¬ Summable (fun n => max (-nonBetweenHarmonicTerm n) 0) := by
  intro hs
  apply not_summable_abs_nonBetweenHarmonicTerm
  apply summable_of_sum_range_le (fun n => abs_nonneg _) (c :=
    2*(∑' n, max (-nonBetweenHarmonicTerm n) 0)+3)
  intro N
  rw [nonBetween_abs_sum_eq_negative]
  have hp := Summable.sum_le_tsum (range N) (fun n _ => le_max_right _ _) hs
  have hb := (abs_le.mp (nonBetweenHarmonicSum_bound N)).2
  linarith

theorem nonBetween_total_variation_tendsto_atTop :
    Tendsto (fun N => ∑ n ∈ range N,
      |nonBetweenHarmonicSum (n+1)-nonBetweenHarmonicSum n|) atTop atTop := by
  simp_rw [nonBetweenHarmonicSum_increment]
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => abs_nonneg _)).mp not_summable_abs_nonBetweenHarmonicTerm

theorem nonBetween_positive_mass_tendsto_atTop :
    Tendsto (fun N => ∑ n ∈ range N, max (nonBetweenHarmonicTerm n) 0)
      atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun _ => le_max_right _ _)).mp not_summable_nonBetween_positive

theorem nonBetween_negative_mass_tendsto_atTop :
    Tendsto (fun N => ∑ n ∈ range N, max (-nonBetweenHarmonicTerm n) 0)
      atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun _ => le_max_right _ _)).mp not_summable_nonBetween_negative


/-- There are increases and decreases beyond every endpoint. Thus the
bounded partial sums are neither eventually monotone nor eventually antitone. -/
theorem nonBetweenHarmonicSum_increases_and_decreases (N : ℕ) :
    (∃ k ≥ N, nonBetweenHarmonicSum k < nonBetweenHarmonicSum (k+1)) ∧
    (∃ k ≥ N, nonBetweenHarmonicSum (k+1) < nonBetweenHarmonicSum k) := by
  constructor
  · by_contra! h
    apply not_summable_nonBetween_positive
    have he : (fun k => max (nonBetweenHarmonicTerm k) 0) =ᶠ[atTop]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop N] with k hk
      have hi := nonBetweenHarmonicSum_increment k
      have hm := h k hk
      apply max_eq_right
      linarith
    exact (summable_congr_atTop he).mpr summable_zero
  · by_contra! h
    apply not_summable_nonBetween_negative
    have he : (fun k => max (-nonBetweenHarmonicTerm k) 0) =ᶠ[atTop]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop N] with k hk
      have hi := nonBetweenHarmonicSum_increment k
      have hm := h k hk
      apply max_eq_right
      linarith
    exact (summable_congr_atTop he).mpr summable_zero

theorem nonBetweenHarmonicSum_not_eventually_monotone :
    ¬ ∃ N : ℕ, MonotoneOn nonBetweenHarmonicSum (Set.Ici N) := by
  rintro ⟨N,hN⟩
  obtain ⟨k,hk,hdown⟩ := (nonBetweenHarmonicSum_increases_and_decreases N).2
  exact hdown.not_ge (hN hk (show k+1 ∈ Set.Ici N from by exact le_trans hk (Nat.le_succ k))
    (Nat.le_succ k))

theorem nonBetweenHarmonicSum_not_eventually_antitone :
    ¬ ∃ N : ℕ, AntitoneOn nonBetweenHarmonicSum (Set.Ici N) := by
  rintro ⟨N,hN⟩
  obtain ⟨k,hk,hup⟩ := (nonBetweenHarmonicSum_increases_and_decreases N).1
  exact hup.not_ge (hN hk (show k+1 ∈ Set.Ici N from by exact le_trans hk (Nat.le_succ k))
    (Nat.le_succ k))

#print axioms nonBetweenHarmonicSum_increases_and_decreases

#print axioms not_summable_abs_nonBetweenHarmonicTerm
#print axioms nonBetween_total_variation_tendsto_atTop
#print axioms nonBetween_positive_mass_tendsto_atTop
#print axioms nonBetween_negative_mass_tendsto_atTop

end Erdos371
