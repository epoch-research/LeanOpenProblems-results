import FormalConjecturesUtil

/-!
Elementary, unconditional facts for the reflection approach to Erdős 371.
This file does not import `Submission.Spec`, use either of its admitted
statements, or claim to prove the density conjecture.
-/

namespace Erdos371Reflection

/-- Consecutive natural numbers never have equal greatest prime factors,
including the library's conventions at zero and one. -/
theorem maxPrimeFac_succ_ne (n : ℕ) :
    Nat.maxPrimeFac (n + 1) ≠ Nat.maxPrimeFac n := by
  cases n with
  | zero => simp
  | succ n =>
    intro h
    have hp : Nat.Prime (Nat.maxPrimeFac (n + 1 + 1)) :=
      Nat.prime_maxPrimeFac_of_one_lt _ (by omega)
    have hd : Nat.maxPrimeFac (n + 1 + 1) ∣ n + 1 := by
      rw [h]
      exact Nat.maxPrimeFac_dvd
    have hsum : Nat.maxPrimeFac (n + 1 + 1) ∣ (n + 1) + 1 :=
      Nat.maxPrimeFac_dvd
    have hone : Nat.maxPrimeFac (n + 1 + 1) ∣ 1 :=
      (Nat.dvd_add_iff_right hd).mpr hsum
    exact hp.not_dvd_one hone

/-- The downward ordering is exactly the complement of the upward ordering. -/
theorem downward_iff_not_upward (n : ℕ) :
    Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n ↔
      ¬ Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) := by
  have h := maxPrimeFac_succ_ne n
  omega

/-- Antisymmetric edge current. -/
def edgeCurrent (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  f n * g (n + 1) - g n * f (n + 1)

/-- A single cutoff against its complement only gives a telescoping balance. -/
theorem current_against_one (f : ℕ → ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N, edgeCurrent f (fun _ => 1) n) = f 0 - f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [edgeCurrent, mul_one, one_mul]
    ring

/-- Swapping the two cutoffs reverses the current. -/
theorem edgeCurrent_swap (f g : ℕ → ℤ) (n : ℕ) :
    edgeCurrent g f n = -edgeCurrent f g n := by
  simp only [edgeCurrent]
  ring

/-- The exact finite count-to-signed-imbalance identity, before any limiting
argument. It applies in particular to the actual upward prime-factor predicate. -/
theorem signed_count (A : ℕ → Prop) [DecidablePred A] (N : ℕ) :
    (∑ n ∈ Finset.range N, if A n then (1 : ℤ) else -1) =
      2 * (((Finset.range N).filter A).card : ℤ) - N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.filter_insert]
    have hn : N ∉ (Finset.range N).filter A := by simp
    by_cases h : A N
    · simp only [h, if_true, Finset.card_insert_of_notMem hn, Nat.cast_add,
        Nat.cast_one]
      rw [ih]
      ring
    · simp only [h, if_false, Nat.cast_add, Nat.cast_one]
      rw [ih]
      ring

/-- The determinant of two adjacent cumulative cutoffs on bin labels. -/
def binCurrent (r s j : ℕ) : ℤ :=
  (if r ≤ j then 1 else 0) * (if s ≤ j + 1 then 1 else 0) -
    (if s ≤ j then 1 else 0) * (if r ≤ j + 1 then 1 else 0)

private theorem binCurrent_of_lt {r s : ℕ} (hrs : r < s) (j : ℕ) :
    binCurrent r s j = if j + 1 = s then 1 else 0 := by
  unfold binCurrent
  split_ifs <;> omega

private theorem sum_binCurrent_of_lt {K r s : ℕ} (hrs : r < s) (hs : s ≤ K) :
    (∑ j ∈ Finset.range K, binCurrent r s j) = 1 := by
  have hspos : 0 < s := by omega
  have heq (j : ℕ) : j + 1 = s ↔ j = s - 1 := by omega
  have hmem : s - 1 ∈ Finset.range K := by
    simp only [Finset.mem_range]
    omega
  simp_rw [binCurrent_of_lt hrs, heq]
  simp [hmem]

/-- Only adjacent cumulative cutoffs are needed to recover the ordering of
unequal bin labels. This is the exact finite algebra behind the mesh reduction. -/
theorem adjacent_cutoff_bins (K r s : ℕ) (hr : r ≤ K) (hs : s ≤ K) :
    (∑ j ∈ Finset.range K, binCurrent r s j) =
      if r < s then 1 else if s < r then -1 else 0 := by
  rcases lt_trichotomy r s with hrs | rfl | hsr
  · simp only [hrs, if_true]
    exact sum_binCurrent_of_lt hrs hs
  · simp [binCurrent]
  · have hswap (j : ℕ) : binCurrent r s j = -binCurrent s r j := by
      unfold binCurrent
      ring
    simp_rw [hswap]
    rw [Finset.sum_neg_distrib, sum_binCurrent_of_lt hsr hr]
    simp [hsr, Nat.not_lt.mpr hsr.le]

/-- The exact natural-density notion in the specification is equivalent to
vanishing of the ordinary, not logarithmic, signed counting average. -/
theorem hasDensity_iff_signedMean (A : ℕ → Prop) [DecidablePred A] :
    {n | A n}.HasDensity (1 / 2) ↔
      Filter.Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range N, if A n then (1 : ℝ) else -1) / N)
        Filter.atTop (nhds 0) := by
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N, if A n then (1 : ℝ) else -1) =
        2 * (((Finset.range N).filter A).card : ℝ) - N := by
    exact_mod_cast signed_count A N
  have hcard (N : ℕ) : ({n | A n} ∩ Set.Iio N).ncard =
      ((Finset.range N).filter A).card := by
    have heq : {n | A n} ∩ Set.Iio N =
        ((Finset.range N).filter A : Set ℕ) := by
      ext n
      simp [and_comm]
    rw [heq]
    exact Set.ncard_coe_finset _
  have hpartial (N : ℕ) : {n | A n}.partialDensity Set.univ N =
      (((Finset.range N).filter A).card : ℝ) / N := by
    simp [Set.partialDensity, hcard]
  have he : (fun N : ℕ =>
      (∑ n ∈ Finset.range N, if A n then (1 : ℝ) else -1) / N) =ᶠ[Filter.atTop]
      (fun N : ℕ => 2 * {n | A n}.partialDensity Set.univ N - 1) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, ?_⟩
    intro N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    dsimp only
    rw [hsum, hpartial, sub_div, mul_div_assoc, div_self hn]
  constructor
  · intro h
    change Filter.Tendsto (fun N => {n | A n}.partialDensity Set.univ N)
      Filter.atTop (nhds (1 / 2 : ℝ)) at h
    have ht : Filter.Tendsto
        (fun N => 2 * {n | A n}.partialDensity Set.univ N - 1)
        Filter.atTop (nhds 0) := by
      convert (h.const_mul (2 : ℝ)).sub_const 1 using 1
      norm_num
    exact ht.congr' he.symm
  · intro h
    have ht := h.congr' he
    change Filter.Tendsto (fun N => {n | A n}.partialDensity Set.univ N)
      Filter.atTop (nhds (1 / 2 : ℝ))
    have hiden (x : ℝ) : (2 * x - 1 + 1) / 2 = x := by ring
    simpa only [hiden, zero_add] using (ht.add_const 1).div_const 2

/-- Specialization to the actual greatest-prime-factor predicate; this is an
unconditional equivalence, not a proof that either side holds. -/
theorem erdos371_iff_signedMean :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Filter.Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range N,
            if Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) then (1 : ℝ) else -1) / N)
        Filter.atTop (nhds 0) := by
  exact hasDensity_iff_signedMean _


#print axioms maxPrimeFac_succ_ne
#print axioms downward_iff_not_upward
#print axioms current_against_one
#print axioms edgeCurrent_swap
#print axioms signed_count
#print axioms adjacent_cutoff_bins
#print axioms hasDensity_iff_signedMean
#print axioms erdos371_iff_signedMean

end Erdos371Reflection
