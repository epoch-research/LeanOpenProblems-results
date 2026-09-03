import Submission.UniformSmoothReciprocalTail

/-! Uniform control of the errors in all harmonic winning-prime currents
up to a cutoff. Disjointness of the winner labels avoids a factor equal to
the number of labels. This does NOT estimate the complementary large-prime
current tail required for the natural-density conjecture. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma real_tsum_tail_ite_eq_nat_add (f : ℕ → ℝ) (hf : Summable f) (N : ℕ) :
    (∑' n, if N≤n then f n else 0) = ∑' j, f (j+N) := by
  have hs : Summable (fun n => if N≤n then f n else 0) := by
    convert hf.indicator {n | N≤n} using 1
    funext n
    simp only [Set.indicator_apply,Set.mem_setOf_eq]
  have h := hs.sum_add_tsum_nat_add N
  have hz : (∑ n ∈ range N, if N≤n then f n else 0) = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [if_neg (by have := mem_range.mp hn; omega)]
  rw [hz,zero_add] at h
  simpa only [Nat.le_add_left,if_true] using h.symm

lemma primeWinnerHarmonic_error_le_tail (p N : ℕ) :
    ‖primeWinnerHarmonicLimit p-rawPrimeWinnerHarmonic p N‖ ≤
      ∑' j, ‖primeWinnerHarmonicTerm p (j+N)‖ := by
  have hs := summable_primeWinnerHarmonicTerm_norm p
  have hterm : Summable (primeWinnerHarmonicTerm p) := hs.of_norm
  have he := hterm.sum_add_tsum_nat_add N
  change rawPrimeWinnerHarmonic p N + (∑' j, primeWinnerHarmonicTerm p (j+N)) =
    primeWinnerHarmonicLimit p at he
  have ht : primeWinnerHarmonicLimit p-rawPrimeWinnerHarmonic p N =
      ∑' j, primeWinnerHarmonicTerm p (j+N) := by linarith
  rw [ht]
  exact norm_tsum_le_tsum_norm ((summable_nat_add_iff (f := fun n => ‖primeWinnerHarmonicTerm p n‖) N).mpr hs)

lemma sum_primeWinnerHarmonicTerm_norm_le_smooth (B n : ℕ) :
    (∑ p ∈ range (B+1), ‖primeWinnerHarmonicTerm p n‖) ≤ smoothReciprocal B n := by
  classical
  by_cases hn : n=0
  · subst n
    simp only [primeWinnerHarmonicTerm,Nat.cast_zero,div_zero,ite_self,norm_zero,sum_const_zero]
    exact smoothReciprocal_nonneg B 0
  by_cases hw : primeWinner n≤B
  · have hm : primeWinner n∈range (B+1) := mem_range.mpr (by omega)
    rw [sum_eq_single (primeWinner n)]
    · rw [primeWinnerHarmonicTerm,if_pos rfl,norm_div,factorSign_norm,Real.norm_natCast,
        smoothReciprocal_of_maxPrimeFac_le B n hn ((le_max_left _ _).trans hw)]
    · intro p hp hne
      simp only [primeWinnerHarmonicTerm,if_neg (Ne.symm hne),norm_zero]
    · intro h
      exact (h hm).elim
  · have hz : (∑ p ∈ range (B+1), ‖primeWinnerHarmonicTerm p n‖) = 0 := by
      apply sum_eq_zero
      intro p hp
      have hne : primeWinner n≠p := by have := mem_range.mp hp; omega
      simp only [primeWinnerHarmonicTerm,if_neg hne,norm_zero]
    rw [hz]
    exact smoothReciprocal_nonneg B n

noncomputable def primeCurrentHeadError (B N : ℕ) : ℝ :=
  ∑ p ∈ range (B+1), ‖primeWinnerHarmonicLimit p-rawPrimeWinnerHarmonic p N‖

/-- A single smooth-number tail controls the whole finite l1 error. -/
theorem primeCurrentHeadError_le_smoothReciprocalTail (B N : ℕ) :
    primeCurrentHeadError B N ≤ smoothReciprocalTail B N := by
  have hs (p : ℕ) : Summable (fun j => ‖primeWinnerHarmonicTerm p (j+N)‖) :=
    (summable_nat_add_iff (f := fun n => ‖primeWinnerHarmonicTerm p n‖) N).mpr
      (summable_primeWinnerHarmonicTerm_norm p)
  have hsum : Summable (fun j => ∑ p ∈ range (B+1), ‖primeWinnerHarmonicTerm p (j+N)‖) :=
    summable_sum (fun p _ => hs p)
  calc
    _ ≤ ∑ p ∈ range (B+1), ∑' j, ‖primeWinnerHarmonicTerm p (j+N)‖ :=
      sum_le_sum (fun p _ => primeWinnerHarmonic_error_le_tail p N)
    _ = ∑' j, ∑ p ∈ range (B+1), ‖primeWinnerHarmonicTerm p (j+N)‖ :=
      (Summable.tsum_finsetSum (fun p _ => hs p)).symm
    _ ≤ ∑' j, smoothReciprocal B (j+N) :=
      Summable.tsum_le_tsum (fun j => sum_primeWinnerHarmonicTerm_norm_le_smooth B (j+N))
        hsum ((summable_nat_add_iff N).mpr (summable_smoothReciprocal B))
    _ = smoothReciprocalTail B N :=
      (real_tsum_tail_ite_eq_nat_add (smoothReciprocal B) (summable_smoothReciprocal B) N).symm

/-- Uniform simultaneous approximation, with no factor B in the estimate. -/
theorem primeCurrentHeadError_uniform_bound (B N : ℕ) (hB : 0<B) (hN : 0<N) :
    primeCurrentHeadError B N ≤
      2*Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2) *
        Real.exp (-Real.log 2*Real.log N/(32*Real.log (B+1 : ℝ))) :=
  (primeCurrentHeadError_le_smoothReciprocalTail B N).trans
    (smoothReciprocalTail_uniform_bound B N hB hN)

theorem primeCurrentHeadError_large_u_bound (B N : ℕ) (hB : 0<B) (hN : 0<N)
    (u : ℝ) (hu : 1024≤u)
    (hscale : u*Real.log (B+1 : ℝ)=Real.log N)
    (hrange : Real.log u≤4*Real.log (B+1 : ℝ)) :
    primeCurrentHeadError B N ≤
      Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2)*Real.exp (-u*Real.log u/16) :=
  (primeCurrentHeadError_le_smoothReciprocalTail B N).trans
    (smoothReciprocalTail_large_u_bound B N hB hN u hu hscale hrange)

#print axioms primeCurrentHeadError_le_smoothReciprocalTail
#print axioms primeCurrentHeadError_uniform_bound
#print axioms primeCurrentHeadError_large_u_bound
end Erdos371
