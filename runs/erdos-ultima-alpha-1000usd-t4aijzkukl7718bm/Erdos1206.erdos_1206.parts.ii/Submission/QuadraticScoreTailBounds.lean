import Submission.QuadraticPrimeMoments

/-! Uniform first moments and elementary large-prime score bounds. -/
namespace Erdos1206.QuadraticScoreTailBounds
open Finset Filter QuadraticPrimeMoments QuadraticConditionalCounts QuadraticSquarefreeSieve
  QuadraticRootLattice BoxDensityLimits
open scoped Classical
set_option maxHeartbeats 2000000

lemma moment_upper (a b c : Fin 4 → ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀p,0≤w p) (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0))
    (i : Fin 4) (hc : 0 < c i) (hQ : Anisotropic (c i) (b i) (a i)) (N : ℕ) :
    (∑x∈positiveBox N (Head a b c S),primeScore w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2 ≤
      (48*mass (c i) (b i) (a i):ℝ)*(∑'p,if p.Prime then w p/p else 0) := by
  have ht0 (p : ℕ) : 0≤term a b c S w i N p := by
    dsimp [term]
    split_ifs
    · exact div_nonneg (mul_nonneg (hw p) (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl
  have hb (p : ℕ) : term a b c S w i N p ≤
      (48*mass (c i) (b i) (a i):ℝ)*(if p.Prime then w p/p else 0) := by
    exact (le_abs_self _).trans (term_bound a b c S w hw i hQ N p)
  have hsum := hs.mul_left (48*mass (c i) (b i) (a i):ℝ)
  have ht := Summable.of_nonneg_of_le ht0 hb hsum
  rw [moment_identity a b c S w i hc]
  simpa only [tsum_mul_left] using ht.tsum_le_tsum hb hsum

lemma tail_summable (w : ℕ → ℝ) (hw : ∀p,0≤w p)
    (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0)) (H : ℕ) :
    Summable (fun p : ℕ => if p.Prime ∧ H≤p then w p/p else 0) := by
  apply Summable.of_nonneg_of_le _ _ hs
  · intro p; split_ifs
    · exact div_nonneg (hw p) (Nat.cast_nonneg p)
    · exact le_rfl
  · intro p
    by_cases hp : p.Prime ∧ H≤p
    · simp only [if_pos hp,if_pos hp.1,le_refl]
    · rw [if_neg hp]
      split_ifs
      · exact div_nonneg (hw p) (Nat.cast_nonneg p)
      · exact le_rfl

lemma tail_tendsto (w : ℕ → ℝ) (hw : ∀p,0≤w p)
    (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0)) :
    Tendsto (fun H : ℕ => ∑'p,if p.Prime ∧ H≤p then w p/p else 0) atTop (nhds 0) := by
  have hpoint (p : ℕ) : Tendsto (fun H : ℕ => if p.Prime ∧ H≤p then w p/p else 0) atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop p] with H hH
    simp [not_le_of_gt hH]
  have hdom (H p : ℕ) : ‖if p.Prime ∧ H≤p then w p/p else 0‖ ≤
      if p.Prime then w p/p else 0 := by
    by_cases hp : p.Prime ∧ H≤p
    · simp only [if_pos hp,if_pos hp.1,Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hw p) (Nat.cast_nonneg p)),le_refl]
    · rw [if_neg hp,norm_zero]
      split_ifs
      · exact div_nonneg (hw p) (Nat.cast_nonneg p)
      · exact le_rfl
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs hpoint
    (Filter.Eventually.of_forall (fun H p => hdom H p))

noncomputable def largeFactors (T n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => T<p)
noncomputable def largeScore (w : ℕ → ℝ) (T n : ℕ) : ℝ := ∑p∈largeFactors T n,w p

lemma largeFactors_card_le {T n k : ℕ} (hT : 1<T) (hn : 0<n) (hsize : n≤T^k) :
    (largeFactors T n).card≤k := by
  have hsub : largeFactors T n⊆n.primeFactors := filter_subset _ _
  have hprod : (∏p∈largeFactors T n,p)∣n :=
    (prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hl : T^(largeFactors T n).card≤∏p∈largeFactors T n,p :=
    pow_card_le_prod _ id T (fun p hp => (mem_filter.mp hp).2.le)
  exact (Nat.pow_le_pow_iff_right hT).mp ((hl.trans (Nat.le_of_dvd hn hprod)).trans hsize)

lemma largeScore_sq_le (w : ℕ → ℝ) {T n k : ℕ}
    (hT : 1<T) (hn : 0<n) (hsize : n≤T^k) :
    largeScore w T n^2 ≤ (k:ℝ)*primeScore (fun p => if T<p then w p^2 else 0) n := by
  have hcs := sum_mul_sq_le_sq_mul_sq (largeFactors T n) (fun _ => (1:ℝ)) w
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  have hcard : ((largeFactors T n).card:ℝ)≤k := by exact_mod_cast largeFactors_card_le hT hn hsize
  have he : primeScore (fun p => if T<p then w p^2 else 0) n=∑p∈largeFactors T n,w p^2 := by
    simp only [primeScore,largeFactors,sum_filter]
  rw [he]
  exact hcs.trans (mul_le_mul_of_nonneg_right hcard (sum_nonneg (fun _ _ => sq_nonneg _)))

#print axioms moment_upper
#print axioms tail_tendsto
#print axioms largeScore_sq_le
end Erdos1206.QuadraticScoreTailBounds
