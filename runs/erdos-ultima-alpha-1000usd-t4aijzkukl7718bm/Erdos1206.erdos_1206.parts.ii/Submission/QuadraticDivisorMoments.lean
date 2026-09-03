import Submission.QuadraticCompositeCounts
import Submission.WeightedDivisorCover

/-! First moments of divisor weights supported on primes and semiprimes.
This is a fixed-form obstruction, not a construction of a Sidon root set. -/
namespace Erdos1206.QuadraticDivisorMoments
open Finset Filter QuadraticSquarefreeSieve QuadraticRootLattice
  QuadraticConditionalCounts BoxDensityLimits PrimeBoxCRT QuadraticSemiprimeDivisibility
open QuadraticCompositeCounts
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def term (a b c : Fin 4 → ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (i : Fin 4) (N d : ℕ) : ℝ :=
  w d*((counts a b c S i N d).card:ℝ)/(N:ℝ)^2

noncomputable def frequency (a b c : Fin 4 → ℕ) (S : Finset ℕ) (i : Fin 4) (d : ℕ) : ℝ :=
  if LowComplexity d ∧ Avoids S d then
    headDensity a b c S*localDensity (QuadraticCompositeCounts.zeros (a i) (b i) (c i)) d else 0

lemma moment_identity (a b c : Fin 4 → ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (i : Fin 4) (hc : 0 < c i) (N : ℕ) :
    (∑x∈positiveBox N (Head a b c S),divisorWeight w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2 =
      ∑'d,term a b c S w i N d := by
  let T := positiveBox N (Head a b c S)
  let f (x : ℕ × ℕ) (d : ℕ) : ℝ := if d∣quad (a i) (b i) (c i) x.1 x.2 then w d else 0
  have hxne (x : ℕ × ℕ) (hx : x∈T) : quad (a i) (b i) (c i) x.1 x.2 ≠ 0 := by
    have hxpos : 0 < x.1 := (mem_filter.mp hx).2.1
    apply Nat.ne_of_gt
    dsimp [quad]
    positivity
  have hs (x : ℕ × ℕ) (hx : x∈T) : Summable (f x) := by
    apply summable_of_ne_finset_zero (s := (quad (a i) (b i) (c i) x.1 x.2).divisors)
    intro d hd
    exact if_neg (fun h => hd (Nat.mem_divisors.mpr ⟨h,hxne x hx⟩))
  have hscore (x : ℕ × ℕ) (hx : x∈T) : divisorWeight w (quad (a i) (b i) (c i) x.1 x.2)=∑'d,f x d := by
    rw [tsum_eq_sum (s := (quad (a i) (b i) (c i) x.1 x.2).divisors)]
    · apply sum_congr rfl
      intro d hd
      exact (if_pos (Nat.mem_divisors.mp hd).1).symm
    · intro d hd
      exact if_neg (fun h => hd (Nat.mem_divisors.mpr ⟨h,hxne x hx⟩))
  have hinner (d : ℕ) : (∑x∈T,f x d)=w d*(counts a b c S i N d).card := by
    simp only [f]
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have he : T.filter (fun x => d∣quad (a i) (b i) (c i) x.1 x.2)=counts a b c S i N d := by
      ext x
      simp only [T,positiveBox,counts,mem_filter]
      tauto
    rw [he,mul_comm]
  have he : (∑x∈T,divisorWeight w (quad (a i) (b i) (c i) x.1 x.2))=
      ∑'d,w d*(counts a b c S i N d).card := by
    calc
      _ = ∑x∈T,∑'d,f x d := sum_congr rfl hscore
      _ = ∑'d,∑x∈T,f x d := (Summable.tsum_finsetSum hs).symm
      _ = _ := tsum_congr hinner
  change (∑x∈T,divisorWeight w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2 = _
  rw [he,←tsum_div_const]
  rfl

lemma term_bound (a b c : Fin 4 → ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ d, 0 ≤ w d) (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (i : Fin 4) (hQ : Anisotropic (c i) (b i) (a i))
    (hD : (b i:ℤ)^2-4*(c i)*(a i)≠0) (N d : ℕ) :
    ‖term a b c S w i N d‖ ≤ (constant (c i) (b i) (a i):ℝ)*(w d/d) := by
  by_cases hd : LowComplexity d
  · rw [term,Real.norm_eq_abs,abs_of_nonneg
      (div_nonneg (mul_nonneg (hw d) (Nat.cast_nonneg _)) (sq_nonneg _))]
    have hh := mul_le_mul_of_nonneg_left (QuadraticCompositeCounts.counts_bound a b c S i hQ hD N d hd) (hw d)
    convert hh using 1 <;> ring
  · simp [term,hsupp d hd]

lemma term_tendsto (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (w : ℕ → ℝ) (hsupp : ∀ d, ¬LowComplexity d → w d=0) (i : Fin 4) (d : ℕ) :
    Tendsto (fun N => term a b c S w i N d) atTop (nhds (w d*frequency a b c S i d)) := by
  by_cases hd : LowComplexity d
  · by_cases havoid : Avoids S d
    · have hh := (QuadraticCompositeCounts.conditional_tendsto a b c S hS i
        (lt_trans Nat.zero_lt_one hd.one_lt) havoid).const_mul (w d)
      simpa only [term,frequency,hd,havoid,and_self,if_true,mul_div_assoc] using hh
    · simp only [term,frequency,hd,havoid,and_false,if_false,mul_zero,
        counts_empty_of_not_avoids a b c S hS i _ d havoid,card_empty,Nat.cast_zero,zero_div]
      exact tendsto_const_nhds
  · simp only [term,hsupp d hd,zero_mul,zero_div]
    exact tendsto_const_nhds

/-- Domination is uniform over primes and semiprimes. It has not been proved
uniformly over arbitrary composite divisors. -/
theorem moment_tendsto (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d) (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d))
    (i : Fin 4) (hc : 0 < c i) (hQ : Anisotropic (c i) (b i) (a i))
    (hD : (b i:ℤ)^2-4*(c i)*(a i)≠0) :
    Tendsto (fun N : ℕ => (∑x∈positiveBox N (Head a b c S),
      divisorWeight w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2)
      atTop (nhds (∑'d,w d*frequency a b c S i d)) := by
  simp_rw [moment_identity a b c S w i hc]
  exact tendsto_tsum_of_dominated_convergence (hs.mul_left (constant (c i) (b i) (a i):ℝ))
    (term_tendsto a b c S hS w hsupp i)
    (Filter.Eventually.of_forall (fun N d => term_bound a b c S w hw hsupp i hQ hD N d))

lemma frequency_bound (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hδ : 0 ≤ headDensity a b c S)
    (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d) (i : Fin 4) (hQ : Anisotropic (c i) (b i) (a i))
    (hD : (b i:ℤ)^2-4*(c i)*(a i)≠0) (d : ℕ) :
    0 ≤ w d*frequency a b c S i d ∧
      w d*frequency a b c S i d ≤ headDensity a b c S*(constant (c i) (b i) (a i):ℝ)*
        (if LowComplexity d ∧ Avoids S d then w d/d else 0) := by
  by_cases hd : LowComplexity d ∧ Avoids S d
  · obtain ⟨hr0,hr⟩ := QuadraticCompositeCounts.zeros_density_bound (a i) (b i) (c i) hQ hD hd.1
    simp only [frequency,if_pos hd]
    refine ⟨mul_nonneg (hw d) (mul_nonneg hδ hr0),?_⟩
    have hh := mul_le_mul_of_nonneg_left hr (mul_nonneg (hw d) hδ)
    convert hh using 1 <;> ring
  · simp [frequency,hd]

lemma small_weight_tail (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hs : Summable (fun d : ℕ => w d/d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, (∑'d,if H ≤ d then w d/d else 0) < ε := by
  have hpoint (d : ℕ) : Tendsto (fun H : ℕ => if H ≤ d then w d/d else 0)
      atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop d] with H hH
    simp [not_le_of_gt hH]
  have hdom (H d : ℕ) : ‖if H ≤ d then w d/d else 0‖ ≤ w d/d := by
    split_ifs
    · rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hw d) (Nat.cast_nonneg d))]
    · simpa only [norm_zero] using div_nonneg (hw d) (Nat.cast_nonneg d)
  have ht := tendsto_tsum_of_dominated_convergence hs hpoint
    (Filter.Eventually.of_forall (fun H d => hdom H d))
  simp only [tsum_zero] at ht
  exact (ht.eventually (gt_mem_nhds hε)).exists

lemma head_survivor_large {H d : ℕ} (hd : 1<d)
    (havoid : Avoids ((range H).filter Nat.Prime) d) : H≤d := by
  by_contra! hlt
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hd.ne'
  have hpdle : p≤d := Nat.le_of_dvd (by omega) hpd
  exact havoid p (mem_filter.mpr ⟨mem_range.mpr (lt_of_le_of_lt hpdle hlt),hp⟩) hpd

#print axioms moment_tendsto
#print axioms small_weight_tail
end Erdos1206.QuadraticDivisorMoments
