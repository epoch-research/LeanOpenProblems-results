import Submission.QuadraticConditionalCounts

/-! Weighted first moments of prime divisibility on a fixed conic head.
The summability assumption permits dominated convergence in the prime index. -/
namespace Erdos1206.QuadraticPrimeMoments
open Finset Filter QuadraticSquarefreeSieve QuadraticRootLattice
  QuadraticConditionalCounts BoxDensityLimits PrimeBoxCRT
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def primeScore (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑p∈n.primeFactors,w p

noncomputable def term (a b c : Fin 4 → ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (i : Fin 4) (N p : ℕ) : ℝ :=
  if p.Prime then w p*((counts a b c S i N p).card:ℝ)/(N:ℝ)^2 else 0

noncomputable def frequency (a b c : Fin 4 → ℕ) (S : Finset ℕ) (i : Fin 4) (p : ℕ) : ℝ :=
  if p.Prime ∧ p∉S then headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p else 0

lemma moment_identity (a b c : Fin 4 → ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (i : Fin 4) (hc : 0 < c i) (N : ℕ) :
    (∑x∈positiveBox N (Head a b c S),primeScore w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2 =
      ∑'p,term a b c S w i N p := by
  let T := positiveBox N (Head a b c S)
  let f (x : ℕ × ℕ) (p : ℕ) : ℝ := if p.Prime ∧ p∣quad (a i) (b i) (c i) x.1 x.2 then w p else 0
  have hxne (x : ℕ × ℕ) (hx : x∈T) : quad (a i) (b i) (c i) x.1 x.2 ≠ 0 := by
    have hxpos : 0 < x.1 := (mem_filter.mp hx).2.1
    apply Nat.ne_of_gt
    dsimp [quad]
    positivity
  have hs (x : ℕ × ℕ) (hx : x∈T) : Summable (f x) := by
    apply summable_of_ne_finset_zero (s := (quad (a i) (b i) (c i) x.1 x.2).primeFactors)
    intro p hp
    have hn : ¬(p.Prime ∧ p∣quad (a i) (b i) (c i) x.1 x.2) :=
      fun h => hp (Nat.mem_primeFactors.mpr ⟨h.1,h.2,hxne x hx⟩)
    exact if_neg hn
  have hscore (x : ℕ × ℕ) (hx : x∈T) : primeScore w (quad (a i) (b i) (c i) x.1 x.2)=∑'p,f x p := by
    rw [tsum_eq_sum (s := (quad (a i) (b i) (c i) x.1 x.2).primeFactors)]
    · apply sum_congr rfl
      intro p hp
      exact (if_pos ⟨(Nat.mem_primeFactors.mp hp).1,(Nat.mem_primeFactors.mp hp).2.1⟩).symm
    · intro p hp
      apply if_neg
      exact fun h => hp (Nat.mem_primeFactors.mpr ⟨h.1,h.2,hxne x hx⟩)
  have hinner (p : ℕ) : (∑x∈T,f x p)=
      if p.Prime then w p*(counts a b c S i N p).card else 0 := by
    by_cases hp : p.Prime
    · simp only [f,hp,true_and,if_true]
      rw [←sum_filter,sum_const,nsmul_eq_mul]
      have he : T.filter (fun x => p∣quad (a i) (b i) (c i) x.1 x.2)=counts a b c S i N p := by
        ext x
        simp only [T,positiveBox,counts,mem_filter]
        tauto
      rw [he,mul_comm]
    · simp [f,hp]
  have he : (∑x∈T,primeScore w (quad (a i) (b i) (c i) x.1 x.2))=
      ∑'p,if p.Prime then w p*(counts a b c S i N p).card else 0 := by
    calc
      _ = ∑x∈T,∑'p,f x p := sum_congr rfl hscore
      _ = ∑'p,∑x∈T,f x p := (Summable.tsum_finsetSum hs).symm
      _ = _ := tsum_congr hinner
  change (∑x∈T,primeScore w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2 = _
  rw [he,←tsum_div_const]
  apply tsum_congr
  intro p
  by_cases hp : p.Prime <;> simp [term,hp]

lemma term_bound (a b c : Fin 4 → ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) (i : Fin 4) (hQ : Anisotropic (c i) (b i) (a i)) (N p : ℕ) :
    ‖term a b c S w i N p‖ ≤ (48*mass (c i) (b i) (a i):ℝ)*
      (if p.Prime then w p/p else 0) := by
  by_cases hp : p.Prime
  · rw [term,if_pos hp,if_pos hp,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (mul_nonneg (hw p) (Nat.cast_nonneg _)) (sq_nonneg _))]
    have hh := mul_le_mul_of_nonneg_left (counts_bound a b c S i hQ N p hp) (hw p)
    convert hh using 1 <;> ring
  · simp [term,hp]

lemma term_tendsto (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (w : ℕ → ℝ) (i : Fin 4) (p : ℕ) :
    Tendsto (fun N => term a b c S w i N p) atTop (nhds (w p*frequency a b c S i p)) := by
  by_cases hp : p.Prime
  · by_cases hpS : p∈S
    · simp only [term,frequency,hp,hpS,not_true_eq_false,and_false,if_true,if_false,mul_zero,
        counts_empty a b c S hS i _ hpS,card_empty,Nat.cast_zero,zero_div]
      exact tendsto_const_nhds
    · have hh := (conditional_tendsto a b c S hS i hp hpS).const_mul (w p)
      simpa only [term,frequency,hp,hpS,not_false_eq_true,and_self,if_true,mul_div_assoc] using hh
  · simp only [term,frequency,hp,false_and,if_false,mul_zero]
    exact tendsto_const_nhds

/-- The normalized weighted prime-divisibility moment has the expected CRT
limit. Summability is used for domination, not as a heuristic interchange. -/
theorem moment_tendsto (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0))
    (i : Fin 4) (hc : 0 < c i) (hQ : Anisotropic (c i) (b i) (a i)) :
    Tendsto (fun N : ℕ => (∑x∈positiveBox N (Head a b c S),
      primeScore w (quad (a i) (b i) (c i) x.1 x.2))/(N:ℝ)^2)
      atTop (nhds (∑'p,w p*frequency a b c S i p)) := by
  simp_rw [moment_identity a b c S w i hc]
  exact tendsto_tsum_of_dominated_convergence (hs.mul_left (48*mass (c i) (b i) (a i):ℝ))
    (term_tendsto a b c S hS w i) (Filter.Eventually.of_forall (fun N p => term_bound a b c S w hw i hQ N p))

lemma frequency_bound (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hδ : 0 ≤ headDensity a b c S)
    (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) (i : Fin 4) (hQ : Anisotropic (c i) (b i) (a i)) (p : ℕ) :
    0 ≤ w p*frequency a b c S i p ∧
      w p*frequency a b c S i p ≤ headDensity a b c S*(48*mass (c i) (b i) (a i)+1)*
        (if p.Prime ∧ p∉S then w p/p else 0) := by
  by_cases hp : p.Prime ∧ p∉S
  · obtain ⟨hr0,hr⟩ := zeros_density_bound (a i) (b i) (c i) hQ hp.1
    simp only [frequency,if_pos hp]
    refine ⟨mul_nonneg (hw p) (mul_nonneg hδ hr0),?_⟩
    have hh := mul_le_mul_of_nonneg_left hr (mul_nonneg (hw p) hδ)
    convert hh using 1 <;> ring
  · simp [frequency,hp]

/-- The reciprocal first moment has arbitrarily small tails, formulated with
an indicator so that it can be compared directly to conditional frequencies. -/
lemma small_prime_weight_tail (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, (∑'p,if p.Prime ∧ H ≤ p then w p/p else 0) < ε := by
  have hpoint (p : ℕ) : Tendsto (fun H : ℕ => if p.Prime ∧ H ≤ p then w p/p else 0)
      atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop p] with H hH
    simp [not_le_of_gt hH]
  have hdom (H p : ℕ) : ‖if p.Prime ∧ H ≤ p then w p/p else 0‖ ≤
      if p.Prime then w p/p else 0 := by
    by_cases hp : p.Prime ∧ H ≤ p
    · simp only [if_pos hp,if_pos hp.1,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hw p) (Nat.cast_nonneg p)),le_refl]
    · rw [if_neg hp,norm_zero]
      split_ifs
      · exact div_nonneg (hw p) (Nat.cast_nonneg p)
      · exact le_rfl
  have ht := tendsto_tsum_of_dominated_convergence hs hpoint
    (Filter.Eventually.of_forall (fun H p => hdom H p))
  simp only [tsum_zero] at ht
  exact (ht.eventually (gt_mem_nhds hε)).exists

#print axioms moment_tendsto
#print axioms small_prime_weight_tail
end Erdos1206.QuadraticPrimeMoments
