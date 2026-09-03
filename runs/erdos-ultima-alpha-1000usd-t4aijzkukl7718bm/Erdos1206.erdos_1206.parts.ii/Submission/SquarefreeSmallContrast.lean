import Submission.ConicContrastMoments
import Submission.SquarefreeHeadDensity

/-! Finite reciprocal-prime square energy forces arbitrarily small oriented
contrasts at strict squarefree cubic collisions. Individual scores need not
be small. This does not settle the positive-density Sidon conjecture. -/
namespace Erdos1206.SquarefreeSmallContrast
open Finset Filter SquarefreeConicFamily QuadraticPrimeMoments QuadraticScoreTailBounds
  ConicScoreSplit ConicContrastMoments QuadraticConditionalCounts QuadraticSquarefreeSieve
  BoxDensityLimits SquarefreeHeadDensity
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def primeHead (H : ℕ) : Finset ℕ := (range H).filter Nat.Prime

lemma primeHead_primes (H : ℕ) : ∀p∈primeHead H,p.Prime := fun _p hp => (mem_filter.mp hp).2

lemma head_density_pos (H : ℕ) : 0<headDensity a b c (primeHead H) :=
  QuadraticConditionalCounts.head_density_pos a b c (primeHead H) (primeHead_primes H)
    SquarefreeSummablePrimeObstruction.anisotropic_reversed SquarefreeSummablePrimeObstruction.local_units_nat

lemma momentLimit_le_tail (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) (H : ℕ) :
    momentLimit (primeHead H) w ≤ headDensity a b c (primeHead H)*constant*tailEnergy w H := by
  let S := primeHead H
  let δ := headDensity a b c S
  have hδ : 0≤δ := (head_density_pos H).le
  let r (p : ℕ) : ℝ := if p.Prime ∧ H≤p then w p^2/p else 0
  have hrs : Summable r := tail_summable (fun p => w p^2) (fun p => sq_nonneg _) hs H
  have he (p : ℕ) : (if p.Prime ∧ p∉S then w p^2/p else 0)=r p := by
    by_cases hp : p.Prime
    · simp only [S,primeHead,mem_filter,mem_range,hp,and_true,true_and,not_lt,r]
    · simp only [hp,false_and,if_false,r]
  have hbound (i : Fin 4) (p : ℕ) :
      0≤w p^2*frequency a b c S i p ∧
      w p^2*frequency a b c S i p≤δ*(48*QuadraticRootLattice.mass (c i) (b i) (a i)+1)*r p := by
    simpa only [he] using frequency_bound a b c S hδ (fun p => w p^2) (fun p => sq_nonneg _)
      i (SquarefreeSummablePrimeObstruction.anisotropic_reversed i) p
  have hlim (i : Fin 4) : (∑'p,w p^2*frequency a b c S i p)≤
      δ*(48*QuadraticRootLattice.mass (c i) (b i) (a i)+1)*(∑'p,r p) := by
    have hdom := hrs.mul_left (δ*(48*QuadraticRootLattice.mass (c i) (b i) (a i)+1))
    have hs' := Summable.of_nonneg_of_le (fun p => (hbound i p).1) (fun p => (hbound i p).2) hdom
    simpa only [tsum_mul_left] using hs'.tsum_le_tsum (fun p => (hbound i p).2) hdom
  calc
    _ ≤ ∑i,δ*(48*QuadraticRootLattice.mass (c i) (b i) (a i)+1)*(∑'p,r p) :=
      sum_le_sum (fun i hi => hlim i)
    _ = _ := by dsimp only [constant,tailEnergy,δ,S,r]; rw [←sum_mul,←mul_sum]

/-- The whole finite unit head may be prescribed in advance. The conclusion
controls only the inner-minus-outer contrast, not the four scores separately. -/
theorem exists_small_contrast (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    (H0 : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃x : ℕ × ℕ, 0<x.1 ∧ (∀i,Squarefree (F i x.1 x.2)) ∧
      (∀p,p.Prime → p≤H0 → ∀i,¬p∣F i x.1 x.2) ∧ |totalContrast w x|<ε := by
  obtain ⟨γ,hγ,hγhead⟩ := relative_density a b c
    (by intro i; fin_cases i <;> norm_num [a])
    (by intro i; fin_cases i <;> norm_num [c])
    SquarefreeSummablePrimeObstruction.anisotropic_reversed
    (by intro i; fin_cases i <;> norm_num [a,b,c])
    SquarefreeSummablePrimeObstruction.local_units_nat
  have htarget : 0<γ*ε^2/(16*constant) := by have := constant_pos; positivity
  have ht := tail_tendsto (fun p => w p^2) (fun p => sq_nonneg _) hs
  obtain ⟨H,hHtail,hHbig,hH0⟩ := ((ht.eventually (gt_mem_nhds htarget)).and
    ((eventually_ge_atTop 1000001).and (eventually_gt_atTop H0))).exists
  let S := primeHead H
  let δ := headDensity a b c S
  have hS : ∀p∈S,p.Prime := primeHead_primes H
  have hδ : 0<δ := head_density_pos H
  have hhead (p : ℕ) (hp : p.Prime) (hpH : p≤1000000) : p∈S :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩
  have hL : 8*momentLimit S w<γ*δ*ε^2 := by
    have hbound := momentLimit_le_tail w hs H
    have hsmall := mul_lt_mul_of_pos_left hHtail (show 0<δ*constant by exact mul_pos hδ constant_pos)
    have he : δ*constant*(γ*ε^2/(16*constant))=γ*δ*ε^2/16 := by
      have hc := constant_pos.ne'
      field_simp
    change δ*constant*tailEnergy w H<_ at hsmall
    rw [he] at hsmall
    change momentLimit S w≤δ*constant*tailEnergy w H at hbound
    have hpos : 0<γ*δ*ε^2 := mul_pos (mul_pos hγ hδ) (sq_pos_of_pos hε)
    nlinarith only [hbound,hsmall,hpos]
  by_contra! hnone
  have hno (x : ℕ × ℕ) (hx0 : 0<x.1) (hxsf : ∀i,Squarefree (F i x.1 x.2))
      (hxH : Head a b c S x) : ε≤|totalContrast w x| := by
    apply hnone x hx0 hxsf
    intro p hp hpH i
    exact (mem_head a b c S hS x).mp hxH p
      (mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩) i
  have hlow : ∀ᶠ N : ℕ in atTop, γ*δ*ε^2≤secondMoment S w N := by
    filter_upwards [hγhead S hS,eventually_gt_atTop 0] with N hN hNp
    have hNR : (0:ℝ)<N := by exact_mod_cast hNp
    have hh : ε^2*((squarefreeBox a b c S N).card:ℝ)≤
        ∑x∈positiveBox N (Head a b c S),totalContrast w x^2 := by
      calc
        _ = ∑_x∈squarefreeBox a b c S N,ε^2 := by simp [mul_comm]
        _ ≤ ∑x∈squarefreeBox a b c S N,totalContrast w x^2 := by
          apply sum_le_sum
          intro x hx
          obtain ⟨hxN,hx0,hxH,hxsf⟩ := (mem_squarefreeBox _ _ _ _ _ _).mp hx
          have h := hno x hx0 hxsf hxH
          have habs := sq_abs (totalContrast w x)
          nlinarith only [h,habs,hε]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (squarefreeBox_subset a b c S N)
          (fun x _ _ => sq_nonneg _)
    have hh' := (mul_le_mul_of_nonneg_left hN (sq_nonneg ε)).trans hh
    dsimp only [secondMoment]
    apply (le_div_iff₀ (sq_pos_of_pos hNR)).mpr
    convert hh' using 1; ring
  have hp : Tendsto (fun T : ℕ => T^8) atTop atTop := tendsto_pow_atTop (by decide)
  have hupper : ∀ᶠ T : ℕ in atTop, γ*δ*ε^2≤upper S w T := by
    filter_upwards [hp.eventually hlow,eventually_ge_atTop 1000000] with T hlow hT
    exact hlow.trans (secondMoment_le_upper S hS hhead w hs hT)
  have hh := ge_of_tendsto (upper_tendsto S hS w hs) hupper
  exact (not_le_of_gt hL) hh

#print axioms momentLimit_le_tail
#print axioms exists_small_contrast
end Erdos1206.SquarefreeSmallContrast
